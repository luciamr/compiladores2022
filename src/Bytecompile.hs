{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List ( intercalate, elemIndex )
import Data.Char
import TypeChecker ( tc )
import Lang (TTerm)

type Opcode = Int
type Bytecode = [Int]

data Val = I Int | Fun Env Bytecode | RA Env Bytecode
type Env = [Val]
type Stack = Env

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern JUMP     = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern CJUMP    = 15
pattern TAILCALL = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i): showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bccT :: MonadFD4 m => TTerm -> m Bytecode
bccT (App _ f t) = do
  f' <- bccT f
  t' <- bccT t
  return $ f' ++ t' ++ [TAILCALL]
bccT (IfZ _ c t f) = do
  c' <- bcc c
  t' <- bccT t
  f' <- bccT f
  return $ c' ++ [CJUMP, length t'] ++ t' ++ [JUMP, length f'] ++ f'
bccT t = do
  t' <- bcc t
  return $ t' ++ [RETURN]

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (Const _ (CNat n)) = return [CONST, n]
bcc (V _ (Bound i)) = return [ACCESS, i]
bcc (BinaryOp _ op t1 t2) = do
  t1' <- bcc t1
  t2' <- bcc t2
  case op of
    Add -> return $ t1' ++ t2' ++ [ADD]
    Sub -> return $ t1' ++ t2' ++ [SUB]
bcc (App _ f t) = do
  f' <- bcc f
  t' <- bcc t
  return $ f' ++ t' ++ [CALL]
bcc (Lam _ _ _ (Sc1 t)) = do
  t' <- bccT t
  return $ [FUNCTION, length t'] ++ t'
bcc (Fix _ nm1 _ nm2 _ (Sc2 t)) = do
  t' <- bcc t
  return $ [FUNCTION, length t'] ++ t' ++ [RETURN, FIX]
bcc (IfZ _ c t f) = do
  c' <- bcc c
  t' <- bcc t
  f' <- bcc f
  return $ c' ++ [CJUMP, length t'] ++ t' ++ [JUMP, length f'] ++ f'
bcc (Print _ s t) = do
  t' <- bcc t
  let s' = string2bc s in
    return $ [PRINT] ++ s' ++ [NULL] ++ t' ++ [PRINTN]
bcc (Let _ nm _ t1  (Sc1 t2)) = do
  t1' <- bcc t1
  t2' <- bcc t2
  return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]
bcc t = failFD4 "bcc: no deberia haber llegado a aqui"

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = let m' = global2free m in do
  bc <- bccT (processNestedLets m')
  return $ bc ++ [STOP]

-- transformar variables globales en free
global2free :: Module -> Module -- [Decl TTerm]
global2free = map (\ (Decl p n t) -> Decl p n (global2free' t))

global2free' :: TTerm -> TTerm
global2free' (V i (Global n)) = V i (Free n)
global2free' (Lam i nm ty (Sc1 t)) = Lam i nm ty (Sc1 (global2free' t))
global2free' (App i t1 t2) = App i (global2free' t1) (global2free' t2)
global2free' (Print i s t) = Print i s (global2free' t)
global2free' (BinaryOp i bo t1 t2) = BinaryOp i bo (global2free' t1) (global2free' t2)
global2free' (Fix i nm1 ty1 nm2 ty2 (Sc2 t)) = Fix i nm1 ty1 nm2 ty2 (Sc2 (global2free' t))
global2free' (IfZ i tc tt te) = IfZ i (global2free' tc) (global2free' tt) (global2free' te)
global2free' (Let i nm ty u (Sc1 t)) = Let i nm ty (global2free' u) (Sc1 (global2free' t))
global2free' t = t -- incluye V Bound, V Free and Const

-- procesar let anidados
processNestedLets :: Module -> TTerm
processNestedLets [m] = declBody m
processNestedLets (m:ms) = let
  p = declPos m
  ty = NatTy -- TODO: corregir el tipo, ver Decl
  nm = declName m
  b = declBody m
  in
    Let (p, ty) nm ty b (close nm (processNestedLets ms))

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runBC'' bc [] []

val2string :: Val -> String
val2string (I n) = "I " ++ (show n)
val2string (Fun e bc) = "(Fun " ++ intercalate ";" (map val2string e) ++ showBC bc ++ ")"
val2string (RA e bc) = "(RA " ++ intercalate ";" (map val2string e) ++ showBC bc  ++ ")"

runBC'' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC'' bc e s = do
  -- printFD4 $ "BC: " ++ showBC bc
  -- printFD4 $ "Env: " ++ intercalate ";" (map val2string e) -- no usar con fix
  -- printFD4 $ "Stack: " ++ intercalate ";" (map val2string s) -- no usar con fix
  -- printFD4 "----------"
  runBC' bc e s

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (CONST:n:bc) e s = runBC'' bc e (I n:s)
runBC' (ACCESS:i:bc) e s = runBC'' bc e ((e!!i):s)
runBC' (ADD:bc) e ((I n2):(I n1):s) = runBC'' bc e (I (n1+n2):s)
runBC' (SUB:bc) e ((I n2):(I n1):s) = let r = max 0 (n1-n2) in runBC'' bc e (I r:s)
runBC' (CALL:bc) e (v:(Fun ef bcf):s) = runBC'' bcf (v:ef) (RA e bc:s)
runBC' (FUNCTION:l:bc) e s = runBC'' (drop (l+1) bc) e (Fun e (take (l+1) bc):s)
runBC' (RETURN:_) _ (v:(RA e bc):s) = runBC'' bc e (v:s)
runBC' (FIX:bc) e ((Fun ef bcf):s) =
  let efix = Fun efix bcf:ef in
    runBC'' bc e (Fun efix bcf:s)
runBC' (PRINT:bc) e s = do
  let mi = elemIndex NULL bc in
    case mi of
      Nothing -> failFD4 "falta NULL despues de PRINT"
      Just i -> do
        printFD4 (bc2string (take i bc))
        runBC'' (drop (i+1) bc) e s
runBC' (PRINTN:bc) e (I n:s) = do
    printFD4 $ show n
    runBC'' bc e (I n:s)
runBC' (SHIFT:bc) e (v:s) = runBC'' bc (v:e) s
runBC' (DROP:bc) (v:e) s = runBC'' bc e s
runBC' (CJUMP:lt:bc) e (I n:s) =
  case n of
    0 -> runBC'' bc e s
    _ -> runBC'' (drop (lt+2) bc) e s -- +2 para consumir JUMP
runBC' (JUMP:lf:bc) e s = runBC'' (drop lf bc) e s
runBC' (STOP:_) _ _ = return ()
runBC' [] _ _  = failFD4  "runBC': no deberia haber llegado a aqui"

