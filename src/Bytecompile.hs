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
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = "ACCESS" : show i : showOps xs
showOps (FUNCTION:i:xs)  = "FUNCTION" : show i : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = "JUMP" : show i: showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps xs
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (Const _ (CNat n)) = return [CONST, n]
bcc (V _ (Bound i)) = return [ACCESS, i]
bcc (BinaryOp _ op t1 t2) = do
  t1' <- bcc t1
  t2' <- bcc t2
  case op of
    Add -> return (t1' ++ t2' ++ [ADD])
    Sub -> return (t1' ++ t2' ++ [SUB])
bcc (App _ f t) = do
  f' <- bcc f
  t' <- bcc t
  return (f' ++ t' ++ [CALL])
bcc (Lam _ _ _ (Sc1 t)) = do
  t' <- bcc t
  return ([FUNCTION, length t'] ++ t' ++ [RETURN])
bcc (Fix _ nm1 _ nm2 _ (Sc2 t)) = do
  t' <- bcc t
  return ([FUNCTION, length t'] ++ t' ++ [RETURN, FIX])
  -- return ([FIXPOINT, length t'] ++ t' ++ [RETURN])
bcc (IfZ _ c t f) = do
  c' <- bcc c
  t' <- bcc t
  f' <- bcc f
  failFD4 "implementar ifz!"
bcc (Print _ s t) = do
  t' <- bcc t
  let s' = string2bc s in
    return ([PRINT] ++ s' ++ [NULL] ++ t' ++ [PRINTN])
bcc (Let _ nm _ t1  (Sc1 t2)) = do
  t1' <- bcc t1
  t2' <- bcc t2
  return (t1' ++ [SHIFT] ++ t2' ++ [DROP])
bcc t = failFD4 "implementame!"

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = failFD4 "implementame!"

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
runBC bc = runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (CONST:n:bc) e s = runBC' bc e (I n:s)
runBC' (ACCESS:i:bc) e s = runBC' bc e ((e!!i):s)
runBC' (ADD:bc) e ((I n1):(I n2):s) = runBC' bc e (I (n1+n2):s)
runBC' (SUB:bc) e ((I n1):(I n2):s) = runBC' bc e (I (n1-n2):s)
runBC' (CALL:bc) e (v:(Fun ef bcf):s) = runBC' bcf (v:ef) (RA e bc:s)
-- runBC' (FUNCTION:l:bc) e s =
--   let  rf = runBC' (take l bc) e s
--   in
--     runBC' (drop l bc) e (Fun e rf:s)
-- runBC' (FIX:bc)
-- runBC' (RETURN:_) _ (v:(RA e bc):s) = runBC' bc e (v:s)
-- runBC' (FIXPOINT:l:bc) e s =
--   let cf = runBC' (take l bc) e s
--       efix = (Fun efix cf):e
--   in
--     runBC' (drop l bc) e ((Fun efix cf):s)
-- runBC' (PRINT:bc) e s = do
--     mi <- elemIndex NULL bc
--     case mi of
--       Nothing -> failFD4 "falta NULL despues de PRINT"
      -- Just i -> do
      --   printFD4 (bc2string (take i bc))
      --   runBC' (drop (i+1) bc) e s
runBC' (PRINTN:bc) e (I n:s) = do
    printFD4 $ show n
    runBC' bc e (I n:s)
runBC' (SHIFT:bc) e (v:s) = runBC' bc (v:e) s
runBC' (DROP:bc) (v:e) s = runBC' bc e s
runBC' [] _ s  = failFD4  "definir final"

