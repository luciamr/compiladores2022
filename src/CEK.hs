{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : CEK
Description : Implementación de la máquina CEK (control statement, environment y continuation)

Declaración de tipos e implementación de las funciones de búsqueda y reducción.
-}

module CEK where

import MonadFD4 ( MonadFD4, failFD4, lookupDecl, printFD4 )
import Lang
import Common ( Pos(..) )
import Eval ( semOp )
import PPrint ( ppName )
import Subst ( substN )

import Data.List ( intercalate )

data Val = N Int | Cls Closure
type Env = [Val]
data Closure = ClsLam (Pos,Ty) Env Name Ty TTerm | ClsFix (Pos,Ty) Env Name Ty Name Ty TTerm
data Frame =
    FrmApp Env TTerm -- ρ · □ t
    | FrmCls Closure -- clos □
    | FrmIfZ Env TTerm TTerm -- ρ · ifz □ then t else e
    | FrmBOpT Env BinaryOp TTerm -- ρ · □ ⊕ t
    | FrmBOpV BinaryOp Val -- v ⊕ □
    | FrmPrint String -- print str □
    | FrmLet Env Name TTerm -- ρ · let x = □ in t
type Kont = [Frame]

runCEK :: MonadFD4 m => TTerm -> m TTerm
runCEK tt = do
    v <- search tt [] []
    return (val2TTerm v)

val2string :: Val -> String
val2string (N n) = "N " ++ show n
val2string (Cls c) = "(Cls " ++ closure2string c ++ ")"

closure2string :: Closure -> String
closure2string (ClsLam _ e nm ty tt) = intercalate "|" ["ClsLam", env2string e, nm, show ty, show tt]
closure2string (ClsFix _ e nm1 ty1 nm2 ty2 tt) = intercalate "|" ["ClsFix", env2string e, nm1, show ty1, nm2, show ty2, show tt]

env2string :: Env -> String
env2string e = intercalate ";" (map val2string e)

frame2string :: Frame -> String
frame2string (FrmApp e tt) = intercalate "|" ["FrmApp", env2string e, show tt]
frame2string (FrmCls c) = intercalate "|" ["FrmCls", closure2string c]
frame2string (FrmIfZ e tt1 tt2) = intercalate "|" ["FrmIfz", env2string e, show tt1, show tt2]
frame2string (FrmBOpT e bo tt) = intercalate "|" ["FrmBOpT", env2string e, show tt]
frame2string (FrmBOpV bo v) = intercalate "|" ["FrmBOpV", val2string v]
frame2string (FrmPrint s) = intercalate "|" ["FrmPrint", s]
frame2string (FrmLet e nm tt) = intercalate "|" ["FrmLet", env2string e, nm, show tt]

kont2string :: Kont -> String
kont2string k = intercalate ";" (map frame2string k)

search' :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search' tt e k = do
  --  printFD4 "-- search"
  --  printFD4 $ "TTerm: " ++ show tt
  --  printFD4 $ "Env: " ++ env2string e
  --  printFD4 $ "Kont: " ++ kont2string k
    search tt e k

search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print _ s t) e k = search' t e (FrmPrint s:k)
search (BinaryOp _ o t u) e k = search' t e (FrmBOpT e o u:k)
search (IfZ _ tc tt te) e k = search' tc e (FrmIfZ e tt te:k)
search (App _ t u) e k = search' t e (FrmApp e u:k)
search (V _ (Bound i)) e k = destroy' (e!!i) k
search (V _ (Free n)) _ _ = failFD4 $ "Error de ejecución: variable libre detectada: " ++ ppName n
search (V _ (Global n)) e k = do
    mt <- lookupDecl n
    case mt of
        Just t -> search' t e k
        Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n -- idem Eval
search (Const _ (CNat n)) e k = destroy' (N n) k
search (Lam i nm ty (Sc1 t)) e k = destroy' (Cls (ClsLam i e nm ty t)) k
search (Fix i nm1 ty1 nm2 ty2 (Sc2 t)) e k = destroy' (Cls (ClsFix i e nm1 ty1 nm2 ty2 t)) k
search (Let _ nm ty u (Sc1 t)) e k = search' u e (FrmLet e nm t:k)

destroy' :: MonadFD4 m => Val -> Kont -> m Val
destroy' v k = do
--    printFD4 "-- destroy"
--    printFD4 $ "Val: " ++ val2string v
--    printFD4 $ "Kont: " ++ kont2string k
    destroy v k

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy (N i) ((FrmPrint s):k) = do printFD4 (s++show i)
                                    destroy (N i) k
destroy (Cls _) ((FrmPrint s):k) = failFD4 "Error de tipo en runtime! : Print"
destroy (N i) ((FrmBOpT e o t):k) = search' t e (FrmBOpV o (N i):k)
destroy (N i2) ((FrmBOpV o (N i1)):k) =  destroy' (N (semOp o i1 i2)) k
destroy (N _) ((FrmBOpV o (Cls _)):k) =  failFD4 "Error de tipo en runtime! : BinaryOp" -- TODO: pprint del operador
destroy v ((FrmCls (ClsFix i e nm1 ty1 nm2 ty2 t)):k) = search t (Cls (ClsFix i e nm1 ty1 nm2 ty2 t):v:e) k
destroy (N 0) ((FrmIfZ e tt te):k) = search' tt e k
destroy (N _) ((FrmIfZ e tt te):k) = search' te e k
destroy (Cls c) ((FrmApp e t):k) = search' t e (FrmCls c:k)
destroy v ((FrmCls (ClsLam _ e nm ty t)):k) = search' t (v:e) k
destroy v ((FrmLet e nm t):k) = search' t (v:e) k

val2TTerm :: Val -> TTerm
val2TTerm (N i) = Const (NoPos,NatTy) (CNat i)
val2TTerm (Cls (ClsLam i e nm ty t)) = substN (map val2TTerm e) (Lam i nm ty (Sc1 t))
val2TTerm (Cls (ClsFix i e nm1 ty1 nm2 ty2 t)) = substN (map val2TTerm e) (Fix i nm1 ty1 nm2 ty2 (Sc2 t))
