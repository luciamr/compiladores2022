{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert 
    (runCC)
where

import IR
import Lang
import Subst ( open, open2 )
import Control.Monad.State
import Control.Monad.Writer

type MonadCC = StateT Int (Writer [IrDecl])

getFreshName :: String -> MonadCC Name
getFreshName s = do
    n <- get
    put $ n+1
    return $ s ++ "_" ++ show n ++ "_"

getIrTy :: Ty -> IrTy
getIrTy NatTy = IrInt
getIrTy (FunTy _ _) = IrClo

buildIrLets :: [(Name, Ty)] -> Name -> Ir -> Int -> Ir
buildIrLets (v:vs) c_nm t i  = IrLet (fst v) IrClo (IrAccess (IrVar c_nm) (getIrTy (snd v)) i) (buildIrLets vs c_nm t (i+1))
buildIrLets [] _ t _ = t

closureConvert :: TTerm -> MonadCC Ir
-- -- closureConvert (V _ (Bound _)) no deberia pasar
closureConvert (V _ (Free nm)) = return $ IrVar nm
closureConvert (V _ (Global nm)) = return $ IrVar nm
closureConvert (Const _ c) = return $ IrConst c
closureConvert l@(Lam info nm ty sc) = do
    fresh <- getFreshName "v"
    t' <-  closureConvert (open fresh sc)
    let vs = freeVarsTy l
    fun_nm <- getFreshName "lam"
    e_nm <- getFreshName "env"
    tell [IrFun fun_nm (getIrTy (getTy l)) [(e_nm, IrClo), (fresh, getIrTy ty)] (buildIrLets vs e_nm t' 1)]
    return $ MkClosure fun_nm (map (IrVar . fst) vs)
closureConvert (App (_, ty) t1 t2) = do
    nm <- getFreshName "app"
    i1 <- closureConvert t1
    i2 <- closureConvert t2
    return $ IrLet nm IrClo i1 (IrCall (IrAccess (IrVar nm) IrFunTy 0) [IrVar nm, i2] (getIrTy ty))
closureConvert (Print _ s t) = do
     p_nm <- getFreshName "print"
     i <- closureConvert t
     return $ IrLet p_nm IrInt i (IrPrint s (IrVar p_nm))
closureConvert (BinaryOp _ op t1 t2) = do
     bop_nm_1 <- getFreshName "bop1"
     i1 <- closureConvert t1
     bop_nm_2 <- getFreshName "bop2"
     i2 <- closureConvert t2
     return $ IrLet bop_nm_1 (getIrTy (getTy t1)) i1 (IrLet bop_nm_2 (getIrTy (getTy t2)) i2 (IrBinaryOp op (IrVar bop_nm_1) (IrVar bop_nm_2)))
closureConvert f@(Fix _ nm1 ty1 nm2 ty2 sc) = do
    fresh1 <- getFreshName "v"
    fresh2 <- getFreshName "v"
    t' <-  closureConvert (open2 fresh1 fresh2 sc)
    let vs = freeVarsTy f
    fix_nm <- getFreshName "fix"
    c_nm <- getFreshName "clos"
    tell [IrFun fix_nm (getIrTy ty1) [(c_nm, IrClo), (fresh2, getIrTy ty2)] (IrLet fresh1 (getIrTy ty1) (IrVar c_nm) (buildIrLets vs c_nm t' 1))]
    return $ MkClosure fix_nm (map (IrVar . fst) vs)
closureConvert (IfZ _ ct tt ft) = do
    ct' <- closureConvert ct
    tt' <- closureConvert tt
    ft' <- closureConvert ft
    return $ IrIfZ ct' tt' ft'
closureConvert l@(Let _ nm ty t sc) = do
    t' <- closureConvert t
    let_nm <- getFreshName "let"
    s' <- closureConvert (open let_nm sc)
    return $ IrLet let_nm (getIrTy (getTy l)) t' s'

runCC' :: Decl TTerm -> MonadCC IrDecl
runCC' (Decl p nm t) = do
    t' <- closureConvert t
    return $ IrVal nm (getIrTy (getTy t)) t'

runCC :: [Decl TTerm] -> IrDecls 
runCC ds = do
    let ((decls1, f_stt), decls2) = runWriter (runStateT (mapM runCC' ds) 0) in
        IrDecls (decls1 ++ decls2)
