module ClosureConvert where

import IR
import Lang
import Control.Monad.State
import Control.Monad.Writer
import MonadFD4


-- runStateT -> put, get
-- writer -> tell

getFreshName :: MonadFD4 m => String -> m Name
getFreshName s = do
                    n <- getFreshCounter
                    return $ s ++ "_" ++ show n ++ "_"

getIrTy :: Ty -> IrTy
getIrTy (NatTy _) = IrInt
getIrTy (FunTy _ _) = IrClo

closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
-- -- closureConvert (V _ (Bound _)) no deberia pasar
closureConvert (V _ (Free nm)) = return $ IrVar nm
closureConvert (V _ (Global nm)) = return $ IrVar nm
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam info nm ty sc) = do
    fresh <- getFreshName "v"
    t <- open fresh sc
    t' <- closureConvert t
    vs <- freeVarsTy t
    fun_nm <- getFreshName "fun"
    e_nm <- getFreshName "env"
    x_nm <- getFreshName "x"
    let decl = IrFun fun_nm (getIrTy (getTy info)) [(e_nm, IrClo), (x_nm, getIrTy ty)] (lts' vs e_nm t' 1)
    in
        modify (\d -> {decls = decls ++ [d]}) decl -- esta mal, usar tell
    return $ MkClosure fun_nm (map (\v -> IrVar (fst v)) vs)
    where   lts' :: [(Name, Ty)] -> Ir -> Int -> Ir -> Ir 
            lts' v:vs c_nm t i  = IrLet (fst v) IrClo (IrAccess c_nm (snd v) i) (lts' vs c_nm t (i+1))
            lts' [] _ t _ = t
closureConvert (App (_, ty) t1 t2) = do
    nm <- getFreshName
    i1 <- closureConvert t1
    i2 <- closureConvert t2
    return $ IrLet nm IrClo i1 (IrCall (IrAccess (IrVar nm) IrFunTy 0) [IrVar nm, i2] (getIrTy ty))
closureConvert (Print _ s t) = do -- agregar let para forzar orden
     i <- closureConvert t
     return $  IrPrint s i
closureConvert (BinaryOp _ op t1 t2) = do -- agregar lets para forzar el orden
     i1 <- closureConvert t1
     i2 <- closureConvert t2
     return $ IrBinaryOp op i1 i2
-- --Fix info Name Ty Name Ty (Scope2 info var)
-- --IfZ info (Tm info var) (Tm info var) (Tm info var)
-- --Let info Name Ty (Tm info var)  (Scope info var)


-- runCC :: [Decl Term] -> [IrDecl]