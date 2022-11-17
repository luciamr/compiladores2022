module ClosureConvert where

import IR
import Lang
import Control.Monad.State
import Control.Monad.Writer
import MonadFD4

getFreshName :: MonadFD4 m => m Name
getFreshName = do
                n <- getFreshCounter
                return $ "`n_" ++ show n ++ "_"

getIrTy :: Ty -> IrTy
getIrTy (NatTy _) = IrInt
getIrTy (FunTy _ _) = IrClo

closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
-- -- closureConvert (V _ (Bound _)) no deberia pasar
closureConvert (V _ (Free nm)) = return $ IrVar nm
closureConvert (V _ (Global nm)) = return $ IrVar nm
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam info nm ty sc) = do
    nm <- getFreshName
    fresh <- getFreshName
    t <- open fresh sc
    vs <- freeVarsTy t

    return $ MkClosure nm [Ir]
closureConvert (App (_, ty) t1 t2) = do
    nm <- getFreshName
    i1 <- closureConvert t1
    i2 <- closureConvert t2
    return $ IrLet nm IrClo i1 (IrCall (IrAccess (IrVar nm) IrClo 0) [IrVar nm, i2] (getIrTy ty)) -- tipo para IrAccess?
-- print: necesito let?
-- closureConvert (Print _ s t) = do
--     i <- closureConvert t
--     return $  IrPrint s i
-- binaryop: necesito let?
-- closureConvert (BinaryOp _ op t1 t2) = do
--     i1 <- closureConvert t1
--     i2 <- closureConvert t2
--     return $ IrBinaryOp op i1 i2
-- --Fix info Name Ty Name Ty (Scope2 info var)
-- --IfZ info (Tm info var) (Tm info var) (Tm info var)
-- --Let info Name Ty (Tm info var)  (Scope info var)


-- runCC :: [Decl Term] -> [IrDecl]