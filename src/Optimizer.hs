{-|
Module      : Optimizer
Description : Optimiza el código previo a su evaluación o compilación.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo incluye constant folding y propagation.
-}
module Optimizer
  (optimize)
 where

import Lang
import Subst ( close, close2, open, open2, subst )
import Eval ( semOp )
import MonadFD4
    ( failFD4, MonadFD4, setOptimized, getOptimized, getFreshVar )

maxRuns :: Int
maxRuns = 10

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = optimize' maxRuns

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' n t = do
    setOptimized 0
    t1 <- visit t constantFolding
    t2 <- visit t1 constantPropagation
    opt <- getOptimized
    case opt of
      0 -> optimize' 0 t
      _ -> optimize' (n-1) t2

visit :: MonadFD4 m => TTerm -> (TTerm -> m TTerm) -> m TTerm
visit v@(V _ _) f = return v
visit c@(Const _ _) f = return c
visit (Lam i nm ty sc) f = do
  fresh <- getFreshVar
  t' <- visit (open fresh sc) f
  f (Lam i nm ty (close fresh t'))
visit (Fix i nm1 ty1 nm2 ty2 sc) f = do
  fresh1 <- getFreshVar
  fresh2 <- getFreshVar
  t' <- visit (open2 fresh1 fresh2 sc) f
  f (Fix i nm1 ty1 nm2 ty2 (close2 fresh1 fresh2 t'))
visit (App i t1 t2) f = do
  t1' <- visit t1 f
  t2' <- visit t2 f
  f (App i t1' t2')
visit (Print i s t) f = do
  t' <- visit t f
  return (Print i s t')
visit (BinaryOp i op t1 t2) f = do
  t1' <- visit t1 f
  t2' <- visit t2 f
  f (BinaryOp i op t1' t2')
visit (IfZ i ct tt ft) f = do
  ct' <- visit ct f
  tt' <- visit tt f
  ft' <- visit ft f
  f (IfZ i ct' tt' ft')
visit (Let i nm ty t sc) f = do
  t' <- visit t f
  fresh <- getFreshVar
  t'' <- visit (open fresh sc) f
  f (Let i nm ty t' (close fresh t''))
visit t f = failFD4 "visit: no deberia haber llegado a aqui"

constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding (BinaryOp i op (Const i1 (CNat n1)) (Const i2 (CNat n2))) = do
  setOptimized 1
  return $ Const i1 (CNat (semOp op n1 n2))
constantFolding (BinaryOp i op t (Const i2 (CNat 0))) = do
  setOptimized 1
  return t
constantFolding (BinaryOp i op (Const i1 (CNat 0)) t) = do
  setOptimized 1
  return (case op of
    Add -> t
    Sub -> Const i1 (CNat 0))
constantFolding (IfZ i (Const i1 (CNat n)) t f) = do
  setOptimized 1
  case n of
    0 -> constantFolding t
    _ -> constantFolding f
constantFolding t = return t

constantPropagation :: MonadFD4 m => TTerm -> m TTerm
constantPropagation (Let i nm ty c@(Const _ _) (Sc1 t)) = do
  setOptimized 1
  return $ subst c (Sc1 t)
constantPropagation (Let i nm ty v@(V _ _) (Sc1 t)) = do
  setOptimized 1
  return $ subst v (Sc1 t)
constantPropagation t = return t
