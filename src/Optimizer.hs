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
import Subst
import MonadFD4

import TypeChecker ( tc )
import Lang (TTerm)
s
maxRuns :: Int
maxRuns = 10

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = optimize' maxRuns

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' n t = do
    t1 <- constantFolding t
    t2 <- constantPropagation t1
    optimize' (n-1) t2

constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding v@(V _ _) = return v
constantFolding c@(Const _ _) = return c
constantFolding (Lam i nm ty (Sc1 t)) = return (Lam i nm ty (Sc1 (constantFolding t)))
constantFolding (Fix i nm1 ty1 nm2 ty2 (Sc2 t)) = return (Fix i nm1 ty1 nm2 ty2 (Sc2 (constantFolding t)))
constantFolding (App i t1 t2) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return (App i t1' t2')
constantFolding (Print i s t) = return (Print i s (constantFolding t))
constantFolding (BinaryOp i op (Const i1 (CNat n1)) (Const i2 (CNat n2))) = do
  case op of
    Add -> return (BinaryOp i op (Const i1 (CNat (n1+n2))))
    Sub -> return (BinaryOp i op (Const i1 (CNat (n1-n2))))
constantFolding (BinaryOp i op t (Const i2 (CNat 0))) = return t
constantFolding (BinaryOp i op (Const i1 (CNat 0)) t) = do
  case op of
    Add -> return t
    Sub -> (Const i2 (CNat 0))
constantFolding (BinaryOp i op t1 t2) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return (BinaryOp i op t1' t2')
constantFolding (IfZ i (Const i1 (CNat n)) t f) = do
  case n of
    0 -> return $ constantFolding t
    _ -> return $ constantFolding f
constantFolding (IfZ i c t f) = do
  c' <- constantFolding c
  t' <- constantFolding t
  f' <- constantFolding f
  return (IfZ i c' t' f')
constantFolding (Let i nm ty t1 (Sc1 t2)) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return (Let i nm ty t1' (Sc1 t2'))
constantFolding t = failFD4 "constantFolding: no deberia haber llegado a aqui"

constantPropagation :: MonadFD4 m => TTerm -> m TTerm
constantPropagation v@(V _ _) = return v
constantPropagation c@(Const _ _) = return c
constantPropagation l@(Lam i nm ty (Sc1 t)) = return (Lam i nm ty (Sc1 (constantPropagation t)))
constantPropagation (Fix i nm1 ty1 nm2 ty2 (Sc2 t)) = return (Fix i nm1 ty1 nm2 ty2 (Sc2 (constantPropagation t)))
constantPropagation (App i t1 t2) = do
    t1' <- constantPropagation t1
    t2' <- constantPropagation t2
    return (App i t1' t2')
constantPropagation (Print i s t) = return (Print i s (constantPropagation t))
constantPropagation (BinaryOp i op t1 t2) = do
    t1' <- constantPropagation t1
    t2' <- constantPropagation t2
    return (BinaryOp i op t1' t2')
constantPropagation (IfZ i c t f) = do
  c' <- constantPropagation c
  t' <- constantPropagation t
  f' <- constantPropagation f
  return (IfZ i c' t' f')
constantPropagation (Let i nm ty c@(Const (CNat n)) (Sc1 t)) = do
    return (subst c (Sc1 (constantPropagation t)))
constantPropagation (Let i nm ty t1 (Sc1 t2)) = do
    t1' <- constantPropagation t1
    t2' <- constantPropagation t2
    return (Let i nm ty t1' (Sc1 t2'))
constantPropagation t = failFD4 "constantPropagation: no deberia haber llegado a aqui"
