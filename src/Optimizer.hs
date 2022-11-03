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

maxRuns :: Int
maxRuns = 10

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = optimize' maxRuns

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' n t = do
    t1 <- visit t constantFolding
    t2 <- visit t1 constantPropagation
    optimize' (n-1) t2

-- TODO: visit con scopes
visit :: MonadFD4 m => TTerm -> (TTerm -> TTerm) -> m TTerm
visit v@(V _ _) f = return v
visit c@(Const _ _) f = return c
visit (Lam i nm ty (Sc1 t)) f = do
  t' <- visit t f
  return $ f (Lam i nm ty (Sc1 t'))
visit (Fix i nm1 ty1 nm2 ty2 (Sc2 t)) f = do
  t' <- visit t f
  return $ f (Fix i nm1 ty1 nm2 ty2 (Sc2 t'))
visit (App i t1 t2) f = do
  t1' <- visit t1 f
  t2' <- visit t2 f
  return $ f (App i t1' t2')
visit (Print i s t) f = do
  t' <- visit t f
  return (Print i s t')
visit (BinaryOp i op t1 t2) f = do
  t1' <- visit t1 f
  t2' <- visit t2 f
  return $ f (BinaryOp i op t1' t2')
visit (IfZ i ct tt ft) f = do
  ct' <- visit ct f
  tt' <- visit tt f
  ft' <- visit ft f
  return $ f (IfZ i ct' tt' ft')
visit (Let i nm ty t1 (Sc1 t2)) f = do
  t1' <- visit t1 f
  t2' <- visit t2 f
  return $ f (Let i nm ty t1' (Sc1 t2'))
visit t f = failFD4 "visit: no deberia haber llegado a aqui"

constantFolding :: TTerm -> TTerm
constantFolding (BinaryOp i op (Const i1 (CNat n1)) (Const i2 (CNat n2))) =
  case op of
    Add -> Const i1 (CNat (n1+n2))
    Sub -> Const i1 (CNat (n1-n2)) -- no puede ser negativo, buscar funcion ya implementada
constantFolding (BinaryOp i op t (Const i2 (CNat 0))) = t
constantFolding (BinaryOp i op (Const i1 (CNat 0)) t) =
  case op of
    Add -> t
    Sub -> (Const i1 (CNat 0))
constantFolding (IfZ i (Const i1 (CNat n)) t f) =
  case n of
    0 -> constantFolding t
    _ -> constantFolding f
constantFolding t = t

-- TODO: reemplazo de una variable por otra
constantPropagation :: TTerm -> TTerm
constantPropagation (Let i1 nm ty c@(Const i2 (CNat n)) (Sc1 t)) = subst c (Sc1 t)
constantPropagation t = t
