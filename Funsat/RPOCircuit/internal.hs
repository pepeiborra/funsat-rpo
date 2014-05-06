{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Funsat.RPOCircuit.Internal where

import Control.Applicative
import Control.Monad.Reader
import qualified Data.Term as Family
import Funsat.ECircuit

newtype WrapWithTerm term f a = WrapWithTerm { unwrapWithTerm :: f a}
                              deriving (Applicative, Functor, Monad)
deriving instance MonadReader (BIEnv v) f => MonadReader (BIEnv v) (WrapWithTerm term f)

newtype WrapEval term v = WrapEval_ {unWrapEval_ :: WrapWithTerm term Eval v}
pattern WrapEval a = WrapEval_ (WrapWithTerm a)

type instance Family.TermF (WrapEval term) = Family.TermF term
type instance Family.Var   (WrapEval term) = Family.Var   term
type instance Family.Id    (WrapEval term) = Family.Id    term

unwrapEval :: WrapEval term v -> Eval v
unwrapEval = unwrapWithTerm . unWrapEval_
wrap1 :: ( Eval a -> Eval b) -> WrapEval term a -> WrapEval term b
wrap1 f = WrapEval . f . unwrapEval
wrap2 f x y = WrapEval $ f (unwrapEval x) (unwrapEval y)
wrap3 f x y z = WrapEval $ f (unwrapEval x) (unwrapEval y) (unwrapEval z)
wrapL f = WrapEval . f . map unwrapEval
--pattern WrapEval a = WrapEval_

newtype Flip t a b = Flip {unFlip::t b a}

newtype EvalM v a = EvalTerm {unEvalFlip :: Flip EvalF v a}
pattern EvalM a = EvalTerm(Flip(Eval a))
runEvalM env = flip unEval env . unFlip . unEvalFlip

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromLeft _ = error "fromLeft on a Right"
fromRight :: Either l r -> r
fromRight (Right r) = r
fromRight _ = error "fromRight on a Left"

unEvalM :: EvalM a b -> EvalF b a
unEvalM = unFlip . unEvalFlip

evalB :: Eval v -> EvalM v Bool
evalN :: Eval v -> EvalM v Int
evalB c = liftM (fromRight :: Either Int Bool -> Bool) (eval c)
evalN c = liftM (fromLeft  :: Either Int Bool -> Int)  (eval c)
eval  c = do {env <- ask; return (runEval env c)}

instance Functor (EvalM v) where fmap f (EvalM m) = EvalM $ \env -> f(m env) ; fmap _ _ = error "Pleasing the exhaustive pattern matching checker"
                                 
instance Applicative (EvalM v) where
  pure x = return x
  f <*> x = EvalM $ \env -> runEvalM env f $ runEvalM env x

instance Monad (EvalM v) where
  return x = EvalM $ \_ -> x
  m >>= f  = EvalM $ \env -> runEvalM env $ f $ runEvalM env m

instance MonadReader (BIEnv v) (EvalM v) where
  ask       = EvalM $ \env -> env
  local f m = EvalM $ \env -> runEvalM (f env) m
