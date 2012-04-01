{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Funsat.RPOCircuit.Internal where

import Control.Monad.Reader
import Funsat.ECircuit

newtype Flip t a b = Flip {unFlip::t b a}
type EvalM = Flip EvalF

fromLeft :: Either l r -> l
fromLeft (Left l) = l
fromLeft _ = error "fromLeft on a Right"
fromRight :: Either l r -> r
fromRight (Right r) = r
fromRight _ = error "fromRight on a Left"

runEvalM :: BIEnv e -> EvalM e a -> a
runEvalM env = flip unEval env . unFlip

evalB :: Eval v -> EvalM v Bool
evalN :: Eval v -> EvalM v Int
evalB c = liftM (fromRight :: Either Int Bool -> Bool) (eval c)
evalN c = liftM (fromLeft  :: Either Int Bool -> Int)  (eval c)
eval  c = do {env <- ask; return (runEval env c)}

instance Functor (EvalM v) where fmap f (Flip (Eval m)) = Flip $ Eval $ \env -> f(m env)
instance Monad (EvalM v) where
  return x = Flip $ Eval $ \_ -> x
  m >>= f  = Flip $ Eval $ \env -> runEvalM env $ f $ runEvalM env m

instance MonadReader (BIEnv v) (EvalM v) where
  ask       = Flip $ Eval $ \env -> env
  local f m = Flip $ Eval $ \env -> runEvalM (f env) m
