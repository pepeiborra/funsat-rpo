{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Funsat.TermCircuit.Symbols where

import Control.Arrow(second)
import qualified Data.Term as Family
import Funsat.ECircuit as C
import Funsat.TermCircuit
import Funsat.TermCircuit.SomeCircuit
import Control.Monad.Writer (WriterT, runWriterT, liftM, tell)
import Control.Monad.Cont (MonadTrans)
import Control.Applicative (Applicative)
import Prelude hiding (fromInteger)
import Data.Strict

-- -------------------------------------------------
-- Symbol factories
-- -------------------------------------------------

type SymbolFactory s m repr =
                       ( Monad m
                       , ECircuit repr, OneCircuit repr, NatCircuit repr
                       , Co repr (Family.Var s)
                       , Show(Family.Id s), Show(Family.Var s),Ord(Family.Var s)) =>
                          (String -> m (Family.Var s))
                       -> (String -> m (Natural (Family.Var s)))
                       -> (Family.Id s, Int)
                       -> m (s, [(String, repr (Family.Var s))])

class Monad m => MonadCircuit m where
  type Var m
  assertAll :: [SomeCircuit (Var m)] -> m ()
  assertAll' :: String -> [SomeCircuit (Var m)] -> m ()

newtype CircuitM v m a = CircuitM {unCircuitM::WriterT [Pair String (SomeCircuit v)] m a}
    deriving (Applicative, Functor, Monad, MonadTrans)

runCircuitM :: (Co repr v, OneCircuit repr, ECircuit repr, NatCircuit repr, Monad m
               ) => CircuitM v m a -> m (a, [(String, repr v)])
runCircuitM = liftM (second (map (second unC . unpack))) . runWriterT . unCircuitM

unpack(a :!: b) = (a,b)

instance Monad m => MonadCircuit (CircuitM v m) where
  type Var (CircuitM v m) = v
  assertAll x = CircuitM $ tell [ "" :!: andL x]
  assertAll' msg x = CircuitM $ tell [msg :!: andL x]

