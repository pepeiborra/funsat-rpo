{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Funsat.TermCircuit.Symbols where

import Control.Arrow(second)
import Control.DeepSeq
import qualified Data.Term as Family
import Funsat.ECircuit as C
import Funsat.TermCircuit
import Control.Monad.Writer (WriterT, runWriterT, liftM, tell)
import Control.Monad.Cont (MonadTrans)
import Control.Applicative (Applicative)

-- ----------------------------
-- Type for natural variables
-- ----------------------------

newtype Natural v = Natural {encodeNatural::v} deriving (Eq,Ord,Show,NFData)

-- --------------------------------
-- Typing untyped circuits
-- --------------------------------

newtype SomeCircuit v = SomeCircuit { unC :: forall repr . (Circuit repr, OneCircuit repr, ECircuit repr, Co repr v) => repr v }

liftSomeCircuit :: (forall repr . (ECircuit repr, Co repr v) => repr v -> repr v) -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit  f (SomeCircuit x) = SomeCircuit (f x)
liftSomeCircuit2 :: (forall repr . (ECircuit repr, Co repr v) => repr v -> repr v -> repr v) -> SomeCircuit v -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit2 f (SomeCircuit x) (SomeCircuit y) = SomeCircuit (f x y)

instance Circuit SomeCircuit where
  type Co SomeCircuit v = ()
  true = SomeCircuit true
  false = SomeCircuit false
  input v = SomeCircuit (input v)
  not = liftSomeCircuit C.not
  and = liftSomeCircuit2 C.and
  or  = liftSomeCircuit2 C.or

instance OneCircuit SomeCircuit where
  one xx = SomeCircuit (one $ map unC xx)

instance ECircuit SomeCircuit where
  onlyif = liftSomeCircuit2 C.onlyif
  iff = liftSomeCircuit2 C.iff
  xor = liftSomeCircuit2 C.xor
  ite (SomeCircuit a) (SomeCircuit b) (SomeCircuit c) = SomeCircuit (ite a b c)

-- -------------------------------------------------
-- Generic encoding of RPO symbols with AF
-- -------------------------------------------------

type SymbolFactory s m repr =
                       (Monad m, ECircuit repr, OneCircuit repr, Co repr (Family.Var s)
                       ,Show(Family.Id s), Show(Family.Var s),Ord(Family.Var s)) =>
                          (String -> m (Family.Var s))
                       -> (String -> m (Natural (Family.Var s)))
                       -> (Family.Id s, Int)
                       -> m (s, [(String, repr (Family.Var s))])

class Monad m => MonadCircuit m where
  type Var m
  assertAll :: [SomeCircuit (Var m)] -> m ()
  assertAll' :: String -> [SomeCircuit (Var m)] -> m ()

newtype CircuitM v m a = CircuitM {unCircuitM::WriterT [(String,SomeCircuit v)] m a}
    deriving (Applicative, Functor, Monad, MonadTrans)

--runCircuitM :: (Co repr v, OneCircuit repr, ECircuit repr, Monad m) => CircuitM v m a -> m (a, [String,repr v])
runCircuitM = liftM (second (map (second unC))) . runWriterT . unCircuitM

instance Monad m => MonadCircuit (CircuitM v m) where
  type Var (CircuitM v m) = v
  assertAll x = CircuitM $ tell [("", andL x)]
  assertAll' msg x = CircuitM $ tell [(msg, andL x)]

