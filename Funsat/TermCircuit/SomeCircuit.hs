{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ConstraintKinds #-}

module Funsat.TermCircuit.SomeCircuit where

import Funsat.ECircuit as Funsat
import Funsat.TermCircuit
import Prelude hiding (and,or,not,fromInteger)

-- --------------------------------
-- Existential Circuits
-- --------------------------------

newtype SomeCircuit v =
  SomeCircuit { unC :: forall repr .
                                     ( NatCircuit repr
                                     , OneCircuit repr
                                     , ECircuit repr
                                     , Co repr v
                                     ) => repr v }

liftSomeCircuit :: (forall repr . (ECircuit repr, Co repr v) => repr v -> repr v) -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit  f (SomeCircuit x) = SomeCircuit (f x)
liftSomeCircuit2 :: (forall repr . (ECircuit repr, NatCircuit repr, Co repr v) => repr v -> repr v -> repr v) -> SomeCircuit v -> SomeCircuit v -> SomeCircuit v
liftSomeCircuit2 f (SomeCircuit x) (SomeCircuit y) = SomeCircuit (f x y)

type instance Co SomeCircuit v = ()
instance Circuit SomeCircuit where
  true = SomeCircuit true
  false = SomeCircuit false
  input v = SomeCircuit (input v)
  not = liftSomeCircuit not
  and = liftSomeCircuit2 and
  or  = liftSomeCircuit2 or

instance OneCircuit SomeCircuit where
  one xx = SomeCircuit (one $ map unC xx)

instance ECircuit SomeCircuit where
  onlyif = liftSomeCircuit2 onlyif
  iff = liftSomeCircuit2 iff
  xor = liftSomeCircuit2 xor
  ite (SomeCircuit a) (SomeCircuit b) (SomeCircuit c) = SomeCircuit (ite a b c)

instance NatCircuit SomeCircuit where
  lt  = liftSomeCircuit2 lt
  eq  = liftSomeCircuit2 eq
  gt  = liftSomeCircuit2 gt
  (+#)= liftSomeCircuit2 (+#)
  (-#)= liftSomeCircuit2 (-#)
  (*#)= liftSomeCircuit2 (*#)
  nat v = SomeCircuit (nat v)
  fromInteger i = SomeCircuit (fromInteger i)
  iteNat (SomeCircuit a) (SomeCircuit b) (SomeCircuit c) = SomeCircuit (iteNat a b c)
