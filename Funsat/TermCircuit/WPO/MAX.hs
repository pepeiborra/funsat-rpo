{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Funsat.TermCircuit.WPO.MAX(MAX(..), max, maxM, agt, age, wF) where

import Control.DeepSeq (NFData)
import Data.Foldable (Foldable, toList)
import Data.Term (Term, foldTerm, HasId1(..))
import qualified Data.Term as Family
import Data.Typeable
import Funsat.ECircuit hiding (max)
import Funsat.TermCircuit.Symbols
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.WPO
import Funsat.TermCircuit.WPO.Symbols hiding (MAX)
import qualified Funsat.TermCircuit.WPO.Symbols as Algebra
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (fromInteger, sum, max)

newtype MAX v a = MAX { theSymbol :: WPOSymbolBase v a }
  deriving (Eq, Show, Ord, Pretty
           ,Functor, Foldable, NFData
           ,HasPrecedence, HasStatus, HasFiltering, WPOSymbol
           ,Typeable)

type instance Family.Var (MAX v id) = v
type instance Family.Id  (MAX v id) = id

max :: WPOOptions -> Natural v -> SymbolFactory (MAX v id) m repr
max opts  w0 b n x = runCircuitM $ maxM opts w0 b n x
maxM opts w0 b n x = do
  s <- wpoM b n opts (const Algebra.MAX) x

  -- Fix the contants to N
  let zero = fromInteger 0
  assertAll [ nat p `gt` zero | p <- getP s]

  return (MAX s)

agt,age ::( termF ~ Family.TermF repr
          , id    ~ Family.Id termF
          , v     ~ Family.Var id
          , WPOCircuit repr, MaxCircuit repr, Co repr v
          , HasId1 termF, Functor termF, Foldable termF
          , WPOSymbol id, WPOAlgebra repr
          , Eq v'
          ) => Term termF v' -> Term termF v' -> repr v
agt s t = (w s `gt` w t)
age s t = (w s `ge` w t)

w = foldTerm(const w0) wF

wF t
  | [] <- sp_ii = nat(getW i)
  | otherwise
  = maxL [ (nat sc_i *# t_i) +# nat sp_i
            | ( sc_i, sp_i, t_i) <- zip3 (getC i) (getP i) (toList t)]
   where
    Just i = getId1 t
    sp_ii  = getP i
