{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Funsat.TermCircuit.WPO.MPOL(MPOL(..), mpol, agt, age) where

import Control.DeepSeq (NFData)
import Control.Monad (when)
import Data.Foldable (Foldable)
import Data.Term (Term, foldTerm, HasId1(..), vars)
import qualified Data.Term as Family
import Data.Typeable
import Funsat.ECircuit
import Funsat.TermCircuit.Internal.Syntax
import Funsat.TermCircuit.Symbols
import Funsat.TermCircuit.Ext
import Funsat.TermCircuit.WPO
import Funsat.TermCircuit.WPO.Symbols hiding (MAX, POL)
import Funsat.TermCircuit.WPO.POL as POL (wF, vc)
import Funsat.TermCircuit.WPO.MAX as MAX (wF)
import qualified Funsat.TermCircuit.WPO.Symbols as Algebra
import Text.PrettyPrint.HughesPJClass
import Prelude hiding (fromInteger, sum, not)

newtype MPOL v a = MPOL { theSymbol :: WPOSymbolBase v a }
  deriving (Eq, Show, Ord, Pretty
           ,Functor, Foldable, NFData
           ,HasPrecedence, HasStatus, HasFiltering, WPOSymbol
           ,Typeable)

type instance Family.Var (MPOL v id) = v
type instance Family.Id  (MPOL v id) = id

mpol :: WPOOptions -> Natural v -> SymbolFactory (MPOL v id) m repr
mpol opts w0 b n x = runCircuitM $ mpolM opts w0 b n (\max -> if max then Algebra.MAX else Algebra.POL) x
mpolM opts w0 b n interpretAlgebraBit x = do
  s <- wpoM b n opts interpretAlgebraBit x

  let zero = fromInteger 0
  -- Enforcing the SIMP constraint
  assertAll [ input st --> (nat c `gt` zero)
            | (st,c) <- zip (encodeSel s)
                            (encodeP s)
            ]
  -- Enforcing WMIN
  let wf = nat(encodeW s)
  assertAll[(wf `gt` nat  w0) \/
             orL [ nat sc_i `gt` zero | sc_i <- encodeC s]]

  -- Fix the contants to N
--   assertAll [ nat p `gt` zero | p <- getP s]

  -- For arity 1, fix to pol
  when (snd x < 2) $ assertAll [not $ input(getAlg s)]

  return (MPOL s)

agt,age ::( termF ~ Family.TermF repr
          , id    ~ Family.Id termF
          , v     ~ Family.Var id
          , ECircuit repr, MaxCircuit repr, WPOCircuit repr, Co repr v
          , HasId1 termF, Functor termF, Foldable termF
          , WPOSymbol id, WPOAlgebra repr
          , Eq v'
          ) => Term termF v' -> Term termF v' -> repr v
agt s t = (w s `gt` w t) /\ andL [ vc x s `ge` vc x t | x <- vars t]
age s t = (w s `ge` w t) /\ andL [ vc x s `ge` vc x t | x <- vars t]

w :: ( WPOSymbol (Family.Id t)
     , ECircuit repr, MaxCircuit repr, WPOCircuit repr
     , HasId1 t, Foldable t, Co repr v
     , Functor t
     , id ~ Family.Id t
     , v ~ Family.Var id
     ) => Term t a -> repr v
w = foldTerm (const w0) f where
  f t
    | ar < 2    = POL.wF t
    | otherwise = iteNat (input$ getAlg i)
                         (MAX.wF t)
                         (POL.wF t)
   where
    Just i = getId1 t
    ar = length $ getC i
