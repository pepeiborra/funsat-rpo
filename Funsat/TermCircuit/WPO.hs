{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}

module Funsat.TermCircuit.WPO
       ( WPOCircuit(..), WPOAlgebra(..), WPOSymbol(..)
       , termGt_, termGe_
       )where

import Data.Foldable (Foldable)
import Data.Term as Family
import Funsat.ECircuit
import Funsat.TermCircuit
import Funsat.TermCircuit.Internal.Syntax
import Funsat.TermCircuit.Ext

import Prelude.Extras
import Prelude hiding (and, not, or, fromInteger, (>))

class (TermCircuit repr, NatCircuit repr) => WPOCircuit repr where
  w0 :: Co repr v => repr v

class (HasPrecedence id, HasStatus id, HasFiltering id) =>  WPOSymbol id where
  getW   :: id ->  Natural(Family.Var id)
  getC   :: id -> [Natural(Family.Var id)]
  getP   :: id -> [Natural(Family.Var id)]
  getAlg :: id -> Family.Var id

-- WPO is algebra + simplification ordering
-- There are many algebras, but the simplification constraints are fixed
class WPOCircuit repr => WPOAlgebra repr where
  aGt, aGe, aEq :: ( termF ~ Family.TermF repr
                   , id ~ Family.Id termF
                   , v ~ Family.Var id
                   , Functor termF
                   , WPOSymbol id
                   , Eq1 termF, Eq v'
                   , Foldable termF, HasId1 termF
                   , CoTerm repr termF v' v
                   ) =>
              Term termF v' -> Term termF v' -> repr v

  aGe t u = aGt t u \/ aEq t u
  aEq t u = not (aGt t u) /\ aGe t u

termGte cmp1 s t = s `aGt` t \/ ( aEq s t /\ cmp1 s t)
termGt_ = termGte (sgte False)
termGe_ = termGte (sgte True)

sgte ::
        (var   ~ Family.Var id
        ,termf ~ Family.TermF repr
        ,id    ~ Family.Id termf
        ,Eq var', Eq1 termf
        ,Eq id, HasId1 termf, Foldable termf
        ,ECircuit repr, NatCircuit repr
        ,TermExtCircuit repr id
        ,HasFiltering id, HasPrecedence id
        ,CoTerm repr termf var' var
        ) =>
        Bool -> Term termf var' -> Term termf var' -> repr var

-- Simplification ordering
sgte isGe s t
--    | pprTrace (text "termGt_" <+> pPrint s <+> pPrint t) False = undefined
    | s == t = if isGe then true else false

    | Just id_t <- rootSymbol t
    , Just id_s <- rootSymbol s
    = cond2 id_s id_t tt_s tt_t `or` cond1 id_s tt_s

    | Just id_s <- rootSymbol s
    = cond1 id_s tt_s

    | Just id_t <- rootSymbol t
    = cond3 id_t

    | otherwise = false
   where
    tt_s = directSubterms s
    tt_t = directSubterms t

    cond1 id_s tt_s
      =  any (\(s_i,i) -> inAF i id_s `and` (s_i >~ t))
            (zip tt_s [1..])

    cond2 id_s id_t tt_s tt_t
      = all (\(t_j,j) -> inAF j id_t --> s > t_j) (zip tt_t [1..])
        `and`
         (or (precedence id_s `gt` precedence id_t)
             (and (precedence id_s `eq` precedence id_t)
                  (ex id_s id_t tt_s tt_t)))

    cond3 id_t = eq (precedence id_t) (fromInteger 0) /\ none(map input $ filtering_vv id_t)

    all f = andL . map f
    any f = orL  . map f
    ex = if isGe then exGe else exGt

    infixr 8 >
    infixr 8 >~
    infixr 7 -->

    s >  t  = termGt s t
    s >~ t  = termGe s t
    a --> b = onlyif a b
