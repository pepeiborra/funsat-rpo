{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

{-| Extension of Funsat.Circuit to generate RPO constraints as boolean circuits

-}
module Funsat.TermCircuit
   (
   -- * Circuit language extensions for Term circuits
   -- ** The language extension for Term circuits
    TermCircuit(..), Co, CoTerm, CoTerm_
   -- ** The language extension for an efficient only-one-true predicate
   ,OneCircuit(..), oneDefault, oneExist
   -- ** The language extension for asserting a fact
   ,AssertCircuit(..), assertCircuits
   -- * Concrete implementations
--   ,runEval, runEvalM, evalB, evalN
   -- ** An implementation via trees for representation
   ,Tree(..), TreeF(..), simplifyTree, printTree, mapTreeTerms, typeCheckTree, collectIdsTree, CircuitType(..)
   ,tOpen, tTrue, tFalse, tNot, tOne, tAnd, tOr, tXor, tIff, tOnlyIf, tEq, tLt, tIte, tIteNat, tTermGt, tTermEq
   -- ** An evaluator
   ,pattern WrapEval, WrapEval(..), unwrapEval
   ,Flip(..), EvalM(..), eval, evalB, evalN, unEvalM, runEvalM
   ,WrapWithTerm(..), TermEval(..)
   )
 where

{-
    This file is heavily based on parts of funsat.

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PUTermSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad.Cont
import           Control.Monad.Reader (MonadReader(..))
import           Data.Bifoldable ( Bifoldable(bifoldMap) )
import           Data.Bifunctor ( Bifunctor(bimap) )
import           Data.Bitraversable ( Bitraversable (bitraverse), bimapDefault, bifoldMapDefault )
import           Data.Foldable (Foldable)
import           Data.Hashable
import           Data.Monoid (Monoid(..))
import           Data.Set ( Set )
import           Data.Traversable (Traversable, traverse)
import Prelude hiding( not, and, or, (>), fromInteger, max )

import           Funsat.ECircuit as Funsat
                       ( Circuit(..), Co
                       , ECircuit(..)
                       , NatCircuit(..), Natural(..), MaxCircuit(..)
                       , ExistCircuit(..)
                       , CastCircuit(..)
                       , BIEnv
                       , Eval, EvalF(..), runEval
                       )
import           Funsat.Types ( Var(..) )
import           Funsat.TermCircuit.Internal.Syntax

import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Prelude as Prelude

import           Data.Term hiding (Var)
import           Data.Term.Rules (collectIds)
import qualified Data.Term.Family as Family

import           Text.PrettyPrint.HughesPJClass hiding (first)

import           GHC.Generics
import           GHC.Prim (Constraint)

class Circuit repr => OneCircuit repr where
    -- | @one bb = length (filter id bb) == 1@
    one  :: (Co repr var) => [repr var] -> repr var
    one  = oneDefault

class Circuit repr => AssertCircuit repr where
  assertCircuit :: repr a -> repr a -> repr a

assertCircuits :: AssertCircuit repr => [repr a] -> repr a -> repr a
assertCircuits [] e = e
assertCircuits (a:aa) e = assertCircuit a $ assertCircuits aa e

oneExist :: (ECircuit repr, ExistCircuit repr, Co repr v) => [repr v] -> repr v
oneExist [] = false
oneExist vv = (`runCont` id) $ do
          ones  <- replicateM (length vv) (cont existsBool)
          zeros <- replicateM (length vv) (cont existsBool)
          let encoding = andL
                  [ (one_i  `iff` ite b_i zero_i1 one_i1) `and`
                    ( zero_i `iff` (not b_i `and` zero_i1))
                   | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                      zip5 vv ones zeros (tail ones ++ [false]) (tail zeros ++ [true])
                  ]
          return (head ones `and` encoding)
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []

oneDefault :: (Circuit repr, Co repr v) => [repr v] -> repr v
oneDefault [] = false
oneDefault (v:vv) = (v `and` none vv) `or` (not v `and` oneDefault vv)

-- -------------
-- Term Circuits
-- -------------
type family CoTerm_ (repr :: * -> *) (termF :: * -> *) v' v :: Constraint
class Circuit repr => TermCircuit repr where
    termGt, termGe, termEq :: (termF ~ Family.TermF repr
                              ,id    ~ Family.Id termF
                              ,v     ~ Family.Var id
                              ,Foldable termF, HasId1 termF
                              ,Eq (Term termF v')
                              ,CoTerm repr termF v' v
                              ) =>
                              Term termF v' -> Term termF v' -> repr v
--    termGe s t | pprTrace (text "termGe" <+> pPrint s <+> pPrint t) False = undefined
    termGe s t = termGt s t `or` termEq s t
    termEq s t = not(termGt s t) `and` termGe s t

type CoTerm repr term tv v = (Co repr v, CoTerm_ repr term tv v)

-- ----------------------
-- Generic term circuits
-- ----------------------

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.

data TreeF term (a :: *)
               = TTrue
               | TFalse
               | TFromInteger Integer
               | TNot a
               | TAnd a a
               | TOr  a a
               | TXor a a
               | TIff a a
               | TOnlyIf a a
               | TIte a a a
               | TIteNat a a a
               | TEq  a a
               | TLt  a a
               | TPlus a a
               | TMinus a a
               | TMul a a
               | TMax a a
               | TOne [a]
               | TTermEq term term
               | TTermGt term term
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Bifunctor TreeF where bimap = bimapDefault
instance Bifoldable TreeF where bifoldMap = bifoldMapDefault
instance Bitraversable TreeF where
  bitraverse _ _ TTrue = pure TTrue
  bitraverse _ _ TFalse = pure TFalse
  bitraverse _ _ (TFromInteger n) = pure $ TFromInteger n
  bitraverse _ g (TNot t) = TNot <$> g t
  bitraverse _ g (TAnd t u) = TAnd <$> g t <*> g u
  bitraverse _ g (TOr  t u) = TOr  <$> g t <*> g u
  bitraverse _ g (TXor t u) = TXor <$> g t <*> g u
  bitraverse _ g (TIff t u) = TIff <$> g t <*> g u
  bitraverse _ g (TOnlyIf t u)   = TOnlyIf <$> g t <*> g u
  bitraverse _ g (TIte i t e)    = TIte    <$> g i <*> g t <*> g e
  bitraverse _ g (TIteNat i t e) = TIteNat <$> g i <*> g t <*> g e
  bitraverse _ g (TEq t u)  = TEq <$> g t <*> g u
  bitraverse _ g (TLt t u)  = TLt <$> g t <*> g u
  bitraverse _ g (TPlus t u) = TPlus <$> g t <*> g u
  bitraverse _ g (TMinus t u) = TMinus <$> g t <*> g u
  bitraverse _ g (TMul t u) = TMul <$> g t <*> g u
  bitraverse _ g (TMax t u) = TMax <$> g t <*> g u
  bitraverse _ g (TOne tt)  = TOne <$> traverse g tt
  bitraverse f _ (TTermEq t u) = TTermEq <$> f t <*> f u
  bitraverse f _ (TTermGt t u) = TTermGt <$> f t <*> f u

data Tree term v = TNat (Natural v)
                 | TLeaf v
                 | TFix {tfix :: TreeF term (Tree term v)}
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type instance Family.TermF (Tree term) = Family.TermF term
type instance Family.Id (Tree term) = Family.Id term
type instance Family.Var (Tree term) = Family.Var term

instance Bifunctor Tree where bimap = bimapDefault
instance Bifoldable Tree where bifoldMap = bifoldMapDefault
instance Bitraversable Tree where
  bitraverse _ g (TNat v)  = TNat  <$> (traverse g v)
  bitraverse _ g (TLeaf v) = TLeaf <$> g v
  bitraverse f g (TFix t)  = TFix  <$> bitraverse f (bitraverse f g) t

foldTree fnat  _ _ (TNat v)  = fnat v
foldTree _ fleaf _ (TLeaf v) = fleaf v
foldTree fn fl f (TFix t) = f (fmap (foldTree fn fl f) t)

foldTreeM :: Monad f => (v -> f res) -> (v -> f res) -> (TreeF term res -> f res) -> Tree term v -> f res
foldTreeM fnat _ _ (TNat v) = fnat (encodeNatural v)
foldTreeM _ fleaf _ (TLeaf v) = fleaf v
foldTreeM fn fl f (TFix t) = f =<< T.mapM (foldTreeM fn fl f) t

tLeaf   = TLeaf
tNat    = TNat
tTrue   = TFix TTrue
tFalse  = TFix TFalse
tFromInt= TFix . TFromInteger
tNot    = TFix . TNot
tOne    = TFix . TOne
tAnd    = (TFix.) . TAnd
tOr     = (TFix.) . TOr
tXor    = (TFix.) . TXor
tIff    = (TFix.) . TIff
tOnlyIf = (TFix.) . TOnlyIf
tIte    = ((TFix.).) . TIte
tIteNat = ((TFix.).) . TIteNat
tEq     = (TFix.) . TEq
tLt     = (TFix.) . TLt
tMax    = (TFix.) . TMax
tPlus   = (TFix.) . TPlus
tMinus  = (TFix.) . TMinus
tMul    = (TFix.) . TMul
tTermGt = (TFix.) . TTermGt
tTermEq = (TFix.) . TTermEq

tOpen (TFix t) = Just t
tOpen _ = Nothing

tClose = TFix

tId TTrue  = tTrue
tId TFalse = tFalse
tId (TFromInteger n) = tFromInt n
tId (TNot n) = tNot n
tId (TOne n) = tOne n
tId (TAnd t1 t2) = tAnd t1 t2
tId (TOr  t1 t2) = tOr t1 t2
tId (TXor t1 t2) = tXor t1 t2
tId (TIff t1 t2) = tIff t1 t2
tId (TOnlyIf t1 t2) = tOnlyIf t1 t2
tId (TMax t1 t2) = tMax t1 t2
tId (TEq t1 t2) = tEq t1 t2
tId (TLt t1 t2) = tLt t1 t2
tId (TIte c t e) = tIte c t e
tId (TIteNat c t e) = tIteNat c t e
tId (TPlus a b)  = tPlus a b
tId (TMinus a b) = tMinus a b
tId (TMul a b)   = tMul a b
--tId (TTermGt t u) = tTermGt t u
--tId (TTermEq t u) = tTermEq t u
tId _ = error "internal error - unreachable"

mapTreeTerms :: (term -> term') -> Tree term v -> Tree term' v
mapTreeTerms f = foldTree tNat tLeaf f'
  where
   f' (TTermGt t u) = tTermGt (f t) (f u)
   f' (TTermEq t u) = tTermGt (f t) (f u)
   f' t = tId t

printTree :: (Pretty a, Pretty(Natural a), Pretty t) => Int -> Tree t a -> Doc
printTree p t = foldTree fn fl f t p where
  fl v _ = pPrint v
  fn v _ = pPrint v
  f TTrue  _ = text "true"
  f TFalse _ = text "false"
  f (TNot t)        p = pP p 10 $ text "!" <> t 9
  f (TMax t1 t2)    p = pP p 5 $ text "MAX" <+> (t1 5 $$ t2 5)
  f (TAnd t1 t2)    p = pP p 5 $ text "AND" <+> (t1 5 $$ t2 5)
--   f (TAnd t1 t2) p = pP p 5 $ pt 5 t1 <+> text "&" <+> pt 5 t2
  f (TOr t1 t2)     p = pP p 5 $ text "OR " <+> (t1 5 $$ t2 5)
--   f (TOr  t1 t2) p = pP p 5 $ t1 5 <+> text "||" <+> pt 5 t2
  f (TXor t1 t2)    p = pP p 5 $ t1 5 <+> text "xor" <+> t2 5
  f (TIff t1 t2)    p = pP p 3 $ t1 3 <+> text "<->" <+> t2 3
  f (TOnlyIf t1 t2) p = pP p 3 $ t1 3 <+> text "-->" <+> t2 3
  f (TIte c t e)    p = pP p 2 $ text "IFTE" <+> (c 1 $$ t 1 $$ e 1)
  f (TIteNat c t e) p = pP p 2 $ text "IFTE" <+> (c 1 $$ t 1 $$ e 1)
  f (TEq n1 n2)     p = pP p 7 (n1 1 <+> text "==" <+> n2 1)
  f (TLt n1 n2)     p = pP p 7 (n1 1 <+> text "<"  <+> n2 1)
  f (TOne vv)       p = pP p 1 $ text "ONE" <+> (fsep $ punctuate comma $ map ($ 1) vv)
  f (TTermGt t u)   p = pP p 6 $ pPrint t <+> text ">" <+> pPrint u
  f (TTermEq t u)   p = pP p 6 $ pPrint t <+> text "=" <+> pPrint u
  f (TFromInteger i) p = integer i
  f (TPlus  a b)     p = pP p 8 (a 8 <+> text "+" <+> b 8)
  f (TMinus a b)     p = pP p 8 (a 8 <+> text "-" <+> b 8)
  f (TMul a b)       p = pP p 9 (a 9 <+> text "-" <+> b 9)

pP prec myPrec doc = if myPrec Prelude.> prec then doc else parens doc

collectIdsTree :: (Functor t, Foldable t, HasId1 t, Ord(Id t)) => Tree (Term t v) a -> Set (Id t)
collectIdsTree = foldTree (const mempty) (const mempty) f
  where
   f (TNot    t1)    = t1
   f (TAnd    t1 t2) = mappend t1 t2
   f (TOr     t1 t2) = mappend t1 t2
   f (TXor    t1 t2) = mappend t1 t2
   f (TOnlyIf t1 t2) = mappend t1 t2
   f (TIff    t1 t2) = mappend t1 t2
   f (TPlus   t1 t2) = mappend t1 t2
   f (TMinus  t1 t2) = mappend t1 t2
   f (TMul    t1 t2) = mappend t1 t2
   f (TIte t1 t2 t3) = t1 `mappend` t2 `mappend` t3
   f (TIteNat t1 t2 t3) = t1 `mappend` t2 `mappend` t3
   f (TTermGt t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f (TTermEq t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f TOne{} = mempty
   f TTrue  = mempty
   f TFalse = mempty
   f TEq{}  = mempty
   f TLt{}  = mempty
   f TMax{} = mempty
   f TFromInteger{} = mempty

data CircuitType = Nat | Bool deriving (Eq, Show)

typeCheckTree :: Show term => Tree term v -> Maybe CircuitType
typeCheckTree = foldTreeM (const (pure Nat)) (const (pure Bool)) f where
    f TFalse = return Bool
    f TTrue  = return Bool
    f TFromInteger{} = return Nat
    f (TNot Bool) = return Bool
    f (TAnd Bool Bool) = return Bool
    f (TOr  Bool Bool) = return Bool
    f (TXor Bool Bool) = return Bool
    f (TIff Bool Bool) = return Bool
    f (TOnlyIf Bool Bool) = return Bool
    f (TIte Bool a b)
      | a==b = return a
      | otherwise    = fail "TIte"
    f (TIteNat Bool a b)
      | a==b = return a
      | otherwise    = fail "TIte"
    f (TOne vv)
      | all ((==) Bool) vv = return Bool
      | otherwise = fail "TOne"
    f TTermGt{} = return Bool
    f TTermEq{} = return Bool
    f (TEq Nat Nat) = return Bool
    f (TLt Nat Nat) = return Bool
    f (TMax Nat Nat) = return Nat
    f (TPlus Nat Nat) = return Nat
    f (TMinus Nat Nat) = return Nat
    f (TMul Nat Nat) = return Nat
    f other = fail (show other)


-- | Performs obvious constant propagations.
simplifyTree :: (Eq a, Eq term) => Tree term a -> Tree term a
simplifyTree = foldTree TNat TLeaf f where
  f TFalse      = tFalse
  f TTrue       = tTrue
  f (TFromInteger i) = tFromInt i
  f (TNot (tOpen -> Just TTrue))  = tFalse
  f (TNot (tOpen -> Just TFalse)) = tTrue
  f it@TNot{} = tClose it

  f (TAnd (tOpen -> Just TFalse) _) = tFalse
  f (TAnd (tOpen -> Just TTrue) r)  = r
  f (TAnd l (tOpen -> Just TTrue))  = l
  f (TAnd _ (tOpen -> Just TFalse)) = tFalse
  f it@TAnd{} = tClose it

  f (TOr (tOpen -> Just TTrue) _) = tTrue
  f (TOr (tOpen -> Just TFalse) r) = r
  f (TOr _ (tOpen -> Just TTrue)) = tTrue
  f (TOr l (tOpen -> Just TFalse)) = l
  f it@TOr{} = tClose it

  f (TXor (tOpen -> Just TTrue) (tOpen -> Just TTrue)) = tFalse
  f (TXor (tOpen -> Just TFalse) r) = r
  f (TXor l (tOpen -> Just TFalse)) = l
  f (TXor (tOpen -> Just TTrue) r) = tNot r
  f (TXor l (tOpen -> Just TTrue)) = tNot l
  f it@TXor{} = tClose it

  f (TIff (tOpen -> Just TFalse) (tOpen -> Just TFalse)) = tTrue
  f (TIff (tOpen -> Just TFalse) r) = tNot r
  f (TIff (tOpen -> Just TTrue)  r) = r
  f (TIff l (tOpen -> Just TFalse)) = tNot l
  f (TIff l (tOpen -> Just TTrue))  = l
  f it@TIff{} = tClose it

  f it@(l `TOnlyIf` r) =
    case (tOpen l, tOpen r) of
         (Just TFalse,_)  -> tTrue
         (Just TTrue,_)   -> r
         (_, Just TTrue)  -> tTrue
         (_, Just TFalse) -> tNot l
         _           -> tClose it
  f it@(TIte x t e) =
    case (tOpen x, tOpen t, tOpen e) of
         (Just TTrue,_,_)  -> t
         (Just TFalse,_,_) -> e
         (_,Just TTrue,_)  -> tOr x e
         (_,Just TFalse,_) -> tAnd (tNot x) e
         (_,_,Just TTrue)  -> tOr (tNot x) t
         (_,_,Just TFalse) -> tAnd x t
         _      -> tClose it
  f it@(TIteNat x t e) =
    case (tOpen x, tOpen t, tOpen e) of
         (Just TTrue,_,_)  -> t
         (Just TFalse,_,_) -> e
         (_,Just TTrue,_)  -> tOr x e
         (_,Just TFalse,_) -> tAnd (tNot x) e
         (_,_,Just TTrue)  -> tOr (tNot x) t
         (_,_,Just TFalse) -> tAnd x t
         _      -> tClose it

  f t@(TEq x y) = if x == y then tTrue  else tClose t
  f t@(TLt x y) = if x == y then tFalse else tClose t
  f t@TPlus{}   = tClose t
  f t@TMinus{}  = tClose t
  f t@TMul{}    = tClose t
  f t@TMax{}    = tClose t
  f (TOne [])   = tFalse
  f t@TOne{}    = tClose t
  f (TTermEq s t) | s == t = tTrue
  f t@TTermEq{} = tClose t
  f (TTermGt s t) | s == t = tFalse
  f t@TTermGt{} = tClose t


instance (ECircuit c, OneCircuit c, TermCircuit c, NatCircuit c, MaxCircuit c
         ) =>
  CastCircuit (Tree term) c
 where
  type CastCo (Tree term) c v = ( CoTerm c (TermF term) (Family.Var term) v
                                , term ~ Term (TermF c) (Family.Var term)
--                                , v    ~ Family.Var c
                                , v    ~ Family.Var (Id(TermF term))
                                , Foldable (TermF term)
                                , HasId1 (TermF term)
                                , Eq term
                                )
  castCircuit (TFix TTrue) = true
  castCircuit (TFix TFalse) = false
  castCircuit (TFix (TAnd t1 t2)) = and (castCircuit t1) (castCircuit t2)
  castCircuit (TLeaf v) = input v
  castCircuit (TFix (TOr t1 t2)) = or (castCircuit t1) (castCircuit t2)
  castCircuit (TFix (TXor t1 t2)) = xor (castCircuit t1) (castCircuit t2)
  castCircuit (TFix (TNot t)) = not (castCircuit t)
  castCircuit (TNat n) = nat n
  castCircuit (TFix (TFromInteger i)) = fromInteger i
  castCircuit (TFix(TIte i t e)) = ite (castCircuit i) (castCircuit t) (castCircuit e)
  castCircuit (TFix(TIteNat i t e)) = iteNat (castCircuit i) (castCircuit t) (castCircuit e)
  castCircuit (TFix(TIff t1 t2)) = iff (castCircuit t1) (castCircuit t2)
  castCircuit (TFix(TOnlyIf t1 t2)) = onlyif (castCircuit t1) (castCircuit t2)
  castCircuit (TFix(TEq s t)) = eq (castCircuit s) (castCircuit t)
  castCircuit (TFix(TLt s t)) = lt (castCircuit s) (castCircuit t)
  castCircuit (TFix(TPlus  s t)) = castCircuit s +# castCircuit t
  castCircuit (TFix(TMinus s t)) = castCircuit s -# castCircuit t
  castCircuit (TFix(TMul   s t)) = castCircuit s *# castCircuit t
  castCircuit (TFix(TMax   s t)) = max (castCircuit s) (castCircuit t)
  castCircuit (TFix(TOne tt)) = one (map castCircuit tt)
  castCircuit (TFix(TTermEq t u)) = termEq ( t) ( u)
  castCircuit (TFix(TTermGt t u)) = termGt ( t) (u)

--   castCircuit = foldTree input nat f where
--     f TTrue        = true
--     f TFalse       = false
--     f (TAnd t1 t2) = and t1 t2
--     f (TOr t1 t2)  = or  t1 t2
--     f (TXor t1 t2) = xor t1 t2
--     f (TNot t)     = not t
--     f (TIff t1 t2) = iff t1 t2
--     f (TOnlyIf t1 t2) = onlyif t1 t2
--     f (TIte x t e) = ite x t e
--     f (TEq t1 t2)  = eq t1 t2
--     f (TLt t1 t2)  = lt t1 t2
--     f (TOne tt)    = one tt
--     f c@(TTermEq t u) = termEq t u
--     f c@(TTermGt t u) = termGt t u

type instance Co (Tree term) v = ()
instance Circuit (Tree term) where
    true  = tTrue
    false = tFalse
    input = tLeaf
    and   = tAnd
    or    = tOr
    not   = tNot

instance ECircuit (Tree term) where
    xor    = tXor
    iff    = tIff
    onlyif = tOnlyIf
    ite    = tIte

instance NatCircuit (Tree term) where
    eq       = tEq
    lt       = tLt
    (+#)     = tPlus
    (-#)     = tMinus
    (*#)     = tMul
    nat      = tNat
    iteNat   = tIteNat
    fromInteger = tFromInt

instance MaxCircuit (Tree term) where max = tMax

instance OneCircuit (Tree term) where
    one   = tOne

type instance CoTerm_ (Tree term) termF tv v = (term ~ Term termF tv)
instance TermCircuit (Tree term) where
    termGt = tTermGt
    termEq = tTermEq


-- -------------------------------------------------------------
-- A phantom type wrapper for packaging term circuit evaluators
-- -------------------------------------------------------------

newtype WrapWithTerm term f a = WrapWithTerm { unwrapWithTerm :: f a}
                              deriving (Applicative, Functor, Monad)
deriving instance MonadReader (BIEnv v) f => MonadReader (BIEnv v) (WrapWithTerm term f)

newtype WrapEval term v = WrapEval_ {unWrapEval_ :: WrapWithTerm term Eval v}
pattern WrapEval a = WrapEval_ (WrapWithTerm a)

type instance Co (WrapEval term) v = Co Eval v
instance Circuit (WrapEval term) where
   true  = WrapEval true
   false = WrapEval false
   input = WrapEval . input
   not   = wrap1 Funsat.not
   andL  = wrapL andL
   orL   = wrapL orL
   and   = wrap2 and
   or    = wrap2 or

instance NatCircuit (WrapEval term) where
   nat = WrapEval . nat
   eq  = wrap2 eq
   lt  = wrap2 lt
   gt  = wrap2 gt
   fromInteger = WrapEval . fromInteger
   (+#) = wrap2 (+#)
   (-#) = wrap2 (-#)
   (*#) = wrap2 (*#)
   iteNat = wrap3 iteNat

instance MaxCircuit (WrapEval term) where max = wrap2 max

instance ECircuit (WrapEval term) where
   ite = wrap3 ite
   iff = wrap2 iff
   onlyif = wrap2 onlyif
   xor = wrap2 xor

instance CastCircuit (WrapEval term) (WrapEval term) where
  type CastCo (WrapEval term) (WrapEval term) v = ()
  castCircuit = id

data TermEval a v = Term {(>), (>~), (~~) :: a -> a -> EvalM v Bool}

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

-- --------------------------------
-- A monad for evaluating circuits
-- --------------------------------

newtype Flip t a b = Flip {unFlip::t b a} deriving Generic

instance NFData (t b a) => NFData (Flip t a b)

newtype EvalM v a = EvalTerm {unEvalFlip :: Flip EvalF v a} deriving Generic
pattern EvalM a = EvalTerm(Flip(Eval a))
runEvalM env = flip unEval env . unFlip . unEvalFlip

instance Show (EvalM v a) where show _ = "evalM computation"
instance NFData (EvalM v a)

unEvalM :: EvalM a b -> EvalF b a
unEvalM = unFlip . unEvalFlip

evalB :: Eval v -> EvalM v Bool
evalN :: Eval v -> EvalM v Int
evalB c = liftM (fromRight :: Either Int Bool -> Bool) (eval c)
evalN c = liftM (fromLeft  :: Either Int Bool -> Int)  (eval c)
eval  c = do {env <- ask; return (runEval env c)}

instance Functor (EvalM v) where
  fmap f (EvalM m) = EvalM $ \env -> f(m env) ;
  fmap _ _ = error "Pleasing the exhaustive pattern matching checker"

instance Applicative (EvalM v) where
  pure x = return x
  f <*> x = EvalM $ \env -> runEvalM env f $ runEvalM env x

instance Monad (EvalM v) where
  return x = EvalM $ \_ -> x
  m >>= f  = EvalM $ \env -> runEvalM env $ f $ runEvalM env m

instance MonadReader (BIEnv v) (EvalM v) where
  ask       = EvalM $ \env -> env
  local f m = EvalM $ \env -> runEvalM (f env) m

-- ------------------------
-- Hashable instances
-- ------------------------
{-
instance Hashable Var where
  newtype Var :->: x = VarTrie (Int :->: x)
  empty = VarTrie HashMap.empty
  lookup (V i) (VarTrie t) = HashMap.lookup i t
  insert (V i) v (VarTrie t) = VarTrie (HashMap.insert i v t)
  toList (VarTrie t) = map (first V) (HashMap.toList t)
-}
deriving instance Hashable Var -- where hashWithSalt s (V i) = hashWithSalt s i
