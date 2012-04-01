{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE CPP #-}
{- LANGUAGE NoMonoLocalBinds #-}

{-| Extension of Funsat.Circuit to generate RPO constraints as boolean circuits

-}
module Funsat.RPOCircuit
   (
   -- * Circuit language extensions for RPO circuits
   -- ** The language extension for RPO circuits
    RPOCircuit(..), Co, CoRPO, termGt_, termGe_, termEq_
   -- ** The language extension for multi term RPO comparisons
   ,RPOExtCircuit(..)
   -- ** The language extension for an efficient only-one-true predicate
   ,OneCircuit(..), oneDefault, oneExist
   -- ** The language extension for asserting a fact
   ,AssertCircuit(..)
   -- * Type classes for RPO identifiers
   ,HasPrecedence(..), precedence
   ,HasFiltering(..), listAF, inAF
   ,HasStatus(..), useMul, lexPerm
   -- * Concrete implementations
   -- ** An implementation via boolean circuits with sharing
   ,Shared(..), FrozenShared(..), runShared
--   ,runEval, runEvalM, evalB, evalN
   -- ** An implementation via graphs for displaying
   ,Graph(..), NodeType(..), EdgeType(..), shareGraph, shareGraph', runGraph
   -- ** An implementation via trees for representation
   ,Tree(..), TreeF(..), simplifyTree, printTree, mapTreeTerms, typeCheckTree, collectIdsTree, CircuitType(..)
   ,tOpen, tTrue, tFalse, tNot, tOne, tAnd, tOr, tXor, tIff, tOnlyIf, tEq, tLt, tIte, tTermGt, tTermEq
   -- ** An evaluator
   ,WrapEval(..)
   -- * Tools
   ,RPOCircuitProblem(..)
   ,removeComplex, removeExist
   ,toCNF, toCNF'
   ,projectRPOCircuitSolution
   ,reconstructNatsFromBits
   ) where

{-
    This file is heavily based on parts of funsat.

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

import Control.Applicative
import qualified Data.Array as A
import Control.Arrow (first)
import Control.Exception as CE (assert, throw, catch, evaluate, AssertionFailed(..))
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.RWS (execRWS, tell)
import Control.Monad.State.Strict hiding ((>=>), forM_)
import qualified Control.Monad.State.Lazy as Lazy hiding ((>=>), forM_)
import Data.Bifunctor     ( Bifunctor(bimap) )
import Data.Bifoldable    ( Bifoldable(bifoldMap) )
import Data.Bitraversable ( Bitraversable (bitraverse), bimapDefault, bifoldMapDefault )
import Data.Bimap( Bimap )
import Data.Foldable (Foldable)
import Data.List( nub,  sortBy)
import Data.List.Split (chunk)
import Data.Maybe( fromJust )
import Data.Hashable
import Data.Monoid (Monoid(..))
import Data.Set( Set )
import Data.Traversable (Traversable, traverse)
import System.IO.Unsafe
import Prelude hiding( not, and, or, (>) )

import Funsat.ECircuit ( Circuit(..)
                       , ECircuit(..)
                       , NatCircuit(nat,lt,gt,eq)
                       , ExistCircuit(..)
                       , CastCircuit(..)
                       , CircuitHash, falseHash, trueHash
                       , Eval, EvalF(..), fromBinary
                       , ECircuitProblem(..)
                       , reconstructNatsFromBits)
import Funsat.Types( CNF(..), Var(..), var, lit, Solution(..), litSign, litAssignment )
import Funsat.RPOCircuit.Internal

import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Data.Bimap as Bimap
import qualified Funsat.ECircuit as ECircuit
import qualified Prelude as Prelude
import qualified Data.HashMap as HashMap

import Data.Term hiding (Var)
import Data.Term.Rules (collectIds)
import qualified Data.Term.Family as Family

import Text.PrettyPrint.HughesPJClass hiding (first)

import GHC.Prim (Constraint)

type k :->:  v = HashMap.Map k v
type k :<->: v = Bimap.Bimap k v

class Circuit repr => OneCircuit repr where
    -- | @one bb = length (filter id bb) == 1@
    one  :: (Co repr var) => [repr var] -> repr var
    one  = oneDefault

class Circuit repr => AssertCircuit repr where
  assertCircuit :: repr a -> repr a -> repr a

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
  where
   none = foldr and true . map not

class Circuit repr => RPOCircuit repr term | repr -> term where
    type CoRPO_ repr term v :: Constraint
    termGt, termGe, termEq :: (--termF ~ Family.TermFM repr
                              --,var   ~ Family.VarM repr
                              --,id    ~ Family.Id1 repr
                              --,id    ~ Family.Id1 termF
                              --Foldable termF, HasId termF
--                            ,HasPrecedence v id, HasFiltering v id, HasStatus v id
                              CoRPO repr term v
                              ) =>
                              term -> term -> repr v
--    termGe s t | pprTrace (text "termGe" <+> pPrint s <+> pPrint t) False = undefined
    termGe s t = termGt s t `or` termEq s t

type CoRPO repr term v = (Co repr v, CoRPO_ repr term v)

class RPOCircuit repr term => RPOExtCircuit repr term where
    exGt, exGe, exEq :: (--termF ~ Family.TermFM repr
                        --,var   ~ Family.VarM repr
                        -- id    ~ Family.Id1 repr
                         HasPrecedence v (Family.Id term), HasFiltering v (Family.Id term), HasStatus v (Family.Id term)
                        ,CoRPO repr term v) =>
                        Family.Id term -> Family.Id term -> [term] -> [term] -> repr v
    exGe id_s id_t ss tt = exGt id_s id_t ss tt `or` exEq id_s id_t ss tt

class HasPrecedence v a | a -> v where precedence_v  :: a -> v
class HasFiltering  v a | a -> v where listAF_v      :: a -> v
                                       filtering_vv  :: a -> [v]
class HasStatus v id | id -> v   where useMul_v      :: id -> v
                                       lexPerm_vv    :: id -> Maybe [[v]]

precedence :: (NatCircuit repr, HasPrecedence v id, Co repr v) => id -> repr v
precedence = nat . precedence_v
listAF :: (Circuit repr, HasFiltering v id, Co repr v) => id -> repr v
listAF     = input . listAF_v
{- INLINE inAF -}
inAF   :: (Circuit repr, HasFiltering v id, Co repr v) => Int -> id -> repr v
inAF i     = input . (!! pred i) . filtering_vv
useMul :: (Circuit repr, HasStatus v id, Co repr v) => id -> repr v
useMul     = input . useMul_v
lexPerm :: (Circuit repr, HasStatus v id, Co repr v) => id -> Maybe [[repr v]]
lexPerm    = (fmap.fmap.fmap) input . lexPerm_vv

termGt_, termEq_, termGe_ ::
        (HasId termf, Foldable termf
        ,HasStatus var id, HasPrecedence var id, HasFiltering var id
        ,ECircuit repr, NatCircuit repr
        ,RPOExtCircuit repr (Term termf tvar)
        ,CoRPO repr (Term termf tvar) var
        ,Eq(Term termf tvar)
        ,Eq tvar
        ,id ~ Id1 termf
        ) =>
        Term termf tvar -> Term termf tvar -> repr var

termGt_ s t
--    | pprTrace (text "termGt_" <+> pPrint s <+> pPrint t) False = undefined
    | s == t = false

    | Just id_t <- rootSymbol t
    , Just id_s <- rootSymbol s
    = cond1 id_s id_t tt_s tt_t `or` cond2 id_s tt_s

    | Just id_s <- rootSymbol s
    = cond2 id_s tt_s

    | otherwise = false
   where
    tt_s = directSubterms s
    tt_t = directSubterms t

    cond1 id_s id_t tt_s tt_t
      = all (\(t_j, j) -> inAF j id_t --> (s > t_j))
            (zip tt_t [1..])
        `and`
        (listAF id_t --> and (listAF id_s)
                             (or (precedence id_s `gt` precedence id_t)
                                 (and (precedence id_s `eq` precedence id_t)
                                      (exGt id_s id_t tt_s tt_t))))

    cond2 id_s tt_s
      = any (\(s_i,i) -> inAF i id_s `and`
                         ((s_i > t) `or` (listAF id_s `and` (s_i ~~ t))))
            (zip tt_s [1..])

    all f = andL . map f
    any f = orL  . map f

    infixr 8 >
    infixr 8 ~~
    infixr 7 -->

    s > t   = termGt s t
    s ~~ t  = termEq s t
    a --> b = onlyif a b

termGe_ (Pure s) (Pure t) = if s == t then true else false
termGe_ s t
--   | pprTrace (text "termGe_" <+> pPrint s <+> pPrint t) False = undefined
   | s == t  = true
   | isVar s = not(listAF id_t) `and`
               all (\(t_j,j) -> inAF j id_t --> s ~~ t_j)
                   (zip tt [1..])

   | Just id_s <- rootSymbol s
   , isVar t = ite (listAF id_s)
                   (any (\(s_i,i) -> inAF i id_s /\  s_i >~ t) (zip ss [1..]))
                   (all (\(s_i,i) -> inAF i id_s --> s_i >~ t) (zip ss [1..]))

   | id_s == id_t
   = ite (listAF id_s)
         (exGe id_s id_t ss tt)
         (all (\(s_i,t_i,i) -> inAF i id_s --> s_i >~ t_i) (zip3 ss tt [1..]))

   | otherwise
   = ite (listAF id_s)
         (ite (listAF id_t)
              ((precedence id_s `eq` precedence id_t) `and` exGe id_s id_t ss tt)
              (all (\(t_j,j) -> inAF j id_t --> s >~ t_j) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i >~ t) (zip ss [1..]))
  where
    ss = directSubterms s
    tt = directSubterms t
    ~(Just id_s) = rootSymbol s
    ~(Just id_t) = rootSymbol t

    all f = andL . map f
    any f = orL  . map f

    infixr 8 /\, >~, ~~
    infixr 7 -->

    s >~ t  = termGe s t
    s ~~ t  = termEq s t
    a /\  b = a `and` b
    a --> b = onlyif a b

termEq_ (Pure s) (Pure t) = if s == t then true else false
termEq_ s t
--   | pprTrace (text "termEq_" <+> pPrint s <+> pPrint t) False = undefined
   | s == t  = true
   | isVar s = not(listAF id_t) `and`
               all (\(t_j,j) -> inAF j id_t --> s ~~ t_j)
                   (zip tt [1..])
   | isVar t = not(listAF id_s) `and`
               all (\(s_i,i) -> inAF i id_s --> s_i ~~ t)
                   (zip ss [1..])

   | id_s == id_t
   = ite (listAF id_s)
         (exEq id_s id_t ss tt)
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   | otherwise
   = ite (listAF id_s)
         (ite (listAF id_t)
              ((precedence id_s `and` listAF id_t) --> exEq id_s id_t ss tt)
              (all (\(t_j,j) -> inAF j id_t --> s ~~ t_j) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   where
    ss = directSubterms s
    tt = directSubterms t
    ~(Just id_s) = rootSymbol s
    ~(Just id_t) = rootSymbol t

    all f = andL . map f

    infixr 8 ~~
    infixr 7 -->

    s ~~ t  = termEq s t
    a --> b = onlyif a b


-- instance (CastCircuit Circuit.Tree c
--          ,tvar ~ Family.VarM c
--          ,tid  ~ Family.Id1 c
--          ,HasPrecedence v tid, HasFiltering v tid, HasStatus v tid
--          ,Ord v, Hashable v, Show v
--          ,Hashable tid, Ord tid
--          ,Hashable tvar, Ord tvar, Show tvar, Pretty tvar)
--          ) => CastCircuit Circuit.Tree c
--     where
--       castCircuit = castCircuit

-- instance (CastCircuit ECircuit.Tree c
--          ,tid  ~ Family.Id1 c
--          ,tvar ~ Family.VarM c
--          ,HasPrecedence v tid, HasFiltering v tid, HasStatus v tid
--          ,Ord v, Hashable v, Show v
--          ,Hashable tid, Ord tid
--          ,Hashable tvar, Ord tvar, Show tvar, Pretty tvar)
--          ) => CastRPOCircuit ECircuit.Tree c
--      where
--        castRPOCircuit = castCircuit

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared term v = Shared { unShared :: Lazy.State (CMaps term v) CCode }

type instance Family.Id1    (Shared term) = Family.Id term
type instance Family.TermFM (Shared term) = Family.TermF term
type instance Family.VarM   (Shared term) = Family.Var term

-- | A shared circuit that has already been constructed.
data FrozenShared term v = FrozenShared !CCode !(CMaps term v) deriving Eq

frozenShared code maps = FrozenShared code maps


instance (Hashable term, Show term, Show v) => Show (FrozenShared term v) where
  showsPrec p (FrozenShared c maps) = ("FrozenShared " ++) . showsPrec p c . showsPrec p maps{hashCount=[]}


-- | Reify a sharing circuit.
runShared :: (Hashable term, Ord term) => Shared term v -> FrozenShared term v
runShared = runShared' emptyCMaps

runShared' :: (Hashable term, Ord term) => CMaps term v -> Shared term v -> FrozenShared term v
runShared' _ = uncurry frozenShared . (`Lazy.runState` emptyCMaps) . unShared

getChildren :: (Ord v, Hashable v) => CCode -> CircuitHash :<->: v -> v
getChildren code codeMap =
    case Bimap.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

getChildren' :: (Ord v) => CCode -> Bimap CircuitHash v -> v
getChildren' code codeMap =
    case Bimap.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

instance (Hashable term, Ord term, ECircuit c, NatCircuit c, ExistCircuit c) => CastCircuit (Shared term) c where
    type CastCo (Shared term) c var = Co c var
    castCircuit = castCircuit . runShared

instance (ECircuit c, NatCircuit c, ExistCircuit c) => CastCircuit (FrozenShared term) c where
    type CastCo (FrozenShared term) c var = Co c var
    castCircuit (FrozenShared code maps) = runCont (go code) id
      where
        go (CTrue{})     = return true
        go (CFalse{})    = return false
        go (CExistBool _)= cont existsBool
        go (CExistNat  _)= cont existsNat
        go c@(CVar{})    = return $ input $ getChildren' c (varMap maps)
        go c@(CAnd{})    = liftM(uncurry and)     . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = liftM(uncurry or)      . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = liftM not              . go  $ getChildren c (notMap maps)
        go c@(CXor{})    = liftM (uncurry xor)    . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = liftM (uncurry onlyif) . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = liftM (uncurry iff)    . go2 $ getChildren c (iffMap maps)
        go c@(CIte{})    = liftM (uncurry3 ite)   . go3 $ getChildren c (iteMap maps)
        go c@CEq{}       = liftM (uncurry eq)     . go2 $ getChildren c (eqMap maps)
        go c@CLt{}       = liftM (uncurry lt)     . go2 $ getChildren c (ltMap maps)
        go c@CNat{}      = return $ nat $ getChildren' c (natMap maps)
        go c@COne{}      = liftM oneDefault $ mapM go $ getChildren c (oneMap maps)

        go2 (a,b)   = do {a' <- go a; b' <- go b; return (a',b')}
        go3 (a,b,c) = do {a' <- go a; b' <- go b; c' <- go c; return (a',b',c')}
        uncurry3 f (x, y, z) = f x y z

--instance (Hashable id, Ord id, ECircuit c, NatCircuit c, ExistCircuit c, Family.TermF c ~ t) => CastRPOCircuit (Shared id var) c where
--    castRPOCircuit = castCircuit

--instance (ECircuit c, NatCircuit c, ExistCircuit c) => CastRPOCircuit (FrozenShared id var) c id var where
--    castRPOCircuit = castCircuit

data CCode    = CTrue   { circuitHash :: !CircuitHash }
              | CFalse  { circuitHash :: !CircuitHash }
              | CVar    { circuitHash :: !CircuitHash }
              | CAnd    { circuitHash :: !CircuitHash }
              | COr     { circuitHash :: !CircuitHash }
              | CNot    { circuitHash :: !CircuitHash }
              | CXor    { circuitHash :: !CircuitHash }
              | COnlyif { circuitHash :: !CircuitHash }
              | CIff    { circuitHash :: !CircuitHash }
              | CIte    { circuitHash :: !CircuitHash }
              | CNat    { circuitHash :: !CircuitHash }
              | CEq     { circuitHash :: !CircuitHash }
              | CLt     { circuitHash :: !CircuitHash }
              | COne    { circuitHash :: !CircuitHash }
              | CExistBool  { circuitHash :: !CircuitHash }
              | CExistNat   { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

instance Hashable CCode where hash = circuitHash

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `Shared'.
data CMaps term v = CMaps
    { hashCount :: ![CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: !(CircuitHash :<->: v)
     -- ^ Mapping of generated integer IDs to variables.
    , freshSet  :: !(Set CircuitHash)
    , andMap    :: !(CircuitHash :<->: (CCode, CCode))
    , orMap     :: !(CircuitHash :<->: (CCode, CCode))
    , notMap    :: !(CircuitHash :<->: CCode)
    , xorMap    :: !(CircuitHash :<->: (CCode, CCode))
    , onlyifMap :: !(CircuitHash :<->: (CCode, CCode))
    , iffMap    :: !(CircuitHash :<->: (CCode, CCode))
    , iteMap    :: !(CircuitHash :<->: (CCode, CCode, CCode))
    , natMap    :: !(CircuitHash :<->: v)
    , eqMap     :: !(CircuitHash :<->: (CCode, CCode))
    , ltMap     :: !(CircuitHash :<->: (CCode, CCode))
    , oneMap    :: !(CircuitHash :<->: [CCode])
    , termGtMap :: !((term,term) :->: CCode)
    , termGeMap :: !((term,term) :->: CCode)
    , termEqMap :: !((term,term) :->: CCode)
    }

deriving instance (Hashable term, Show term, Show v) => Show (CMaps term v)
deriving instance (Hashable term, Eq term, Eq v) => Eq (CMaps term v)

validCMaps :: forall term v . Ord v => CMaps term v -> Bool
validCMaps cmaps =
    Prelude.and
        [ validBimap2 andMap
        , validBimap2 orMap
        , validBimap1 notMap
        , validBimap2 xorMap
        , validBimap2 onlyifMap
        , validBimap2 iffMap
        , validBimap3 iteMap
        , validBimap2 eqMap
        , validBimap2 ltMap
        , validBimapList oneMap
        ]
    where
      exists :: (Ord a, Ord k) => k -> (CMaps term v -> k :<->: a) -> Bool
      exists h m = Bimap.member h (m cmaps)
      valid (CTrue _)  = True
      valid (CFalse _) = True
      valid (CVar h)   = exists h varMap
      valid (CAnd h)   = exists h andMap
      valid (COr  h)   = exists h orMap
      valid (CNot h)   = exists h notMap
      valid (CXor h)   = exists h xorMap
      valid (COnlyif h)= exists h onlyifMap
      valid (CIff h)   = exists h iffMap
      valid (CIte h)   = exists h iteMap
      valid (CNat h)   = exists h natMap
      valid (CEq  h)   = exists h eqMap
      valid (CLt  h)   = exists h ltMap
      valid (COne h)   = exists h oneMap
      valid (CExistBool _) = True
      valid (CExistNat _) = True

      bimapKeysPred :: forall k a . (a -> Bool) -> (CMaps term v -> k :<->: a) -> Bool
      bimapKeysPred p = all p . Bimap.keysR . ($ cmaps)
      validBimap1    = bimapKeysPred valid
      validBimap2    = bimapKeysPred (\(h1,h2) -> valid h1 && valid h2)
      validBimap3    = bimapKeysPred (\(h1,h2,h3) -> valid h1 && valid h2 && valid h3)
      validBimapList = bimapKeysPred (all valid)

-- | A `CMaps' with an initial `hashCount' of 2.
emptyCMaps :: (Hashable term, Ord term) => CMaps term v
emptyCMaps = CMaps
    { hashCount = [2 ..]
    , varMap    = Bimap.empty
    , freshSet  = Set.empty
    , andMap    = Bimap.empty
    , orMap     = Bimap.empty
    , notMap    = Bimap.empty
    , xorMap    = Bimap.empty
    , onlyifMap = Bimap.empty
    , iffMap    = Bimap.empty
    , iteMap    = Bimap.empty
    , natMap    = Bimap.empty
    , eqMap     = Bimap.empty
    , ltMap     = Bimap.empty
    , oneMap    = Bimap.empty
    , termGtMap = mempty
    , termGeMap = mempty
    , termEqMap = mempty
    }

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
{-# INLINE recordC #-}
recordC :: (Ord a, Hashable a) =>
           (CircuitHash -> b)
        -> (CMaps term v -> Int :<->: a)                 -- ^ prj
        -> (CMaps term v -> Int :<->: a -> CMaps term v) -- ^ upd
        -> a
        -> Lazy.State (CMaps term v) b
recordC _ _ _ x | x `seq` False = undefined
recordC cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (Bimap.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ Bimap.lookupR x (prj s)

{-# INLINE recordC' #-}
recordC' :: Ord a =>
           (CircuitHash -> b)
        -> (CMaps term v -> Bimap Int a)                 -- ^ prj
        -> (CMaps term v -> Bimap Int a -> CMaps term v) -- ^ upd
        -> a
        -> Lazy.State (CMaps term v) b
recordC' _ _ _ x | x `seq` False = undefined
recordC' cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (Bimap.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ Bimap.lookupR x (prj s)


instance Circuit (Shared term) where
    type Co (Shared term) var = Ord var
    false = Shared falseS
    true  = Shared trueS
    input v = Shared $ recordC' CVar varMap (\s e -> s{ varMap = e }) v
    and = liftShared2 and_ where
        and_ c@CFalse{} _ = return c
        and_ _ c@CFalse{} = return c
        and_ CTrue{} c  = return c
        and_ c CTrue{}  = return c
        and_ hl hr = recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)

    or = liftShared2 or_ where
        or_ c@CTrue{} _ = return c
        or_ _ c@CTrue{} = return c
        or_ CFalse{} c  = return c
        or_ c CFalse{}  = return c
        or_ hl hr = recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not = liftShared notS


instance ExistCircuit (Shared term) where
    existsBool k  = Shared $ do
        c:cs <- gets hashCount
        modify $ \s -> s{freshSet = Set.insert c (freshSet s), hashCount=cs}
        unShared . k . Shared . return . CExistBool $ c
    existsNat k  = Shared $ do
        c:cs <- gets hashCount
        modify $ \s -> s{freshSet = Set.insert c (freshSet s), hashCount=cs}
        unShared . k . Shared . return . CExistNat $ c

instance ECircuit (Shared term) where
    xor = liftShared2 xor_ where
        xor_ CTrue{} c = notS c
        xor_ c CTrue{} = notS c
        xor_ CFalse{} c = return c
        xor_ c CFalse{} = return c
        xor_ hl hr = recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
    iff = liftShared2 iffS
    onlyif = liftShared2 onlyif_ where
        onlyif_ CFalse{} _ = trueS
        onlyif_ c CFalse{} = notS c
        onlyif_ CTrue{}  c = return c
        onlyif_ _ CTrue{}  = trueS
        onlyif_ hl hr
           | hl == hr  = trueS
           | otherwise = recordC COnlyif onlyifMap (\s e' -> s{ onlyifMap = e' }) (hl, hr)
    ite x t e = Shared $ do
        hx <- unShared x
        ht <- unShared t ; he <- unShared e
        ite_ hx ht he
      where
        ite_ CTrue{} ht _  = return ht
        ite_ CFalse{} _ he = return he
        ite_ hx ht he = recordC CIte iteMap (\s e' -> s{ iteMap = e' }) (hx, ht, he)

falseS, trueS :: Lazy.State (CMaps term v) CCode
falseS = return $ CFalse falseHash
trueS  = return $ CTrue trueHash

notS CTrue{}  = falseS
notS CFalse{} = trueS
notS (CNot i) = do {s <- get; return $ fromJust $ Bimap.lookup i (notMap s) }
notS h        = recordC CNot notMap (\s e' -> s{ notMap = e' }) h

iffS CTrue{} c  = return c
iffS c CTrue{}  = return c
iffS CFalse{} c = notS c
iffS c CFalse{} = notS c
iffS hl hr
 | hl == hr  = trueS
 | otherwise = recordC CIff iffMap (\s e' -> s{ iffMap = e' }) (hl, hr)

{-# INLINE liftShared #-}
liftShared f a = Shared $ do {h <- unShared a; f h}
{-# INLINE liftShared2 #-}
liftShared2 f a b = Shared $ do
  va <- unShared a
  vb <- unShared b
  f va vb

instance OneCircuit (Shared term) where
    one ss = Shared $ do
               xx <- sequence $ map unShared ss
               if null xx then falseS else recordC COne oneMap (\s e' -> s{oneMap = e'}) xx

instance NatCircuit (Shared term) where
    eq xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then trueS else recordC CEq eqMap (\s e -> s {eqMap = e}) (x,y)

    lt xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 if x == y then falseS else recordC CLt ltMap (\s e -> s {ltMap = e}) (x,y)

    nat = Shared . recordC' CNat natMap (\s e -> s{ natMap = e })

instance ( RPOExtCircuit (Shared (Term termF var)) (Term termF var)
         ) => RPOCircuit (Shared (Term termF var)) (Term termF var) where
 type CoRPO_ (Shared (Term termF var)) (Term termF var) v =
     (Eq var, Ord var
     ,HasId termF, Foldable termF
     ,Eq(Term termF var), Ord (Term termF var), Hashable(Term termF var)
     ,HasStatus v (Id1 termF), HasFiltering v (Id1 termF), HasPrecedence v (Id1 termF)
     )

 termGt s t = Shared $ do
      env <- get
      case HashMap.lookup (s,t) (termGtMap env) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termGt_ s t
           modify $ \env -> env{termGtMap = HashMap.insert (s,t) me (termGtMap env)}
           return me
 termEq s t = Shared $ do
      env <- get
      case (HashMap.lookup (s,t) (termEqMap env)) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termEq_ s t
           modify $ \env -> env{termEqMap = HashMap.insert (s,t) me (termEqMap env)}
           return me
 termGe s t = Shared $ do
      env <- get
      case (HashMap.lookup (s,t) (termGeMap env)) of
         Just v  -> return v
         Nothing -> do
           me <- unShared $ termGe_ s t
           modify $ \env -> env{termGeMap = HashMap.insert (s,t) me (termGeMap env)}
           return me

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.

data TreeF term (a :: *)
               = TTrue
               | TFalse
               | TNot a
               | TAnd a a
               | TOr  a a
               | TXor a a
               | TIff a a
               | TOnlyIf a a
               | TIte a a a
               | TEq  a a
               | TLt  a a
               | TOne [a]
               | TTermEq term term
               | TTermGt term term
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Bifunctor TreeF where bimap = bimapDefault
instance Bifoldable TreeF where bifoldMap = bifoldMapDefault
instance Bitraversable TreeF where
  bitraverse _ _ TTrue = pure TTrue
  bitraverse _ _ TFalse = pure TFalse
  bitraverse _ g (TNot t) = TNot <$> g t
  bitraverse _ g (TAnd t u) = TAnd <$> g t <*> g u
  bitraverse _ g (TOr  t u) = TOr  <$> g t <*> g u
  bitraverse _ g (TXor t u) = TXor <$> g t <*> g u
  bitraverse _ g (TIff t u) = TIff <$> g t <*> g u
  bitraverse _ g (TOnlyIf t u) = TOnlyIf <$> g t <*> g u
  bitraverse _ g (TIte i t e)  = TIte    <$> g i <*> g t <*> g e
  bitraverse _ g (TEq t u)  = TEq <$> g t <*> g u
  bitraverse _ g (TLt t u)  = TLt <$> g t <*> g u
  bitraverse _ g (TOne tt)  = TOne <$> traverse g tt
  bitraverse f _ (TTermEq t u) = TTermEq <$> f t <*> f u
  bitraverse f _ (TTermGt t u) = TTermGt <$> f t <*> f u

data Tree term v = TNat v
                 | TLeaf v
                 | TFix {tfix :: TreeF term (Tree term v)}
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Bifunctor Tree where bimap = bimapDefault
instance Bifoldable Tree where bifoldMap = bifoldMapDefault
instance Bitraversable Tree where
  bitraverse _ g (TNat v)  = TNat  <$> g v
  bitraverse _ g (TLeaf v) = TLeaf <$> g v
  bitraverse f g (TFix t)  = TFix  <$> bitraverse f (bitraverse f g) t

foldTree fnat  _ _ (TNat v)  = fnat v
foldTree _ fleaf _ (TLeaf v) = fleaf v
foldTree fn fl f (TFix t) = f (fmap (foldTree fn fl f) t)

foldTreeM :: Monad f => (v -> f res) -> (v -> f res) -> (TreeF term res -> f res) -> Tree term v -> f res
foldTreeM fnat _ _ (TNat v) = fnat v
foldTreeM _ fleaf _ (TLeaf v) = fleaf v
foldTreeM fn fl f (TFix t) = f =<< T.mapM (foldTreeM fn fl f) t

tLeaf   = TLeaf
tNat    = TNat
tTrue   = TFix TTrue
tFalse  = TFix TFalse
tNot    = TFix . TNot
tOne    = TFix . TOne
tAnd    = (TFix.) . TAnd
tOr     = (TFix.) . TOr
tXor    = (TFix.) . TXor
tIff    = (TFix.) . TIff
tOnlyIf = (TFix.) . TOnlyIf
tEq     = (TFix.) . TEq
tLt     = (TFix.) . TLt
tIte    = ((TFix.).) . TIte
tTermGt = (TFix.) . TTermGt
tTermEq = (TFix.) . TTermEq

tOpen (TFix t) = Just t
tOpen _ = Nothing

tClose = TFix

tId TTrue  = tTrue
tId TFalse = tFalse
tId (TNot n) = tNot n
tId (TOne n) = tOne n
tId (TAnd t1 t2) = tAnd t1 t2
tId (TOr  t1 t2) = tOr t1 t2
tId (TXor t1 t2) = tXor t1 t2
tId (TIff t1 t2) = tIff t1 t2
tId (TOnlyIf t1 t2) = tOnlyIf t1 t2
tId (TEq t1 t2) = tEq t1 t2
tId (TLt t1 t2) = tLt t1 t2
tId (TIte c t e) = tIte c t e
--tId (TTermGt t u) = tTermGt t u
--tId (TTermEq t u) = tTermEq t u
tId _ = error "internal error - unreachable"

mapTreeTerms :: (term -> term') -> Tree term v -> Tree term' v
mapTreeTerms f = foldTree tNat tLeaf f'
  where
   f' (TTermGt t u) = tTermGt (f t) (f u)
   f' (TTermEq t u) = tTermGt (f t) (f u)
   f' t = tId t

printTree :: (Pretty a, Pretty t) => Int -> Tree t a -> Doc
printTree p t = foldTree fn fl f t p where
  fl v _ = pPrint v
  fn v _ = pPrint v
  f TTrue  _ = text "true"
  f TFalse _ = text "false"
  f (TNot t)        p = pP p 9 $ text "!" <> t 9
  f (TAnd t1 t2)    p = pP p 5 $ text "AND" <+> (t1 5 $$ t2 5)
--   f (TAnd t1 t2) p = pP p 5 $ pt 5 t1 <+> text "&" <+> pt 5 t2
  f (TOr t1 t2)     p = pP p 5 $ text "OR " <+> (t1 5 $$ t2 5)
--   f (TOr  t1 t2) p = pP p 5 $ t1 5 <+> text "||" <+> pt 5 t2
  f (TXor t1 t2)    p = pP p 5 $ t1 5 <+> text "xor" <+> t2 5
  f (TIff t1 t2)    p = pP p 3 $ t1 3 <+> text "<->" <+> t2 3
  f (TOnlyIf t1 t2) p = pP p 3 $ t1 3 <+> text "-->" <+> t2 3
  f (TIte c t e)    p = pP p 2 $ text "IFTE" <+> (c 1 $$ t 1 $$ e 1)
  f (TEq n1 n2)     p = pP p 7 (n1 1 <+> text "==" <+> n2 1)
  f (TLt n1 n2)     p = pP p 7 (n1 1 <+> text "<"  <+> n2 1)
  f (TOne vv)       p = pP p 1 $ text "ONE" <+> (fsep $ punctuate comma $ map ($ 1) vv)
  f (TTermGt t u)   p = pP p 6 $ pPrint t <+> text ">" <+> pPrint u
  f (TTermEq t u)   p = pP p 6 $ pPrint t <+> text "=" <+> pPrint u

pP prec myPrec doc = if myPrec Prelude.> prec then doc else parens doc

collectIdsTree :: (Functor t, Foldable t, HasId t) => Tree (Term t v) a -> Set (Id1 t)
collectIdsTree = foldTree (const mempty) (const mempty) f
  where
   f (TNot t1)       = t1
   f (TAnd t1 t2)    = mappend t1 t2
   f (TOr t1 t2)     = mappend t1 t2
   f (TXor t1 t2)    = mappend t1 t2
   f (TOnlyIf t1 t2) = mappend t1 t2
   f (TIff t1 t2)    = mappend t1 t2
   f (TIte t1 t2 t3) = t1 `mappend` t2 `mappend` t3
   f (TTermGt t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f (TTermEq t1 t2) = Set.fromList (collectIds t1) `mappend` Set.fromList (collectIds t2)
   f TOne{} = mempty
   f TTrue  = mempty
   f TFalse = mempty
   f TEq{}  = mempty
   f TLt{}  = mempty

data CircuitType = Nat | Bool deriving (Eq, Show)

typeCheckTree :: Show term => Tree term v -> Maybe CircuitType
typeCheckTree = foldTreeM (const (pure Nat)) (const (pure Bool)) f where
    f TFalse = return Bool
    f TTrue  = return Bool
    f (TNot Bool) = return Bool
    f (TAnd Bool Bool) = return Bool
    f (TOr  Bool Bool) = return Bool
    f (TXor Bool Bool) = return Bool
    f (TIff Bool Bool) = return Bool
    f (TOnlyIf Bool Bool) = return Bool
    f (TIte Bool a b)
      | a==b = return a
      | otherwise    = fail "TIte"
    f (TOne vv)
      | all ((==) Bool) vv = return Bool
      | otherwise = fail "TOne"
    f TTermGt{} = return Bool
    f TTermEq{} = return Bool
    f (TEq Nat Nat) = return Bool
    f (TLt Nat Nat) = return Bool
    f other = fail (show other)


-- | Performs obvious constant propagations.
simplifyTree :: (Eq a, Eq term) => Tree term a -> Tree term a
simplifyTree = foldTree TNat TLeaf f where
  f TFalse      = tFalse
  f TTrue       = tTrue

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

  f t@(TEq x y) = if x == y then tTrue  else tClose t
  f t@(TLt x y) = if x == y then tFalse else tClose t
  f (TOne [])   = tFalse
  f t@TOne{}    = tClose t
  f (TTermEq s t) | s == t = tTrue
  f t@TTermEq{} = tClose t
  f (TTermGt s t) | s == t = tFalse
  f t@TTermGt{} = tClose t


instance (ECircuit c, NatCircuit c, OneCircuit c, RPOCircuit c term
         ) =>
  CastCircuit (Tree term) c
 where
  type CastCo (Tree term) c v = CoRPO c term v
  castCircuit (TFix TTrue) = true
  castCircuit (TFix TFalse) = false
  castCircuit (TFix (TAnd t1 t2)) = and (castCircuit t1) (castCircuit t2)
  castCircuit (TLeaf v) = input v
  castCircuit (TFix (TOr t1 t2)) = or (castCircuit t1) (castCircuit t2)
  castCircuit (TFix (TXor t1 t2)) = xor (castCircuit t1) (castCircuit t2)
  castCircuit (TFix (TNot t)) = not (castCircuit t)
  castCircuit (TNat n) = nat n
  castCircuit (TFix(TIte i t e)) = ite (castCircuit i) (castCircuit t) (castCircuit e)
  castCircuit (TFix(TIff t1 t2)) = iff (castCircuit t1) (castCircuit t2)
  castCircuit (TFix(TOnlyIf t1 t2)) = onlyif (castCircuit t1) (castCircuit t2)
  castCircuit (TFix(TEq s t)) = eq (castCircuit s) (castCircuit t)
  castCircuit (TFix(TLt s t)) = lt (castCircuit s) (castCircuit t)
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

instance Circuit (Tree term) where
    type Co (Tree term) v = ()
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
    eq    = tEq
    lt    = tLt
    nat   = TNat

instance OneCircuit (Tree term) where
    one   = tOne

instance RPOCircuit (Tree term) term where
    type CoRPO_ (Tree term) term v = ()
    termGt = tTermGt
    termEq = tTermEq

--    ------------------
-- ** Circuit evaluator
--    ------------------

instance OneCircuit Eval where
  one tt    = Eval (\env -> Right $ case filter id $  map (fromRight . (`unEval` env)) tt of
                                        (_:[]) -> True
                                        _      -> False)

instance RPOCircuit Eval (Term termF var) where
  type CoRPO_ Eval (Term termF var) v =
      ( Hashable v
      , Eq (Term termF var)
      , Foldable termF, HasId termF
      , HasStatus v (Id1 termF), HasFiltering v (Id1 termF), HasPrecedence v (Id1 termF)
      , Pretty (Id1 termF), Show (Id1 termF)
      )

  termGt t u = unFlip (Right `liftM` (>) evalRPO t u)
  termEq t u = unFlip (Right `liftM` (~~) evalRPO t u)

newtype WrapEval term v = WrapEval { unwrap :: Eval v}
wrap1 f = WrapEval . f . unwrap
wrap2 f x y = WrapEval $ f (unwrap x) (unwrap y)
wrap3 f x y z = WrapEval $ f (unwrap x) (unwrap y) (unwrap z)
wrapL f = WrapEval . f . map unwrap

instance Circuit (WrapEval term) where
   type Co (WrapEval term) v = Co Eval v
   true  = WrapEval true
   false = WrapEval false
   input = WrapEval . input
   not   = wrap1 not
   andL  = wrapL andL
   orL   = wrapL orL
   and   = wrap2 and
   or    = wrap2 or

instance NatCircuit (WrapEval term) where
   nat = WrapEval . nat
   eq  = wrap2 eq
   lt  = wrap2 lt
   gt  = wrap2 gt

instance ECircuit (WrapEval term) where
   ite = wrap3 ite
   iff = wrap2 iff
   onlyif = wrap2 onlyif
   xor = wrap2 xor

instance RPOCircuit (WrapEval (Term termF var)) (Term termF var) where
   type CoRPO_ (WrapEval (Term termF var)) (Term termF var) v =
       ( Eq var
       , Eq (Term termF var)
       , Foldable termF, HasId termF
       , HasStatus v (Id1 termF), HasFiltering v (Id1 termF), HasPrecedence v (Id1 termF)
       , Pretty (Id1 termF), Show (Id1 termF)
       , Hashable v
       )
   termGt t u = WrapEval $ unFlip (Right `liftM` (>)  evalRPO t u)
   termEq t u = WrapEval $ unFlip (Right `liftM` (~~) evalRPO t u)


data RPOEval a v = RPO {(>), (>~), (~~) :: a -> a -> Flip EvalF v Bool}

evalRPO :: forall termF id v var.
           (HasPrecedence v id, HasStatus v id, HasFiltering v id
           ,Ord v, Hashable v, Show v
           ,Pretty id, Show id
           ,Eq(Term termF var)
           ,Foldable termF, HasId termF
           ,id ~ Id1 termF
           ) => RPOEval (Term termF var) v
evalRPO = RPO{..} where

  infixr 4 >
  infixr 4 >~
  infixr 4 ~~

  s >~ t = s > t <|> s ~~ t

  s ~~ t
   | s == t = return True

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t
   , id_s == id_t
   = do
     af_s <- compFiltering id_s
     case af_s of
      Left i -> (tt_s !! pred i) ~~ t
      _      -> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , Just id_t <- rootSymbol t, tt_t <- directSubterms t
   = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s,af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:928" tt_s (pred i) ~~ t
      (_, Left j) -> s ~~ safeAtL "RPOCircuit:929" tt_t (pred j)
      (_,_) -> evalB (precedence id_s `eq` precedence id_t) <&> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
      Left i-> safeAtL "RPOCircuit:935" tt_s (pred i) ~~ t
      _     -> return False

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t = do
     af_t <- compFiltering id_t
     case af_t of
      Left j -> s ~~ safeAtL "RPOCircuit:941" tt_t (pred j)
      _      -> return False

   | otherwise = return False

  s > t

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s
   , id_s == id_t
   = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s, af_t) of
      (Left i, _) -> safeAtL "RPOCircuit:955" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "RPOCircuit:956" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> exgt s t)
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s, af_t) of
      (Left i, Left j) -> safeAtL "RPOCircuit:698" tt_s (pred i) > safeAtL "RPOCircuit:698" tt_t (pred j)
      (Left i, _) -> safeAtL "RPOCircuit:698" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "RPOCircuit:699" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> (evalB (precedence id_s `gt` precedence id_t)
                                                                   <|>
                                                              (evalB (precedence id_s `eq` precedence id_t) <&>
                                                               exgt s t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
       Left  i  -> safeAtL "RPOCircuit:709" tt_s (pred i) > t
       Right ii -> anyM (>~ t) (sel 5 ii tt_s)

   | otherwise = return False

  exgt, exeq :: Term termF var -> Term termF var -> Flip EvalF v Bool
  exgt s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- compFiltering id_s
        af_t <- compFiltering id_t
        let ss' = applyFiltering af_s ss
            tt' = applyFiltering af_t tt
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> mulD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexD (maybe ss' (permute ss) ps)
                 (maybe tt' (permute tt) pt)
          _ -> error "exgt: Cannot compare two symbols with incompatible statuses"
   | otherwise = error "internal error"

  exeq s t
   | Just id_t <- rootSymbol t, tt <- directSubterms t
   , Just id_s <- rootSymbol s, ss <- directSubterms s = do
        af_s <- compFiltering id_s
        af_t <- compFiltering id_t
        let ss' = applyFiltering af_s ss
            tt' = applyFiltering af_t tt
        mul_s <- evalB (useMul id_s)
        mul_t <- evalB (useMul id_t)
        case (mul_s, mul_t) of
          (True,  True)  -> muleqD ss' tt'
          (False, False) -> do
            ps <- evalPerm id_s
            pt <- evalPerm id_t
            lexeqD (maybe ss' (permute ss) ps)
                   (maybe tt' (permute tt) pt)
          _ -> error "exeq:Cannot compare two symbols with incompatible statuses"
   | otherwise = error "internal error"

  lexD []     _      = return False
  lexD _      []     = return True
  lexD (f:ff) (g:gg) = (f > g) <|> (f ~~ g <&> lexD ff gg)

  lexeqD []     []     = return True
  lexeqD _      []     = return False
  lexeqD []     _      = return False
  lexeqD (f:ff) (g:gg) = (f ~~ g <&> lexeqD ff gg)

  mulD m1 m2 = do
    m1' <- differenceByM (~~) m1 m2
    m2' <- differenceByM (~~) m2 m1
    forall m2' $ \y-> exists m1' (> y)

  muleqD [] []     = return True
  muleqD (m:m1) m2 = acmatchM (~~m) m2 >>= \it -> case it of
                                                   Just (_,m2) -> muleqD m1 m2
                                                   _           -> return False
  muleqD _ _       = return False

  differenceByM p = foldM rem1 where
    rem1 []     _ = return []
    rem1 (x:xx) y = p x y >>= \b -> if b then return xx else rem1 xx y

  acmatchM p = go [] where
    go _ [] = return Nothing
    go acc (x:xs) = p x >>= \b -> if b then return $ Just (x, reverse acc ++ xs)
                                       else go (x:acc) xs

  infixr 3 <&>
  infixr 2 <|>

  (<|>) = liftM2 (||)
  (<&>) = liftM2 (&&)

  forall = flip allM
  exists = flip anyM
  allM  f xx = Prelude.and `liftM` mapM f xx
  anyM  f xx = Prelude.or  `liftM` mapM f xx

  sel :: Int -> [Int] -> [a] -> [a]
  sel n ii = selectSafe ("Narradar.Constraints.SAT.RPOCircuit.Eval - " ++ show n) (map pred ii)
  permute ff ii = map fst $ dropWhile ( (<0) . snd) $ sortBy (compare `on` snd) (zip ff ii)
  on cmp f x y = f x `cmp` f y

--  evalPerm :: HasStatus id v => id -> EvalM v (Maybe [Int])
  evalPerm id = do
    bits <- (T.mapM . mapM . mapM) evalB (lexPerm id)
    let perm = (fmap.fmap)
                 (\perm_i -> head ([i | (i,True) <- zip [(1::Int)..] perm_i] ++ [-1]))
                 bits
    return perm

  compFiltering id = do
    isList:filtering <- mapM (evalB.input) (listAF_v id : filtering_vv id)
    let positions = [ i | (i, True) <- zip [1..] filtering ]
    return $ if isList then Right positions
             else assert'
                      ("there should be one filtered positions for " ++ (show$ pPrint id) ++
                       ", instead they are " ++ show positions ++ ".\n" ++ show id)
                      (length positions == 1)
                      (Left (head positions))


  applyFiltering (Right ii) tt = selectSafe "RPOCircuit.verifyRPOAF.applyFiltering" (map pred ii) tt
  applyFiltering (Left j)   tt = [safeAtL   "RPOCircuit.verifyRPOAF.applyFiltering" tt (pred j)]


-- ** Graph circuit

-- | A circuit type that constructs a `G.Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype Graph term v = Graph
    { unGraph :: State Graph.Node (Graph.Node,
                                    [Graph.LNode (NodeType v)],
                                    [Graph.LEdge EdgeType]) }

-- | Node type labels for graphs.
data NodeType v = NInput v
                | NTrue
                | NFalse
                | NAnd
                | NOr
                | NNot
                | NXor
                | NIff
                | NOnlyIf
                | NIte
                | NNat v
                | NEq
                | NLt
                | NOne
                | NTermGt String String
                | NTermEq String String
                  deriving (Eq, Ord, Show, Read)

data EdgeType = ETest -- ^ the edge is the condition for an `ite' element
              | EThen -- ^ the edge is the /then/ branch for an `ite' element
              | EElse -- ^ the edge is the /else/ branch for an `ite' element
              | EVoid -- ^ no special annotation
              | ELeft
              | ERight
                 deriving (Eq, Ord, Show, Read)

runGraph :: (G.DynGraph gr) => Graph term v -> gr (NodeType v) EdgeType
runGraph graphBuilder =
    let (_, nodes, edges) = evalState (unGraph graphBuilder) 1
    in Graph.mkGraph nodes edges

--binaryNode :: NodeType v -> Graph v -> Graph v -> Graph v
{-# INLINE binaryNode #-}
binaryNode ty ledge redge l r = Graph $ do
        (lNode, lNodes, lEdges) <- unGraph l
        (rNode, rNodes, rEdges) <- unGraph r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, ledge) : (rNode, n, redge) : lEdges ++ rEdges)

newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i

instance Circuit (Graph term) where
    type Co (Graph term) v = ()
    input v = Graph $ do
        n <- newNode
        return $ (n, [(n, NInput v)], [])

    true = Graph $ do
        n <- newNode
        return $ (n, [(n, NTrue)], [])

    false = Graph $ do
        n <- newNode
        return $ (n, [(n, NFalse)], [])

    not gs = Graph $ do
        (node, nodes, edges) <- unGraph gs
        n <- newNode
        return (n, (n, NNot) : nodes, (node, n, EVoid) : edges)

    and    = binaryNode NAnd EVoid EVoid
    or     = binaryNode NOr EVoid EVoid

instance ECircuit (Graph term) where
    xor    = binaryNode NXor EVoid EVoid
    iff    = binaryNode NIff EVoid EVoid
    onlyif = binaryNode NOnlyIf ELeft ERight
    ite x t e = Graph $ do
        (xNode, xNodes, xEdges) <- unGraph x
        (tNode, tNodes, tEdges) <- unGraph t
        (eNode, eNodes, eEdges) <- unGraph e
        n <- newNode
        return (n, (n, NIte) : xNodes ++ tNodes ++ eNodes
                 , (xNode, n, ETest) : (tNode, n, EThen) : (eNode, n, EElse)
                 : xEdges ++ tEdges ++ eEdges)

instance NatCircuit (Graph term) where
    eq     = binaryNode NEq EVoid EVoid
    lt     = binaryNode NLt ELeft ERight
    nat x  = Graph $ do {n <- newNode; return (n, [(n, NNat x)],[])}

instance OneCircuit (Graph term) where
    one tt = Graph$ do
      (tips, nodes, edges) <- unzip3 `liftM` mapM unGraph tt
      me <- newNode
      let nodes' = (me, NOne) : concat nodes
          edges' = [(n, me, EVoid) | n <- tips ] ++ concat edges
      return (me, nodes', edges')

instance Pretty term => RPOCircuit (Graph term) term where
    type CoRPO_ (Graph term) term v = ()
    termGt t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermGt (show$ pPrint t) (show$ pPrint u))
                   return (n, [me], [])
    termEq t u = Graph $ do
                   n <- newNode
                   let me = (n, NTermEq (show$ pPrint t) (show$ pPrint u))
                   return (n, [me], [])


{-
defaultNodeAnnotate :: (Show v) => LNode (FrozenShared v) -> [GraphViz.Attribute]
defaultNodeAnnotate (_, FrozenShared (output, cmaps)) = go output
  where
    go CTrue{}       = "true"
    go CFalse{}      = "false"
    go (CVar _ i)    = show $ extract i varMap
    go (CNot{})      = "NOT"
    go (CAnd{hlc=h}) = maybe "AND" goHLC h
    go (COr{hlc=h})  = maybe "OR" goHLC h

    goHLC (Xor{})    = "XOR"
    goHLC (Onlyif{}) = go (output{ hlc=Nothing })
    goHLC (Iff{})    = "IFF"

    extract code f =
        IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
        code
        (f cmaps)

defaultEdgeAnnotate = undefined

dotGraph :: (Graph gr) => gr (FrozenShared v) (FrozenShared v) -> DotGraph
dotGraph g = graphToDot g defaultNodeAnnotate defaultEdgeAnnotate
-}


-- | Given a frozen shared circuit, construct a `G.DynGraph' that exactly
-- represents it.  Useful for debugging constraints generated as `Shared'
-- circuits.
shareGraph :: ( G.DynGraph gr
              , Eq v, Hashable v, Show v
              , Eq term, Hashable term
              ) =>
              FrozenShared term v -> gr (FrozenShared term v) (FrozenShared term v)
shareGraph (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(COne i) = extract i oneMap >>= mapM go >>= addAllKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z)  <- extract i iteMap
                       (x',y',z') <- liftM3 (,,) (go x) (go y) (go z)
                       addAllKids c [x',y',z']

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])
    go c@(CExistBool i) = return (i, [(i, frz c)], [])
    go c@(CExistNat  i) = return (i, [(i, frz c)], [])

    addKids ccode (a,b) = addAllKids ccode [a,b]

    addAllKids ccode stuff = return $
        let (node, nodes, edges) = unzip3 stuff
            hash = circuitHash ccode
            frzc = frz ccode
            edges' = [ (n, hash, frzc) | n <- node]
            node' = (hash, frzc)
        in (hash, node' : concat nodes, edges' ++ concat edges)

    tupM2 f (x, y) = liftM2 (,) (f x) (f y)
    frz ccode = FrozenShared ccode cmaps
    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x


shareGraph' :: (G.DynGraph gr, Ord v, Hashable v, Show v, Pretty term, Ord term) =>
              FrozenShared term v -> gr String String
shareGraph' (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z) <- extract i iteMap
                       ( (cNode, cNodes, cEdges)
                        ,(tNode, tNodes, tEdges)
                        ,(eNode, eNodes, eEdges)) <- liftM3 (,,) (go x) (go y) (go z)
                       return (i, (i, frz c) : cNodes ++ tNodes ++ eNodes
                              ,(cNode, i, "if")
                               : (tNode, i, "then")
                               : (eNode, i, "else")
                               : cEdges ++ tEdges ++ eEdges)

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])
    go c@(CExistBool i) = return (i, [(i, frz c)], [])
    go c@(CExistNat  i) = return (i, [(i, frz c)], [])
    go (COne i) = extract i oneMap >>= mapM go >>= addKidsOne i

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, "l") : (rNode, i, "r") : lEdges ++ rEdges)

    addKidsOne me tt = do
      let (tips, nodes, edges) = unzip3 tt
      let nodes' = (me, "ONE") : concat nodes
          edges' = [(n, me, "") | n <- tips ] ++ concat edges
      return (me, nodes', edges')


    tupM2 f (x, y) = liftM2 (,) (f x) (f y)

--    frz (CVar i) =  "v" ++ show i
    frz (CVar i) = show $ fromJust $ Bimap.lookup i (varMap cmaps)
    frz CFalse{} = "false"
    frz CTrue{}  = "true"
    frz CNot{}   = "not"
    frz CAnd{} = "/\\"
    frz COr{}  = "\\/"
    frz CIff{} = "<->"
    frz COnlyif{} = "->"
    frz CXor{} = "xor"
    frz CIte{} = "if-then-else"
    frz (CNat c) = "n" ++ show c
    frz CEq{} = "=="
    frz CLt{} = "<"
    frz COne{} = "ONE"
    frz (CExistBool i) = "v" ++ show i ++ "? (b)"
    frz (CExistNat  i) = "v" ++ show i ++ "? (n)"

    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x

removeExist :: ( Hashable term, Ord term, Ord v, Hashable v, Show v, ECircuit c, NatCircuit c, OneCircuit c, Co c v
               ) => FrozenShared term v -> c v
removeExist (FrozenShared code maps) = go code
  where
  -- dumb (for playing): remove existentials by replacing them with their assigned value (if any)
  existAssigs = Map.fromList $
                [ (f, val)| (f@CExistBool{}, val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (f@CExistNat{} , val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExistBool{}) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExistNat{} ) <- Bimap.elems(iffMap maps)]

  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren' c (varMap maps)
  go c@CExistBool{} = go $ Map.findWithDefault (error "removeExist: CExistBool") c existAssigs
  go c@CExistNat{}  = go $ Map.findWithDefault (error "removeExist: CExistNat") c existAssigs
  go c@(COr{})  = uncurry or  (go `onTup` getChildren c (orMap  maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))
  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(COne{}) = one . map go $ getChildren c (oneMap maps)
  go c@(CXor{}) = uncurry xor (go `onTup` getChildren c (xorMap  maps))
  go c@(COnlyif{}) = uncurry onlyif (go `onTup` getChildren c (onlyifMap  maps))
  go c@(CIff{}) = uncurry iff (go `onTup` getChildren c (iffMap  maps))
  go c@(CIte{}) = let
      (cc, tc, ec) = getChildren c (iteMap maps)
      [cond, t, e] = map go [cc, tc, ec]
      in ite cond t e

  go c@CNat{} = nat $ getChildren' c (natMap maps)
  go c@CEq{}  = uncurry eq (go `onTup` getChildren c (eqMap  maps))
  go c@CLt{}  = uncurry lt (go `onTup` getChildren c (ltMap  maps))

  onTup f (x, y) = (f x, f y)

-- | Returns an equivalent circuit with no iff, xor, onlyif, ite, nat, eq and lt nodes.
removeComplex :: ( Ord v, Hashable v, Show v
                 , Ord term, Hashable term
                 , Circuit c, Co c v
                 ) => [v] -> FrozenShared term v -> (c v, v :->: [v])
removeComplex freshVars c = assert disjoint $ (go code, bitnats)
  where
  -- casting removes the one constraints
  FrozenShared code maps = runShared (castCircuit c) `asTypeOf` c

  -- encoding nats as binary numbers
  bitwidth = fst . head . dropWhile ( (< Bimap.size (natMap maps)) . snd) . zip [1..] . iterate (*2) $ 2
  bitnats  = HashMap.fromList (Bimap.elems (natMap maps) `zip` chunk bitwidth freshVars)
  disjoint = all (`notElem` Bimap.elems (varMap maps))  (concat $ HashMap.elems bitnats)
  lookupBits c = fromJust $ HashMap.lookup (getChildren' c (natMap maps)) bitnats

  -- dumb (for playing): remove existentials by replacing them with their assigned value (if any)
  existAssigs = Map.fromList $
                [ (f, val)| (f@CExistBool{}, val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (f@CExistNat{} , val) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExistBool{}) <- Bimap.elems(iffMap maps)] ++
                [ (f, val)| (val, f@CExistNat{} ) <- Bimap.elems(iffMap maps)]

  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren' c (varMap maps)
  go c@CExistBool{} = go $ Map.findWithDefault (error "removeComplex: CExistBool") c existAssigs
  go c@CExistNat{}  = go $ Map.findWithDefault (error "removeComplex: CExistNat") c existAssigs
  go c@(COr{})  = uncurry or (go `onTup` getChildren c (orMap maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))
  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(COne{}) = oneDefault (map go (getChildren c (oneMap maps)))
  go c@(CXor{}) = let
      (l, r) = go `onTup` getChildren c (xorMap maps)
      in (l `or` r) `and` not (l `and` r)
  go c@(COnlyif{}) = let
      (p, q) = go `onTup` getChildren c (onlyifMap maps)
      in not p `or` q
  go c@(CIff{}) = let
      (p, q) = go `onTup` getChildren c (iffMap maps)
      in iff p q
  go c@(CIte{}) = let
      (cc, tc, ec) = getChildren c (iteMap maps)
      [cond, t, e] = map go [cc, tc, ec]
      in ite cond t e
  go  CNat{} = typeError "removeComplex: expected a boolean."

  go c@CEq{}
      | (a@CNat{}, b@CNat{}) <- getChildren c (eqMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = eq na nb

      | otherwise
      = typeError "removeComplex: expected a boolean."

  go c@(CLt{})
      | (a@CNat{}, b@CNat{}) <- getChildren c (ltMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = lt na nb

      | otherwise
      = typeError "removeComplex: expected a boolean."


--  fresh = do { v:vv <- get; put vv; return (input v)}

  iff p q = (not p `or` q) `and` (not q `or` p)
  ite cond t e = (cond `and` t) `or` (not cond `and` e)

  eq (p:pp) (q:qq) =      (     (not (input p) `and` not (input q))
                           `or` (input p `and` input q)
                          )
                     `and` eq pp qq
  eq [] [] = true
  eq [] qq = not $ orL $ map input qq
  eq pp [] = not $ orL $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] [] = false
  lt [] qq = orL $ map input qq
  lt _  [] = false

  onTup f (x, y) = (f x, f y)

--    -----------------------
-- ** Convert circuit to CNF
--    -----------------------

-- this data is private to toCNF.

data CNFState = CNFS{ toCnfVars :: !([Var])
                      -- ^ infinite fresh var source, starting at 1
                    , toCnfMap  :: !(Var :<->: CCode)
                    -- ^ record var mapping
                    , toBitMap  :: !(CCode :->: [Var])
--                    , toBitMap  :: !(Var :<->: (CCode,Int))
                    , numCnfClauses :: !Int
                    }

emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , numCnfClauses = 0
                    , toCnfMap = Bimap.empty
                    , toBitMap = mempty}

-- | retrieve and create (if necessary) a cnf variable for the given ccode.
findVar' ccode kfound knot = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    knot $ lit v
      Just v'  -> kfound $ lit v'


recordVar ccode comp = do
    m <- gets toCnfMap
    case Bimap.lookupR ccode m of
      Nothing -> do l <- comp
                    modify $ \s -> s{ toCnfMap = Bimap.insert (var l) ccode (toCnfMap s) }
                    return l
      Just v  -> return (lit v)

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.

data RPOCircuitProblem term v = RPOCircuitProblem
    { rpoProblemCnf     :: CNF
    , rpoProblemCircuit :: !(FrozenShared term v)
    , rpoProblemCodeMap :: !(Var :<->: CCode)
    , rpoProblemBitMap  :: !(Var :->: (CCode,Int)) }

-- Optimal CNF conversion
toCNF' :: (Hashable term, Ord term, Ord v, Hashable v, Show v) => [v] -> FrozenShared term v -> (ECircuitProblem v, v :->: [v])
toCNF' freshv = first(ECircuit.toCNF . ECircuit.runShared) . removeComplex freshv

-- Fast CNF conversion
toCNF :: (Ord v, Hashable v, Show v, Ord term, Hashable term, Show term) =>
         FrozenShared term v -> RPOCircuitProblem term v
toCNF c@(FrozenShared !sharedCircuit !circuitMaps) =
    CE.assert (validCMaps circuitMaps) $
    let (m,cnf) = (\x -> execRWS x circuitMaps emptyCNFState) $ do
                     l <- toCNF' sharedCircuit
                     writeClauses [[l]]

        bitMap = HashMap.fromList [ (v, (c,i)) | (c,vv) <- HashMap.toList (toBitMap m), (v,i) <- zip vv [0..]]

    in RPOCircuitProblem
       { rpoProblemCnf = CNF { numVars    = pred $ unVar $ head (toCnfVars m)
                             , numClauses = numCnfClauses m
                             , clauses    = cnf }
       , rpoProblemCircuit = c
       , rpoProblemCodeMap = toCnfMap m
       , rpoProblemBitMap  = bitMap}
  where
    writeClauses cc = incC (length cc) >> tell cc

    bitWidth  = fst . head
              . dropWhile ( (< Bimap.size (natMap circuitMaps)) . snd )
              . zip [1..] . iterate (*2)
              $ 2

    -- Returns l where {l} U the accumulated c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    toCNF' c@(CVar{})   = findVar' c goOn goOn
    toCNF' c@CExistBool{} = findVar' c goOn goOn
    toCNF' c@CExistNat{}  = findVar' c goOn goOn

    toCNF' CTrue{}  = true
    toCNF' CFalse{} = false
--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) =  findVar' c goOn $ \notLit -> do
        eTree  <- extract i notMap
        eLit   <- toCNF' eTree
        writeClauses [  [negate notLit, negate eLit]
                     ,   [eLit, notLit]
                     ]
        return notLit

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = findVar' c goOn $ \orLit -> do
        (l, r) <- extract i orMap
        lLit <- toCNF' l
        rLit <- toCNF' r

        writeClauses [  [negate lLit, orLit]
                     ,  [negate rLit, orLit]
                     ,  [negate orLit, lLit, rLit]]

        return orLit

--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = findVar' c goOn $ \andLit -> do
        (l, r) <- extract i andMap
        lLit <- toCNF' l
        rLit <- toCNF' r

        writeClauses [  [negate andLit, lLit]
                     ,  [negate andLit, rLit]
                     ,  [negate lLit, negate rLit, andLit]]

        return andLit

    toCNF' c@(CXor i) = recordVar c $ do
        (l,r) <- extract i xorMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        (lLit `or` rLit) `andM` notM (lLit `and` rLit)

    toCNF' c@(COnlyif i) = recordVar c $ do
        (l,r) <- extract i onlyifMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        (negate lLit `or` rLit)

    toCNF' c@(CIff i) = recordVar c $ do
        (l,r) <- extract i iffMap
        lLit <- toCNF' l
        rLit <- toCNF' r
        iff lLit rLit

    toCNF' c@(CIte i) = recordVar c $ do
        (c,t,e) <- extract i iteMap
        cLit <- toCNF' c
        tLit <- toCNF' t
        eLit <- toCNF' e
        ite cLit tLit eLit

    toCNF' c@(CEq i) = recordVar c $ do
        (nl,nr) <- extract i eqMap
        ll      <- findNat nl
        rr      <- findNat nr
        eq ll rr

    toCNF' c@(CLt i) = recordVar c $ do
        (nl,nr) <- extract i ltMap
        ll      <- findNat nl
        rr      <- findNat nr
        lt ll rr

    toCNF' c@(COne i) = recordVar c $ do
        cc      <- extract i oneMap
        case cc of
          [] -> false
          _  -> do
            vv      <- mapM toCNF' cc
            ones    <- replicateM (length vv) fresh
            zeros   <- replicateM (length vv) fresh
            f       <- false
            t       <- true
            writeClauses =<< mapM sequence
               [ [( return one_i  `iffM` ite b_i zero_i1 one_i1) `andM`
                    ( return zero_i `iffM` (negate b_i `and` zero_i1))]
                 | (b_i, one_i, zero_i, one_i1, zero_i1) <-
                     zip5 vv ones zeros (tail ones ++ [f]) (tail zeros ++ [t])
               ]
            return (head ones)
      where
       zip5 (a:aa) (b:bb) (c:cc) (d:dd) (e:ee)
           = (a,b,c,d,e) : zip5 aa bb cc dd ee
       zip5 _ _ _ _ _ = []

    toCNF' c = do
        m <- ask
        error $  "toCNF' bug: unknown code: " ++ show c
              ++ " with maps:\n" ++ show (m{hashCount=[]})

    true = findVar' (CTrue trueHash) goOn $ \l -> do
        writeClauses [[l]]
        return l

    false = findVar' (CFalse falseHash) goOn $ \l -> do
        writeClauses  [ [negate l]]
        return l


    orM l r = do { vl <- l; vr <- r; or vl vr}
--    or lLit rLit | trace ("or " ++ show lLit ++ " " ++ show rLit) False = undefined
    or lLit rLit = do
        me <- fresh
        writeClauses [  [negate lLit, me]
                     ,  [negate rLit, me]
                     ,  [negate me, lLit, rLit]]

        return me

    andM l r = do { vl <- l; vr <- r; and vl vr}

--    and lLit rLit | trace ("and " ++ show lLit ++ " " ++ show rLit) False = undefined
    and lLit rLit =  do
        me <- fresh
        writeClauses [  [negate me, lLit]
                     ,  [negate me, rLit]
                     ,  [negate lLit, negate rLit,me]]

        return me

    notM = liftM negate

--    iff lLit rLit | trace ("iff " ++ show lLit ++ " " ++ show rLit) False = undefined
    iffM ml mr = do {l <- ml; r <- mr; iff l r}
    iff lLit rLit = (negate lLit `or` rLit) `andM` (negate rLit `or` lLit)
    ite cLit tLit eLit = (cLit `and` tLit) `orM` (negate cLit `and` eLit)

    eq [] []         = true
    eq [] rr         = notM $ foldr orM false (map return rr)
    eq ll []         = notM $ foldr orM false (map return ll)
    eq (l:ll) (r:rr) = iff l r `andM` eq ll rr

    lt [] []         = false
    lt _ []          = false
    lt [] rr         = foldr orM false $ map return rr
    lt (l:ll) (r:rr) = lt ll rr `orM` ((negate l `and` r) `andM` eq ll rr)

    incC i = modify $ \m ->  m{numCnfClauses = numCnfClauses m + i}

    extract code f = do
        m <- asks f
        case Bimap.lookup code m of
          Nothing -> error $ "toCNFRpo: unknown code: " ++ show code
          Just x  -> return x

    findNat c@CNat{} = do
        bm <- gets toBitMap
        case HashMap.lookup c bm of
          Nothing -> do
              bits <- replicateM bitWidth fresh
              modify $ \s -> s{ toBitMap  = HashMap.insert c (map var bits) bm }
              return bits
          Just vv -> return (map lit vv)

    findNat _ = error "unreachable"

    goOn c = return c

    fresh = do
       v:vs <- gets toCnfVars
       modify $ \s -> s{toCnfVars=vs}
       return (lit v)


projectRPOCircuitSolution sol prbl = case sol of
                                    Sat lits   -> projectLits lits
                                    Unsat lits -> projectLits lits
  where
  RPOCircuitProblem _ (FrozenShared _ maps) codeMap bitsMap = prbl
  projectLits lits = Map.map Right vm `mappend`
                     Map.map (Left . fromBinary . map snd . sortBy (compare `on` fst)) bm
    where
    (vm, bm) =
      foldl (\m l -> case litHash l of
                       Var h   -> insertVar h l m
                       Bit h_i -> insertNat h_i l m
                       Auxiliar-> m)
            (initiallyAllFalseMap, initiallyAllZeroMap)
            (litAssignment lits)

    initiallyAllFalseMap = Map.fromList [(v,False) | v <- Bimap.elems (varMap maps)]
    initiallyAllZeroMap  = Map.empty -- 8fromList [(v,0)     | v <- Bimap.elems (natMap maps)]

    insertVar h l (mb,mn) = (mb',mn) where
         mb' = case Bimap.lookup h (varMap maps) of
                             Nothing -> mb
                             Just v  -> Map.insert v (litSign l) mb

    insertNat (h,i) l (mb,mn) = (mb,mn') where
         mn' = case Bimap.lookup h (natMap maps) of
                          Nothing -> mn
                          Just n  -> Map.insertWith (++) n [(i, litSign l)] mn

    litHash l = case Bimap.lookup (var l) codeMap of
                  Nothing -> case HashMap.lookup (var l) bitsMap of
                               Just (code,bit) -> Bit (circuitHash code, bit)
                               Nothing    -> Auxiliar
                  Just code -> Var (circuitHash code)

data ProjectionCase = Var CircuitHash | Bit (CircuitHash, Int) | Auxiliar



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
instance Hashable Var where hash (V i) = i

-- ----------
-- Helpers
-- ----------
safeAtL :: String -> [a] -> Int -> a
safeAtL msg [] _   = error ("safeAtL - index too large (" ++ msg ++ ")")
safeAtL _msg (x:_) 0 = x
safeAtL msg (_:xx) i = safeAtL msg xx (pred i)

selectSafe :: forall a. String -> [Int] -> [a] -> [a]
selectSafe msg ii xx
  | len Prelude.> 5   = map (safeIx (A.!) (A.listArray (0, len - 1) xx)) ii
  | otherwise = map (safeIx (!!) xx) ii
  where
    len = length xx
    safeIx :: forall container elem . (container -> Int -> elem) -> container -> Int -> elem
    safeIx ix xx' i
        | i Prelude.> len - 1 = error ("select(" ++ msg ++ "): index too large")
        | i < 0       = error ("select(" ++ msg ++ "): negative index")
        | otherwise = xx' `ix` i

#ifdef TEST
propSelect ii xx = map (xx!!) ii' == selectSafe "" ii' xx
  where _types = (xx::[Int], ii::[Int])
        ii'   = filter (< length xx) (map abs ii)

debug = return ()
pprTrace _ = id
#endif

-- -------
-- Errors
-- -------

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")

assert' :: String -> Bool -> a -> a
assert' msg cond foo =
  unsafePerformIO (
                   CE.assert cond (CE.evaluate foo)
                   `CE.catch` \(AssertionFailed str) ->
                       CE.throw (AssertionFailed (str++":\n"++msg))
                   )

on cmp f x y = f x `cmp` f y
