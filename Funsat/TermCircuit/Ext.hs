{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}

module Funsat.TermCircuit.Ext
       ( TermExtCircuit(..),
         lexgt, lexeq,
         lexpgt,lexpeq,
         mulgt,muleq
       )where

import Data.Foldable (Foldable)
import Data.Term as Family
import Funsat.ECircuit
import Funsat.TermCircuit hiding ((>),(~~))
import Funsat.TermCircuit.Internal
import Control.Monad.Cont (cont, runCont, replicateM)
import Data.List (tails, transpose)
import Control.Applicative (ZipList(..))
import Data.Traversable (traverse)
import Prelude.Extras
import Prelude hiding (or, (>), not, and)
import qualified Prelude as P

class (TermCircuit repr, HasPrecedence id, HasFiltering id, HasStatus id) =>
      TermExtCircuit repr id where
    exGt, exGe, exEq :: (id ~ Family.Id termF
                        ,v  ~ Family.Var id
                        ,termF ~ Family.TermF repr
                        ,Eq1 termF, Eq v'
                        ,Foldable termF, HasId1 termF
                        ,Co repr v
                        ,CoTerm repr termF v' v
                        ) =>
                        id -> id ->
                        [Term termF v'] -> [Term termF v'] -> repr v
    exGe id_s id_t ss tt = exGt id_s id_t ss tt `or` exEq id_s id_t ss tt

(>)  = termGt
(~~) = termEq

-- -----------------------------------
-- Lexicographic extension with AF
-- -----------------------------------

lexpeq, lexpgt, lexeq, lexgt, muleq, mulgt ::
         forall id termF repr tvar var .
         ( var   ~ Family.Var id
         , id    ~ Family.Id termF
         , termF ~ Family.TermF repr
         , HasId1 termF, Foldable termF
         , HasFiltering id, HasStatus id, HasPrecedence id
         , Eq1 termF, Eq id, Eq tvar
         , TermCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         , CoTerm repr termF tvar var
         ) => id -> id -> [Term termF tvar] -> [Term termF tvar] -> repr var

lexgt id_f id_g ff gg = go (zip (map input $ filtering_vv id_f) ff)
                           (zip (map input $ filtering_vv id_g) gg)
 where
  go :: [(repr var,Term termF tvar)] -> [(repr var,Term termF tvar)] -> repr var
  go []     _      = false
  go ff      []    = orL [ af_f | (af_f,_) <- ff]
  go ((af_f,f):ff) ((af_g,g):gg)
    =  ite af_f
           (ite af_g
                ((f > g) \/ ((f ~~ g) /\ go ff gg))
                (go ((af_f,f):ff) gg))
           (go ff ((af_g,g):gg))

lexeq id_f id_g ff gg = go (zip (map input $ filtering_vv id_f) ff)
                           (zip (map input $ filtering_vv id_g) gg)
 where
  go :: [(repr var,Term termF tvar)] -> [(repr var,Term termF tvar)] -> repr var
  go []     []     = true
  go ff      []    = not $ orL [ af_f | (af_f,_) <- ff]
  go []      gg    = not $ orL [ af_g | (af_g,_) <- gg]
  go ((af_f,f):ff) ((af_g,g):gg)
    =  ite af_f
           (ite af_g
                ((f ~~ g) /\ go ff gg)
                (go ((af_f,f):ff) gg))
           (go ff ((af_g,g):gg))

lexgt_exist _    _    [] _  = false
lexgt_exist id_f _    ff [] = orL . map input . filtering_vv $ id_f
lexgt_exist id_f id_g ff gg = (`runCont` id) $ do
-- We build a matrix M of dim n_f x n_g containing all
-- the comparisons between tails of ff and gg
-- That is, M[0,0] = lexgt ff gg
--          M[1,0] = lexgt (drop 1 ff) gg
--          M[0,1] = lexgt ff (drop 1 gg)
--          ...
-- Actually, the matrix containts additional elements
--          M[n_f+1, i] = value if we drop all the elements of ff and i elements of gg
--          M[i, n_g+1] = value if we drop all the elements of gg and i elements of ff
-- The proposition is true iff M[0,0] is true
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i, ff_i)  <-  (tails m `zip` tails (zip filters_f ff))
                      , (m_ij, gg_j) <-  (getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg))]

  return ( m!!0!!0 /\ andL assertions)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint _ []     _      = false
   constraint _ ff      []    = orL [ af_f | (af_f,_) <- ff]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f>g \/ (f~~g /\ m!!1!!1))
                         (m!!0!!1))
                    (m!!1!!0)


lexgt_existA, lexpgt_existA, lexpge_existA, lexeq_existA ::
  forall id termF tv v repr .
                        (HasPrecedence id
                        ,HasFiltering id
                        ,HasStatus id
                        ,HasId1 termF
                        ,Foldable termF
                        ,Eq1 termF, Eq tv
                        ,id ~ Family.Id termF
--                        ,id ~ Family.Id repr
                        ,v  ~ Family.Var id
                        ,termF ~ Family.TermF repr
                        ,ECircuit repr
                        ,ExistCircuit repr
                        ,TermCircuit repr
                        ,AssertCircuit repr
                        ,CoTerm repr termF tv v
                        ) =>
                        id -> id -> [Term termF tv] -> [Term termF tv] -> repr v
lexgt_existA _    _    [] _  = false
lexgt_existA id_f _    ff [] = orL . map input . filtering_vv $ id_f
lexgt_existA id_f id_g ff gg = (`runCont` id) $ do
-- We build a matrix M of dim n_f x n_g containing all
-- the comparisons between tails of ff and gg
-- That is, M[0,0] = lexgt ff gg
--          M[1,0] = lexgt (drop 1 ff) gg
--          M[0,1] = lexgt ff (drop 1 gg)
--          ...
-- Actually, the matrix containts additional elements
--          M[n_f+1, i] = value if we drop all the elements of ff and i elements of gg
--          M[i, n_g+1] = value if we drop all the elements of gg and i elements of ff
-- The proposition is true iff M[0,0] is true
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i, ff_i)  <-  (tails m `zip` tails (zip filters_f ff))
                      , (m_ij, gg_j) <-  (getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg))]

  return $ assertCircuits assertions (head $ head m)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint :: [[repr v]] -> [(repr v,Term termF tv)] -> [(repr v,Term termF tv)] -> repr v
   constraint _ []     _      = false
   constraint _ ff      []    = orL [ af_f | (af_f,_) <- ff]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f>g \/ (f~~g /\ m!!1!!1))
                         (m!!0!!1))
                    (m!!1!!0)

lexeq_exist _    _    [] [] = true
lexeq_exist id_f _    _  [] = not . orL . map input . filtering_vv $ id_f
lexeq_exist _    id_g [] _  = not . orL . map input . filtering_vv $ id_g
lexeq_exist id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i,  ff_i) <- tails m `zip` tails (zip filters_f ff)
                      , (m_ij, gg_j) <- getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg)]

  return ( m!!0!!0 /\ andL assertions)
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint _ []     []     = true
   constraint _ ff      []    = not $ orL [ af_f | (af_f,_) <- ff]
   constraint _ []      gg    = not $ orL [ af_g | (af_g,_) <- gg]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f~~g /\ m!!1!!1)
                         (m!!0!!1))
                    (m!!1!!0)

--lexeq_existA _    _    [] [] = true
--lexeq_existA id_f _    _  [] = not . orL . map input . filtering_vv $ id_f
--lexeq_existA _    id_g [] _  = not . orL . map input . filtering_vv $ id_g
lexeq_existA id_f id_g ff gg = (`runCont` id) $ do
  m <- replicateM (length ff + 1) $ replicateM (length gg + 1) (cont existsBool)
  let assertions = [ m_ij!!0!!0 <--> constraint m_ij ff_i gg_j
                      | (m_i,  ff_i) <- tails m `zip` tails (zip filters_f ff)
                      , (m_ij, gg_j) <- getZipList (traverse (ZipList . tails) m_i)
                                        `zip` tails (zip filters_g gg)]

  return ( assertCircuits assertions (head $ head m) )
 where
   filters_f = map input (filtering_vv id_f)
   filters_g = map input (filtering_vv id_g)

   constraint :: [[repr v]] -> [(repr v,Term termF tv)] -> [(repr v,Term termF tv)] -> repr v
   constraint _ []     []     = true
   constraint _ ff      []    = not $ orL [ af_f | (af_f,_) <- ff]
   constraint _ []      gg    = not $ orL [ af_g | (af_g,_) <- gg]
   constraint m ((af_f,f):ff) ((af_g,g):gg)
             =  ite af_f
                    (ite af_g
                         (f~~g /\ m!!1!!1)
                         (m!!0!!1))
                    (m!!1!!0)

--lexpeq :: (ECircuit repr, TermCircuit repr (Symbol a)) =>
--          Symbol a -> Symbol a -> [TermN (Symbol a)] -> [TermN (Symbol a)] -> repr Var
--lexpeq id_f id_g ss tt | pprTrace (text "encoding " <+> ss <+> text "~" <+> tt) False = undefined
lexpeq id_f id_g ss tt =
  eqArity `and`
  andL ( [ (f_ik /\ g_jk) --> s_i ~~ t_j
              | (s_i, f_i) <- zip ss ff
              , (t_j, g_j) <- zip tt gg
              , (f_ik, g_jk) <- zip f_i g_j])
    where
       (Just ff, Just gg) = (lexPerm id_f, lexPerm id_g)
       eqArity = andL ( take m (zipWith (<-->) (map orL ff ++ repeat false)
                                              (map orL gg ++ repeat false))
                     )
       m   = max (length ff) (length gg)

--lexpgt id_f id_g ss tt | pprTrace (text "encoding " <+> ss <+> text ">" <+> tt) False = undefined
lexpgt id_f id_g ss tt = expgt_k (transpose $ enc_f) (transpose $ enc_g)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g
       n = length ss
       m = length tt
       expgt_k [] _ = false
       expgt_k (f_k:_) [] = orL f_k
       expgt_k (f_k:ff) (g_k:gg)
         = orL [f_ik /\ andL [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ expgt_k ff gg))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpgt_exist id_f id_g [] _  = false
lexpgt_exist id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expgt_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then orL (transpose enc_f !! length tt)
                   else false

  let assertions = zipWith (<-->) vf_k constraints
  return (head vf_k /\ andL assertions)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expgt_k f_k g_k next
         = orL [f_ik /\ andL [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpgt_existA id_f id_g [] _  = false
lexpgt_existA id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expgt_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then orL (transpose enc_f !! length tt)
                   else false

  let assertions = zipWith (<-->) vf_k constraints
  return (assertCircuits assertions $ head vf_k)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expgt_k f_k g_k next
         = orL [f_ik /\ andL [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

lexpge_existA id_f id_g ss tt = (`runCont` id) $ do
  let k = min (length ss) (length tt) + 1
  vf_k <- replicateM k (cont existsBool)
  let constraints = zipWith3 expge_k (transpose $ enc_f) (transpose $ enc_g) (tail vf_k) ++
                    [the_tail]
      the_tail = if length ss P.> length tt
                   then eqArity \/ orL (enc_f !! length tt)
                   else eqArity

  let assertions = zipWith (<-->) vf_k constraints
  return (assertCircuits assertions $ head vf_k)
     where
       Just enc_f = lexPerm id_f
       Just enc_g = lexPerm id_g

       expge_k f_k g_k next
         = orL [f_ik /\ andL [ g_jk --> (s_i >  t_j \/
                                      (s_i ~~ t_j /\ next))
                            | (g_jk, t_j) <- zip g_k tt]
                | (f_ik, s_i) <- zip f_k ss]

       m = max (length enc_f) (length enc_g)
       eqArity = andL ( take m (zipWith (<-->) (map orL enc_f ++ repeat false)
                                              (map orL enc_g ++ repeat false))
                     )



-- ---------------------------
-- Multiset extension with AF
-- ---------------------------

mulgt id_f id_g []  _   = false
mulgt id_f id_g ff  gg  =
    mulgen id_f id_g ff gg (\epsilons ->
                                not $ andL [inAF i id_f --> ep_i
                                           | (i, ep_i) <- zip [1..] epsilons])

muleq id_f id_g [] [] = true
muleq id_f id_g [] gg = none $ map (`inAF` id_g) [1..length gg]
muleq id_f id_g ff gg =
    mulgen id_f id_g ff gg (\epsilons ->
                                andL [inAF i id_f --> ep_i
                                      | (i, ep_i) <- zip [1..] epsilons])


mulgen:: ( var   ~ Family.Var id
         , id    ~ Family.Id termF
         , termF ~ Family.TermF repr
         , HasFiltering id, HasStatus id, HasPrecedence id
         , HasId1 termF, Foldable termF, Eq1 termF, Eq tvar, Eq id
         , TermCircuit repr, ExistCircuit repr, OneCircuit repr, ECircuit repr
         , CoTerm repr termF tvar var
         ) => id -> id -> [Term termF tvar] -> [Term termF tvar] -> ([repr var] -> repr var) ->  repr var
mulgen id_f id_g ff gg k = (`runCont` id) $ do
    let (i,j)    = (length ff, length gg)

    epsilons  <- replicateM i (cont existsBool)
    gammasM_t <- replicateM i $ replicateM j (cont existsBool)
    let gammasM = transpose gammasM_t

        oneCoverForNonFilteredSubtermAndNoCoverForFilteredSubterms =
          [ ite (inAF j id_g)
                (one  gammas_j)
                (none gammas_j)
            | (j, gammas_j) <- zip [1..] gammasM ]

        filteredSubtermsCannotCover =
          [ not(inAF i id_f) --> none gammas_i
            | (i, gammas_i) <- zip [1..] gammasM_t]

        subtermUsedForEqualityMustCoverOnce =
          [ ep_i --> one gamma_i
            | (ep_i, gamma_i) <- zip epsilons gammasM_t]

        greaterOrEqualMultisetExtension =
          [ gamma_ij --> ite ep_i (f_i ~~ g_j)
                                  (f_i >  g_j)
                  | (ep_i, gamma_i, f_i) <- zip3 epsilons gammasM_t ff
                  , (gamma_ij, g_j)      <- zip  gamma_i gg]
    return $
      andL ( k epsilons
           : oneCoverForNonFilteredSubtermAndNoCoverForFilteredSubterms
          ++ filteredSubtermsCannotCover
          ++ subtermUsedForEqualityMustCoverOnce
          ++ greaterOrEqualMultisetExtension
           )
