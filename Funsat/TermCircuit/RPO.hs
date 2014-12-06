{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Funsat.TermCircuit.RPO where

import Control.Monad.Free
import Data.Foldable (Foldable)
import Data.Hashable
import Data.Term as Family
import Funsat.ECircuit
import Funsat.TermCircuit
import Funsat.TermCircuit.Internal
import Funsat.TermCircuit.Ext
import Text.PrettyPrint.HughesPJClass hiding (first)
import System.IO.Unsafe

import Prelude.Extras
import Prelude hiding (and, not, or, (>))
import qualified Prelude
import Data.List (sortBy)
import qualified Data.Traversable as T
import qualified Data.Array as A
import Control.Exception(AssertionFailed(..))
import qualified Control.Exception as CE


-- ---------
-- Encoding
-- ---------

termGt_, termEq_ ::
        (var   ~ Family.Var id
        ,termf ~ Family.TermF repr
        ,id    ~ Family.Id termf
        ,Eq var', Eq1 termf
        ,Eq id, HasId1 termf, Foldable termf
        ,ECircuit repr, NatCircuit repr
        ,TermExtCircuit repr id, Co repr var, CoTerm repr termf var' var
        ) =>
        Term termf var' -> Term termf var' -> repr var

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

    s > t   = termGt_ s t
    s ~~ t  = termEq_ s t

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
              ((precedence id_s `eq` precedence id_t) `and` exEq id_s id_t ss tt)
              (all (\(t_j,j) -> inAF j id_t --> s ~~ t_j) (zip tt [1..])))
         (all (\(s_i,i) -> inAF i id_s --> s_i ~~ t) (zip ss [1..]))

   where
    ss = directSubterms s
    tt = directSubterms t
    ~(Just id_s) = rootSymbol s
    ~(Just id_t) = rootSymbol t

    all f = andL . map f

    infixr 8 ~~

    s ~~ t  = termEq_ s t


-- ---------
-- Evaluator
-- ---------

instance OneCircuit Eval where
  one tt    = Eval (\env -> Right $ case filter id $  map (fromRight . (`unEval` env)) tt of
                                        (_:[]) -> True
                                        _      -> False)

instance TermCircuit Eval  where
  type CoTerm_ Eval termF tv v =
      ( Hashable v
      , Eq (Term termF tv)
      , Foldable termF, HasId1 termF
      , Eq(Id termF), HasStatus (Id termF), HasFiltering (Id termF), HasPrecedence (Id termF)
      , Pretty (Id termF), Show (Id termF)
      )

  termGt t u = unEvalM (Right `liftM` (>) evalRPO t u)
  termEq t u = unEvalM (Right `liftM` (~~) evalRPO t u)

instance TermCircuit (WrapEval (Term termF var))  where
   type CoTerm_ (WrapEval (Term termF var)) termF tv v =
       ( var ~ tv
       , Eq var
       , Eq (Term termF var)
       , Foldable termF, HasId1 termF
       , HasStatus (Id termF), HasFiltering (Id termF), HasPrecedence (Id termF)
       , Eq(Id termF), Pretty (Id termF), Show (Id termF)
       , Hashable v
       )
   termGt t u = WrapEval $ unEvalM (Right `liftM` (>)  evalRPO t u)
   termEq t u = WrapEval $ unEvalM (Right `liftM` (~~) evalRPO t u)

-- -------
-- Checker
-- -------

evalRPO :: forall termF id v var.
           (HasPrecedence id, HasStatus id, HasFiltering id
           ,Ord v, Hashable v, Show v
           ,Eq id, Pretty id, Show id
           ,Eq(Term termF var)
           ,Foldable termF, HasId1 termF
           ,id ~ Id termF
           ,v  ~ Family.Var id
           ) => TermEval (Term termF var) v
evalRPO = Term{..} where

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
      (Left i, _) -> safeAtL "TermCircuit:928" tt_s (pred i) ~~ t
      (_, Left j) -> s ~~ safeAtL "TermCircuit:929" tt_t (pred j)
      (_,_) -> evalB (precedence id_s `eq` precedence id_t) <&> exeq s t

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
      Left i-> safeAtL "TermCircuit:935" tt_s (pred i) ~~ t
      _     -> return False

   | Just id_t <- rootSymbol t, tt_t <- directSubterms t = do
     af_t <- compFiltering id_t
     case af_t of
      Left j -> s ~~ safeAtL "TermCircuit:941" tt_t (pred j)
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
      (Left i, _) -> safeAtL "TermCircuit:955" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "TermCircuit:956" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> exgt s t)
   | Just id_t <- rootSymbol t, tt_t <- directSubterms t
   , Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     af_t <- compFiltering id_t
     case (af_s, af_t) of
      (Left i, Left j) -> safeAtL "TermCircuit:698" tt_s (pred i) > safeAtL "TermCircuit:698" tt_t (pred j)
      (Left i, _) -> safeAtL "TermCircuit:698" tt_s (pred i) > t
      (_, Left j) -> s > safeAtL "TermCircuit:699" tt_t (pred j)
      (Right ii,Right jj) -> anyM (>~ t) (sel 3 ii tt_s) <|>
                             (allM (s >) (sel 4 jj tt_t)  <&> (evalB (precedence id_s `gt` precedence id_t)
                                                                   <|>
                                                              (evalB (precedence id_s `eq` precedence id_t) <&>
                                                               exgt s t)))

   | Just id_s <- rootSymbol s, tt_s <- directSubterms s = do
     af_s <- compFiltering id_s
     case af_s of
       Left  i  -> safeAtL "TermCircuit:709" tt_s (pred i) > t
       Right ii -> anyM (>~ t) (sel 5 ii tt_s)

   | otherwise = return False

  exgt, exeq :: Term termF var -> Term termF var -> EvalM v Bool
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
  sel n ii = selectSafe ("Narradar.Constraints.SAT.TermCircuit.Eval - " ++ show n) (map pred ii)
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


  applyFiltering (Right ii) tt = selectSafe "TermCircuit.verifyTermAF.applyFiltering" (map pred ii) tt
  applyFiltering (Left j)   tt = [safeAtL   "TermCircuit.verifyTermAF.applyFiltering" tt (pred j)]


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
