{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Data.Pattern.Any
-- Description : A module to work with a 'QuasiQuoter' to use different patterns in the head same function clause.
-- Maintainer  : hapytexeu+gh@gmail.com
-- Stability   : experimental
-- Portability : POSIX
--
-- The module exposes two 'QuasiQuoter's named 'anypat' and 'maypat' that allow compiling separate patterns into a single (view) pattern that
-- will fire in case any of the patterns matches. If there are any variable names, it will match these. For the 'anypat' it requires that all
-- variables occur in all patterns. For 'maypat' that is not a requirement. For both 'QuasiQuoter's, it is however required that the variables
-- have the same type in each pattern.
module Data.Pattern.Any
  ( -- * Quasiquoters
    anypat,
    maypat,
    rangepat,

    -- * derive variable names names from patterns
    patVars,
    patVars',

    -- * Range objects
    RangeObj (FromRange, FromThenRange, FromToRange, FromThenToRange),
    rangeToList,
    inRange,
  )
where

import Control.Arrow (first)
import Control.Monad ((>=>))
# if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif
import Data.Function (on)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Language.Haskell.Exts.Parser (ParseResult (ParseFailed, ParseOk), parseExp, parsePat)
import Language.Haskell.Meta (toExp, toPat)
import Language.Haskell.TH (Body (NormalB), Exp (AppE, ArithSeqE, ConE, LamCaseE, TupE, VarE), Match (Match), Name, Pat (AsP, BangP, ConP, InfixP, ListP, LitP, ParensP, RecP, SigP, TildeP, TupP, UInfixP, UnboxedSumP, UnboxedTupP, VarP, ViewP, WildP), Q, Range (FromR, FromThenR, FromThenToR, FromToR))
import Language.Haskell.TH.Quote (QuasiQuoter (QuasiQuoter))

data HowPass = Simple | AsJust | AsNothing deriving (Eq, Ord, Read, Show)

-- | A 'RangeObj' that specifies a range with a start value and optionally a step value and end value.
data RangeObj a
  = FromRange a  -- ^ A 'RangeObj' object that only has a start value, in Haskell specified as @[b ..]@.
  | FromThenRange a a  -- ^ A 'RangeObj' object that has a start value and end value, in Haskell specified as @[b .. e]@.
  | FromToRange a a  -- ^ A 'RangeObj' object with a start and next value, in Haskell specified as @[b, s ..]@.
  | FromThenToRange a a a  -- ^ A 'RangeObj' object with a start, next value and end value, in Haskell specified as @[b, s .. e]@.
  deriving (Eq, Functor, Read, Show)

instance Enum a => Semigroup (RangeObj a) where
  r1 <> r2 = toEnum <$> (go `on` fmap fromEnum) r1 r2
    where
      go (FromRange b1) (FromRange b2) = FromRange (max b1 b2)
      go (FromRange b1) (FromToRange b2 e2) = FromToRange (max b1 b2) e2
      go (FromToRange b1 e1) (FromRange b2) = FromToRange (max b1 b2) e1
      go (FromToRange b1 e1) (FromToRange b2 e2) = FromToRange (max b1 b2) (min e1 e2)


-- | Convert the 'RangeObj' to a list of the values defined by the range.
rangeToList :: Enum a =>
  -- | The 'RangeObj' item to convert to a list.
  RangeObj a ->
  -- | A list of items the 'RangeObj' spans.
  [a]
rangeToList (FromRange b) = enumFrom b
rangeToList (FromThenRange b t) = enumFromThen b t
rangeToList (FromToRange b e) = enumFromTo b e
rangeToList (FromThenToRange b t e) = enumFromThenTo b t e

-- | Provides a list of variable names for a given 'Pat'tern. The list is /not/ sorted. If the same variable name occurs multiple times (which does not make much sense), it will be listed multiple times.
patVars' ::
  -- | The 'Pat'tern to inspect.
  Pat ->
  -- | The list of remaining elements that is added as tail.
  [Name] ->
  -- | The list of variable names that is used to collect (fragments) of the pattern.
  [Name]
patVars' (LitP _) = id
patVars' (VarP n) = (n :)
patVars' (TupP ps) = patVarsF ps
patVars' (UnboxedTupP ps) = patVarsF ps
patVars' (UnboxedSumP p _ _) = patVars' p
patVars' (InfixP p₁ _ p₂) = patVars' p₁ . patVars' p₂
patVars' (UInfixP p₁ _ p₂) = patVars' p₁ . patVars' p₂
patVars' (ParensP p) = patVars' p
patVars' (TildeP p) = patVars' p
patVars' (BangP p) = patVars' p
patVars' (AsP n p) = (n :) . patVars' p
patVars' WildP = id
patVars' (RecP _ ps) = patVarsF (map snd ps)
patVars' (ListP ps) = patVarsF ps
patVars' (SigP p _) = patVars' p
patVars' (ViewP _ p) = patVars' p
patVars' x = patVarsExtra' x

#if MIN_VERSION_template_haskell(2,18,0)
patVarsExtra' :: Pat -> [Name] -> [Name]
patVarsExtra' (ConP _ _ ps) = patVarsF ps
patVarsExtra' _ = id
#else
patVarsExtra' :: Pat -> [Name] -> [Name]
patVarsExtra' (ConP _ ps) = patVarsF ps
patVarsExtra' _ = id
#endif

patVarsF :: [Pat] -> [Name] -> [Name]
patVarsF = foldr ((.) . patVars') id

-- | Provides a list of variable names for a given 'Pat'tern. The list is /not/ sorted. If the same variable name occurs multiple times (which does not make much sense), it will be listed multiple times.
patVars ::
  -- | The 'Pat'tern to inspect.
  Pat ->
  -- | The list of variable names that is used to collect (fragments) of the pattern.
  [Name]
patVars = (`patVars'` [])

howPass :: Bool -> Bool -> HowPass
howPass False True = AsJust
howPass False False = AsNothing
howPass True True = Simple
howPass True False = error "This should never happen"

unionPats :: NonEmpty Pat -> ([(Bool, Name)], [[(HowPass, Name)]])
unionPats (x :| xs) = (un, un')
  where
    n0 = go x
    ns = map go xs
    go = sort . patVars
    go' = map (True,)
    un = foldr (sortedUnion False False (&&) . go') (go' n0) ns
    un' = map (sortedUnion False False howPass un . map (True,)) (n0 : ns)

#if MIN_VERSION_template_haskell(2,18,0)
conP :: Name -> [Pat] -> Pat
conP = (`ConP` [])
#else
conP :: Name -> [Pat] -> Pat
conP = ConP
#endif

bodyPat :: Bool -> [Name] -> (Exp, Pat)
bodyPat _ [] = (ConE 'False, conP 'True [])
bodyPat b [n] = (ConE 'Nothing, wrapIt (conP 'Just . pure) b (VarP n))
bodyPat b ns = (ConE 'Nothing, wrapIt (conP 'Just . pure) b (TildeP (TupP (map VarP ns))))

transName' :: HowPass -> Name -> Exp
transName' Simple = VarE
transName' AsNothing = const (ConE 'Nothing)
transName' AsJust = AppE (ConE 'Just) . VarE

transName :: (HowPass, Name) -> Exp
transName = uncurry transName'

#if MIN_VERSION_template_haskell(2, 16, 0)
_transName :: (HowPass, Name) -> Maybe Exp
_transName = Just . transName
#else
_transName :: (HowPass, Name) -> Exp
_transName = transName
#endif

wrapIt :: (a -> a) -> Bool -> a -> a
wrapIt f = go
  where
    go False = id
    go True = f

bodyExp :: Bool -> [(HowPass, Name)] -> Exp
bodyExp _ [] = ConE 'True
bodyExp b [n] = wrapIt (ConE 'Just `AppE`) b (transName n)
bodyExp b ns = wrapIt (ConE 'Just `AppE`) b (TupE (map _transName ns))

unionCaseFunc' :: [Pat] -> [Name] -> [[(HowPass, Name)]] -> (Exp, Pat)
unionCaseFunc' ps ns ns' = (LamCaseE (zipWith (\p' n -> Match p' (NormalB (bodyExp partial n)) []) ps ns' ++ add), p)
  where
    ~(ef, p) = bodyPat partial ns
    partial = WildP `notElem` ps
    add = [Match WildP (NormalB ef) [] | partial]

sortedUnion :: Ord a => b -> c -> (b -> c -> d) -> [(b, a)] -> [(c, a)] -> [(d, a)]
sortedUnion v0 v1 f = go
  where
    go [] ys = map (first (f v0)) ys
    go xa@((b0, x) : xs) ya@((b1, y) : ys) = case compare x y of
      EQ -> (f b0 b1, x) : go xs ys
      GT -> (f v0 b1, y) : go xa ys
      LT -> (f b0 v1, x) : go xs ya
    go xs [] = map (first (`f` v1)) xs

unionCaseFuncWith :: MonadFail m => ((Exp, Pat) -> a) -> Bool -> NonEmpty Pat -> m a
unionCaseFuncWith f chk ps@(p0 :| ps')
  | not chk || all fst ns = pure (f (unionCaseFunc' (p0 : ps') (map snd ns) ns'))
  | otherwise = fail "Not all patterns have the same variable names"
  where
    (ns, ns') = unionPats ps

unionCaseFunc :: MonadFail m => Bool -> NonEmpty Pat -> m Pat
unionCaseFunc = unionCaseFuncWith (uncurry ViewP)

unionCaseExp :: MonadFail m => Bool -> NonEmpty Pat -> m Exp
unionCaseExp = unionCaseFuncWith fst

#if MIN_VERSION_template_haskell(2,18,0)
parsePatternSequence :: String -> ParseResult (NonEmpty Pat)
parsePatternSequence s = go (toPat <$> parsePat ('(' : s ++ ")"))
  where
    go (ParseOk (ConP n [] [])) | n == '() = fail "no patterns specified"
    go (ParseOk (ParensP p)) = pure (p :| [])
    go (ParseOk (TupP [])) = fail "no patterns specified"
    go (ParseOk (TupP (p : ps))) = pure (p :| ps)
    go (ParseOk _) = fail "not a sequence of patterns"
    go (ParseFailed l m) = ParseFailed l m
#else
parsePatternSequence :: String -> ParseResult (NonEmpty Pat)
parsePatternSequence s = go (toPat <$> parsePat ('(' : s ++ ")"))
  where
    go (ParseOk (ConP n [])) | n == '() = fail "no patterns specified"
    go (ParseOk (ParensP p)) = pure (p :| [])
    go (ParseOk (TupP [])) = fail "no patterns specified"
    go (ParseOk (TupP (p : ps))) = pure (p :| ps)
    go (ParseOk _) = fail "not a sequence of patterns"
    go (ParseFailed l m) = ParseFailed l m

#endif

liftFail :: MonadFail m => ParseResult a -> m a
liftFail (ParseOk x) = pure x
liftFail (ParseFailed _ s) = fail s

failQ :: a -> Q b
failQ = const (fail "The QuasiQuoter can only work to generate code as pattern or expression.")

parseRange :: String -> ParseResult Range
parseRange s = go (toExp <$> parseExp ('[' : s ++ "]"))
  where
    go (ParseOk (ArithSeqE r)) = pure r
    go _ = fail "Not a range expression"

-- | Convert a 'Range' objects from the 'Language.Haskell.TH' module to a 'RangeObj' with 'Exp' as parameters.
rangeToRangeObj
  :: Range  -- ^ The 'Range' object to convert.
  -> RangeObj Exp  -- ^ The equivalent 'RangeObj' with the 'Exp'ressions as parameters.
rangeToRangeObj (FromR b) = FromRange b
rangeToRangeObj (FromThenR b s) = FromThenRange b s
rangeToRangeObj (FromToR b e) = FromToRange b e
rangeToRangeObj (FromThenToR b s e) = FromThenToRange b s e

-- | Convert a 'RangeObj' to the corresponding 'Exp'ression. This will all the appropriate 'RangeObj' data constructor with the parameters.
rangeObjToExp
  :: RangeObj Exp  -- ^ A 'RangeObj' with 'Exp'ressions as parameters.
  -> Exp  -- ^ An 'Exp'ression that contains the data constructor applied to the parameters.
rangeObjToExp (FromRange b) = ConE 'FromRange `AppE` b
rangeObjToExp (FromThenRange b s) = ConE 'FromThenRange `AppE` b `AppE` s
rangeObjToExp (FromToRange b e) = ConE 'FromToRange `AppE` b `AppE` e
rangeObjToExp (FromThenToRange b s e) = ConE 'FromThenToRange `AppE` b `AppE` s `AppE` e

-- | A quasquoter to specify multiple patterns that will succeed if any of the patterns match. All patterns should have the same set of variables and these should
-- have the same type, otherwise a variable would have two different types, and if a variable is absent in one of the patterns, the question is what to pass as value.
anypat ::
  -- | The quasiquoter that can be used as expression and pattern.
  QuasiQuoter
anypat = QuasiQuoter ((liftFail >=> unionCaseExp True) . parsePatternSequence) ((liftFail >=> unionCaseFunc True) . parsePatternSequence) failQ failQ

-- | A quasiquoter to specify multiple patterns that will succeed if any of these patterns match. Patterns don't have to have the same variable names but if a variable is shared over the
-- different patterns, it should have the same type. In case a variable name does not appear in all patterns, it will be passed as a 'Maybe' to the clause with 'Nothing' if a pattern matched
-- without that variable name, and a 'Just' if the (first) pattern that matched had such variable.
maypat ::
  -- | The quasiquoter that can be used as expression and pattern.
  QuasiQuoter
maypat = QuasiQuoter ((liftFail >=> unionCaseExp False) . parsePatternSequence) ((liftFail >=> unionCaseFunc False) . parsePatternSequence) failQ failQ

_rangeCheck :: Int -> Int -> Int -> Bool
_rangeCheck b e x = b <= x && x <= e

_modCheck :: Int -> Int -> Int -> Bool
_modCheck b t x = (x - b) `mod` (t - b) == 0

inRange :: Enum a => RangeObj a -> a -> Bool
inRange r = go (fromEnum <$> r) . fromEnum
  where
    go (FromRange b) = (b <=)
    go (FromToRange b e) = _rangeCheck b e
    go (FromThenRange b t)
      | EQ <- cmp = (b ==)
      | LT <- cmp = _both (b <=) (_modCheck b t)
      | otherwise = _both (b >=) (_modCheck b t)
      where
        cmp = compare b t
    go (FromThenToRange b t e)
      | EQ <- cmp, e >= b = (b ==)
      | LT <- cmp, e >= b = _both (_rangeCheck b e) (_modCheck b t)
      | GT <- cmp, e <= b = _both (_rangeCheck e b) (_modCheck b t)
      | otherwise = const False -- empty range
      where
        cmp = compare b t

_both :: (a -> Bool) -> (a -> Bool) -> a -> Bool
_both f g x = f x && g x

-- | A 'QuasiQuoter' to parse a range expression to a 'RangeObj'. In case the 'QuasiQuoter' is used for a pattern,
-- it compiles into a /view pattern/ that will work if the element is a member of the 'RangeObj'.
rangepat ::
  -- | The quasiquoter that can be used as expression and pattern.
  QuasiQuoter
rangepat = QuasiQuoter (parsefun id) (parsefun ((`ViewP` ConP 'True [] []) . (VarE 'inRange `AppE`))) failQ failQ
  where
    parsefun pp = (liftFail >=> (pure . pp . rangeObjToExp . rangeToRangeObj)) . parseRange
