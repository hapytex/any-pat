{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
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
    hashpat,
    ϵ,

    -- * compile hash patterns
    combineHashViewPats,

    -- * derive variable names names from patterns
    patVars,
    patVars',

    -- * Range objects
    RangeObj (RangeObj, rangeBegin, rangeThen, rangeEnd),
    pattern FromRange,
    pattern FromThenRange,
    pattern FromToRange,
    pattern FromThenToRange,
    rangeToList,
    inRange,
    (∈),
    (∋),
    rangeLength,
    rangeDirection,
    rangeLastValue,
  )
where

import Control.Arrow (first)
import Control.Monad ((>=>))
# if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif
import Data.HashMap.Strict (lookup)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Language.Haskell.Exts.Extension (Extension (EnableExtension), KnownExtension (ViewPatterns))
import Language.Haskell.Exts.Parser (ParseMode (extensions), ParseResult (ParseFailed, ParseOk), defaultParseMode, parseExp, parsePatWithMode)
import Language.Haskell.Meta (toExp, toPat)
import Language.Haskell.TH (Body (NormalB), Exp (AppE, ArithSeqE, ConE, LamCaseE, LamE, TupE, VarE), Match (Match), Name, Pat (AsP, BangP, ConP, InfixP, ListP, LitP, ParensP, RecP, SigP, TildeP, TupP, UInfixP, UnboxedSumP, UnboxedTupP, VarP, ViewP, WildP), Q, Range (FromR, FromThenR, FromThenToR, FromToR), newName)
import Language.Haskell.TH.Quote (QuasiQuoter (QuasiQuoter))

data HowPass = Simple | AsJust | AsNothing deriving (Eq, Ord, Read, Show)

-- | A 'RangeObj' that specifies a range with a start value and optionally a step value and end value.
data RangeObj a = RangeObj {rangeBegin :: a, rangeThen :: Maybe a, rangeEnd :: Maybe a}
  deriving (Eq, Functor, Read, Show)

-- | A 'RangeObj' object that only has a start value, in Haskell specified as @[b ..]@.
pattern FromRange :: a -> RangeObj a
pattern FromRange b = RangeObj b Nothing Nothing

-- | A 'RangeObj' object that has a start value and end value, in Haskell specified as @[b .. e]@.
pattern FromThenRange :: a -> a -> RangeObj a
pattern FromThenRange b e = RangeObj b (Just e) Nothing

-- | A 'RangeObj' object with a start and next value, in Haskell specified as @[b, s ..]@.
pattern FromToRange :: a -> a -> RangeObj a
pattern FromToRange b t = RangeObj b Nothing (Just t)

-- | A 'RangeObj' object with a start, next value and end value, in Haskell specified as @[b, s .. e]@.
pattern FromThenToRange :: a -> a -> a -> RangeObj a
pattern FromThenToRange b t e = RangeObj b (Just t) (Just e)

-- | Determine the last value of a 'RangeObj', given the 'RangeObj' has an /explicit/ end value.
-- The last value is /not/ per se the end value. For example for @[0, 3 .. 10]@, the last value will
-- be @9@. If the 'RangeObj' is empty, or has no (explicit) end value, 'Nothing' is returned.
rangeLastValue :: Enum a => RangeObj a -> Maybe a
rangeLastValue (RangeObj b Nothing e@(Just e'))
  | fromEnum b <= fromEnum e' = e
rangeLastValue (RangeObj b' jt@(Just t') (Just e'))
  | EQ <- c, e >= b = jt -- we reuse the item in the 'RangeObj' to save memory
  | LT <- c, b < e = Just (toEnum (e - ((e - b) `mod` d)))
  | GT <- c, b > e = Just (toEnum (e - ((e - b) `mod` d)))
  where
    c = compare b t
    b = fromEnum b'
    t = fromEnum t'
    e = fromEnum e'
    d = t - b
rangeLastValue _ = Nothing

_fMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
_fMaybe f = go
  where
    go (Just x) (Just y) = Just (f x y)
    go Nothing x = x
    go x _ = x

_sMaybe :: (a -> a -> a) -> a -> Maybe a -> a
_sMaybe f = go
  where
    go x Nothing = x
    go x (Just y) = f x y

_nextdd :: Maybe Int -> Int -> Int -> Int
_nextdd Nothing m1 m2 = max m1 m2
_nextdd (Just dd) m1 m2
  | m2 > m1 = m2 + ((m1 - m2) `mod` dd)
  | otherwise = m1

_subd :: Num a => RangeObj a -> Maybe a
_subd (RangeObj b t _) = subtract b <$> t

_gcd' 0 b = (b, 0, 1)
_gcd' a b = (g, t - (b `div` a) * s, s)
  where
    (g, s, t) = _gcd' (b `mod` a) a

_mergers :: Ordering -> (Int -> Int -> Int, Int -> Int -> Int, Int -> Int -> Int)
_mergers LT = (max, (+), min)
_mergers EQ = (max, (+), min)
_mergers GT = (min, (+), max)

_sameDirMerge :: RangeObj Int -> RangeObj Int -> Ordering -> RangeObj Int
_sameDirMerge r1@(RangeObj b1 t1 e1) r2@(RangeObj b2 t2 e2) o = RangeObj d0 ((d0 +) <$> dd) (_fMaybe m2 e1 e2)
  where
    ~(m1, _, m2) = _mergers o
    dd = _fMaybe (\x -> (*) (signum x) . lcm x) (_subd r1) (_subd r2)
    d0 = m1 b1 b2

_singleRange :: RangeObj Int -> Maybe Int
_singleRange (RangeObj b _ Nothing) = Just b
_singleRange (RangeObj b _ (Just e))
  | b < e = Just b
  | otherwise = Nothing

_withEqMerge :: RangeObj Int -> RangeObj Int -> RangeObj Int
_withEqMerge r1@(RangeObj b1 _ e1) r2@(RangeObj b2 _ _)
  | Just v <- _singleRange r2, not (inRange r1 v) = RangeObj b2 (Just b2) (Just (_sMaybe min b1 e1))
  | otherwise = r2

_difDirMerge :: RangeObj Int -> RangeObj Int -> Ordering -> RangeObj Int
_difDirMerge r1@(RangeObj b1 t1 e1) r2@(RangeObj b2 t2 e2) _ord = undefined

{-_sameDirMerge r1 (RangeObj (_sMaybe ) e2 (Just b1))  -- important to preserve the hops of the second range
where l1 = rangeLastValue r1
      l2 = rangeLastValue r2
      ~(m1, _, m2) = _mergers _ord -}

instance Enum a => Semigroup (RangeObj a) where
  ro1 <> ro2 = toEnum <$> (go (fromEnum <$> ro1) (fromEnum <$> ro2))
    where
      go r1 r2
        | _dir1 == _dir2 = _sameDirMerge r1 r2 _dir1
        | EQ <- _dir1 = _withEqMerge r2 r1
        | EQ <- _dir2 = _withEqMerge r1 r2
        | otherwise = _difDirMerge r1 r2 _dir1
        where
          _dir1 = rangeDirection r1
          _dir2 = rangeDirection r2

-- | Convert the 'RangeObj' to a list of the values defined by the range.
rangeToList ::
  Enum a =>
  -- | The 'RangeObj' item to convert to a list.
  RangeObj a ->
  -- | A list of items the 'RangeObj' spans.
  [a]
rangeToList (RangeObj b Nothing Nothing) = enumFrom b
rangeToList (RangeObj b (Just t) Nothing) = enumFromThen b t
rangeToList (RangeObj b Nothing (Just e)) = enumFromTo b e
rangeToList (RangeObj b (Just t) (Just e)) = enumFromThenTo b t e

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
bodyPat b ns = (ConE 'Nothing, wrapIt (conP 'Just . pure) b (TupP (map VarP ns)))

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

parsePatternSequence :: String -> ParseResult (NonEmpty Pat)
parsePatternSequence s = parsePatWithMode (defaultParseMode {extensions = [EnableExtension ViewPatterns]}) ('(' : s ++ ")") >>= _getPats . toPat

#if MIN_VERSION_template_haskell(2,18,0)
_getPats :: Pat -> ParseResult (NonEmpty Pat)
_getPats (ConP n [] []) | n == '() = fail "no patterns specified"
_getPats (ParensP p) = pure (p :| [])
_getPats (TupP []) = fail "no patterns specified"
_getPats (TupP (p : ps)) = pure (p :| ps)
_getPats _ = fail "not a sequence of patterns"
#else
_getPats :: Pat -> ParseResult (NonEmpty Pat)
_getPats (ConP n []) | n == '() = fail "no patterns specified"
_getPats (ParensP p) = pure (p :| [])
_getPats (TupP []) = fail "no patterns specified"
_getPats (TupP (p : ps)) = pure (p :| ps)
_getPats _ = fail "not a sequence of patterns"
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
rangeToRangeObj ::
  -- | The 'Range' object to convert.
  Range ->
  -- | The equivalent 'RangeObj' with the 'Exp'ressions as parameters.
  RangeObj Exp
rangeToRangeObj (FromR b) = FromRange b
rangeToRangeObj (FromThenR b s) = FromThenRange b s
rangeToRangeObj (FromToR b e) = FromToRange b e
rangeToRangeObj (FromThenToR b s e) = FromThenToRange b s e

-- | Convert a 'RangeObj' to the corresponding 'Exp'ression. This will all the appropriate 'RangeObj' data constructor with the parameters.
rangeObjToExp ::
  -- | A 'RangeObj' with 'Exp'ressions as parameters.
  RangeObj Exp ->
  -- | An 'Exp'ression that contains the data constructor applied to the parameters.
  Exp
rangeObjToExp (RangeObj b t e) = ConE 'RangeObj `AppE` b `AppE` go t `AppE` go e
  where
    go (Just v) = ConE 'Just `AppE` v
    go Nothing = ConE 'Nothing

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

_makeTupleExpressions :: Name -> [Pat] -> Q ([Maybe Exp], [Pat])
_makeTupleExpressions hm = go
  where
    go [] = pure ([], [])
    go (ViewP e p : xs) = (\(es, ps) -> (Just (VarE 'Data.HashMap.Strict.lookup `AppE` e `AppE` VarE hm) : es, conP 'Just [p] : ps)) <$> go xs
    go _ = fail "all items in the hashpat should look like view patterns."

-- | Create a view pattern that maps a HashMap with a locally scoped @hm@ parameter to a the patterns. It thus basically implicitly adds `lookup`
-- to all expressions and matches these with the given patterns. The compilation fails if not all elements are view patterns.
combineHashViewPats ::
  -- | The non-empty list of view patterns that are compiled into a viw pattern.
  NonEmpty Pat ->
  -- | A 'Pat' that is a view pattern that will map a 'Data.HashMap.Strict.HashMap' to make lookups and matches these with the given patterns.
  Q Pat
combineHashViewPats (ViewP e p :| []) = pure (ViewP (AppE (VarE 'Data.HashMap.Strict.lookup) e) (conP 'Just [p]))
combineHashViewPats (x :| xs) = do
  hm <- newName "hm"
  (\(es, ps) -> ViewP (LamE [VarP hm] (TupE es)) (TupP ps)) <$> _makeTupleExpressions hm (x : xs)

-- | A quasiquoter to make `Data.HashMap.Strict.HashMap` lookups more convenient. This can only be used as a pattern.
hashpat :: QuasiQuoter
hashpat = QuasiQuoter failQ ((liftFail >=> combineHashViewPats) . parsePatternSequence) failQ failQ

_rangeCheck :: Int -> Int -> Int -> Bool
_rangeCheck b e x = b <= x && x <= e

_modCheck :: Int -> Int -> Int -> Bool
_modCheck b t x = (x - b) `mod` (t - b) == 0

-- | Determine the number of items for a 'RangeObj', given that can be determined /easily/. This is only for ranges that
-- have an /end/ and where the next item is different from the previous (otherwise this generates an endless list).
rangeLength ::
  Enum a =>
  -- | The 'RangeObj' to determine the number of elements from.
  RangeObj a ->
  -- | The number of elements of the range object, given that can be determined easily; 'Nothing' otherwise.
  Maybe Int
rangeLength = fmap (max 0) . go . fmap fromEnum
  where
    go (RangeObj b t (Just e))
      | Just t' <- t, b == t' = go'
      | otherwise = Just (maybe id (flip div . subtract b) t (e - b) + 1)
      where
        go'
          | b <= e = Nothing
          | otherwise = Just 0
    go _ = Nothing

_forOrdering :: a -> a -> a -> Ordering -> a
_forOrdering lt eq gt = go
  where
    go LT = lt
    go EQ = eq
    go GT = gt

-- | Determine the direction of the range through an 'Ordering' object. For an increasing sequence, 'LT' is used, for a sequence that repeats the element, 'Eq' is returned,
-- and for a descreasing sequence 'GT' is used.
rangeDirection ::
  Ord a =>
  -- | The 'RangeObj' to determine the direction.
  RangeObj a ->
  -- | The direction of the 'RangeObj' as an 'Ordering' object.
  Ordering
rangeDirection (RangeObj _ Nothing _) = LT
rangeDirection (RangeObj b (Just t) _) = compare b t

_incCheck :: Ord a => a -> Maybe a -> Bool
_incCheck _ Nothing = True
_incCheck m (Just n) = m <= n

-- | Check if the given value is in the given 'RangeObj'. This function has some caveats, especially with floating points or other 'Enum' instances
-- where 'fromEnum' and 'toEnum' are no bijections. For example for floating points, `12.5` and `12.2` both map on the same item, as a result, the enum
-- will fail to work properly.
inRange ::
  Enum a =>
  -- | The 'RangeObj' for which we check membership.
  RangeObj a ->
  -- | The element for which we check the membership.
  a ->
  -- 'True' if the element is an element of the 'RangeObj'; 'False' otherwise.
  Bool
inRange r' = go (fromEnum <$> r') . fromEnum
  where
    rangeCheck (RangeObj b _ Nothing) = _forOrdering (b <=) (b ==) (b >=)
    rangeCheck (RangeObj b _ (Just e)) = _forOrdering (_rangeCheck b e) (b ==) (_rangeCheck e b)
    go r@(RangeObj _ Nothing _) = rangeCheck r LT
    go r@(RangeObj b (Just t) e)
      | b == t, _incCheck b e = rangeCheck r (rangeDirection r)
      | b == t = const False
      | otherwise = _both (rangeCheck r (rangeDirection r)) (_modCheck b t)

-- | Flipped alias of 'inRange' that checks if an element is in range of a given 'RangeObj'.
(∈) ::
  Enum a =>
  -- | The given element to check membership for.
  a ->
  -- | The 'RangeObj' object for which we check membership.
  RangeObj a ->
  -- | 'True' if the given element is an element of the given 'RangeObj' object; 'False' otherwise.
  Bool
(∈) = flip inRange

-- | Alias of 'inRange' that checks if an element is in range of a given 'RangeObj'.
(∋) ::
  Enum a =>
  -- | The 'RangeObj' object for which we check membership.
  RangeObj a ->
  -- | The given element to check membership for.
  a ->
  -- | 'True' if the given element is an element of the given 'RangeObj' object; 'False' otherwise.
  Bool
(∋) = inRange

_both :: (a -> Bool) -> (a -> Bool) -> a -> Bool
_both f g x = f x && g x

-- | A 'QuasiQuoter' to parse a range expression to a 'RangeObj'. In case the 'QuasiQuoter' is used for a pattern,
-- it compiles into a /view pattern/ that will work if the element is a member of the 'RangeObj'.
rangepat ::
  -- | The quasiquoter that can be used as expression and pattern.
  QuasiQuoter
rangepat = QuasiQuoter (parsefun id) (parsefun ((`ViewP` conP 'True []) . (VarE 'inRange `AppE`))) failQ failQ
  where
    parsefun pp = (liftFail >=> (pure . pp . rangeObjToExp . rangeToRangeObj)) . parseRange

-- | An alias of the 'rangepat' 'QuasiQuoter', this is used since it looks quite similar to @∊ [a .. b]@,
-- beware that the @ϵ@ in @[ϵ|a .. b|]@ is not an /element of/ character, but the /Greek lunate epsilon/ character
-- which only looks similar.
ϵ ::
  -- | The quasiquoter that can be used as expression and pattern.
  QuasiQuoter
ϵ = rangepat
