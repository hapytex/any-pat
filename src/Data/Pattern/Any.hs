{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Data.Pattern.Any (allPats, patVars, sortedUnion, anypat, maypat) where

import Control.Arrow (first)
import Control.Monad((>=>))
# if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Language.Haskell.Exts.Parser (ParseResult (ParseFailed, ParseOk), parsePat)
import Language.Haskell.Exts.SrcLoc (SrcLoc (SrcLoc))
import Language.Haskell.Meta (toPat)
import Language.Haskell.TH (Body (NormalB), Exp (AppE, ConE, LamCaseE, TupE, VarE), Match (Match), Name, Pat (AsP, BangP, ConP, InfixP, ListP, LitP, ParensP, RecP, SigP, TildeP, TupP, UInfixP, UnboxedSumP, UnboxedTupP, VarP, ViewP, WildP), Q)
import Language.Haskell.TH.Quote (QuasiQuoter (QuasiQuoter))

data HowPass = Simple | AsJust | AsNothing deriving (Eq, Ord, Read, Show)

patVars' :: Pat -> [Name] -> [Name]
patVars' (LitP _) = id
patVars' (VarP n) = (n :)
patVars' (TupP ps) = patVarsF ps
patVars' (UnboxedTupP ps) = patVarsF ps
patVars' (UnboxedSumP p _ _) = patVars' p
patVars' (InfixP p1 _ p2) = patVars' p1 . patVars' p2
patVars' (UInfixP p1 _ p2) = patVars' p1 . patVars' p2
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

patVars :: Pat -> [Name]
patVars = (`patVars'` [])

allPats :: NonEmpty Pat -> Maybe [Name]
allPats (x :| xs)
  | all ((p0 ==) . go) xs = Just p0
  | otherwise = Nothing
  where
    p0 = go x
    go = sort . patVars

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

bodyPat :: [Name] -> (Exp, Pat)
bodyPat [] = (ConE 'False, conP 'True [])
bodyPat [n] = (ConE 'Nothing, conP 'Just [VarP n])
bodyPat ns = (ConE 'Nothing, conP 'Just [TildeP (TupP (map VarP ns))])

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

bodyExp :: [(HowPass, Name)] -> Exp
bodyExp [] = ConE 'True
bodyExp [n] = ConE 'Just `AppE` transName n
bodyExp ns = ConE 'Just `AppE` TupE (map _transName ns)

unionCaseFunc' :: [Pat] -> [Name] -> [[(HowPass, Name)]] -> (Exp, Pat)
unionCaseFunc' ps ns ns' = (LamCaseE (zipWith (\p' n -> Match p' (NormalB (bodyExp n)) []) ps ns' ++ [Match WildP bf []]), p)
  where
    ~(ef, p) = bodyPat ns
    bf = NormalB ef

sortedUnion :: Ord a => b -> c -> (b -> c -> d) -> [(b, a)] -> [(c, a)] -> [(d, a)]
sortedUnion v0 v1 f = go
  where
    go [] ys = map (first (f v0)) ys
    go xa@((b0, x) : xs) ya@((b1, y) : ys) = case compare x y of
      EQ -> (f b0 b1, x) : go xs ys
      GT -> (f v0 b1, y) : go xa ys
      LT -> (f b0 v1, x) : go xs ya
    go xs [] = map (first (`f` v1)) xs

unionCaseFunc :: MonadFail m => Bool -> NonEmpty Pat -> m Pat
unionCaseFunc chk ps@(p0 :| ps')
  | not chk || all fst ns = pure (uncurry ViewP (unionCaseFunc' (p0 : ps') (map snd ns) ns'))
  | otherwise = fail "Not all patterns have the same variable names"
  where
    (ns, ns') = unionPats ps

-- unionCaseFunc' :: [Pat] -> (Exp

parsePatternSequence' :: (Pat -> b) -> (Pat -> a -> b) -> (String -> ParseResult a) -> String -> ParseResult b
parsePatternSequence' zer cmb rec s = case go s of
  p@(ParseFailed (SrcLoc _ _ n) _) -> case splitAt (n-1) s of
                                        (xs, _ : ys) -> cmb <$> go xs <*> rec ys
                                        _ -> zer <$> p
  ParseOk p -> pure (zer p)
  where
    go = fmap toPat . parsePat

parsePatternSequence'' :: String -> ParseResult [Pat]
parsePatternSequence'' = parsePatternSequence' pure (:) parsePatternSequence''

parsePatternSequence :: String -> ParseResult (NonEmpty Pat)
parsePatternSequence = parsePatternSequence' (:| []) (:|) parsePatternSequence''

liftFail :: MonadFail m => ParseResult a -> m a
liftFail (ParseOk x) = pure x
liftFail (ParseFailed _ s) = fail s

failQ :: a -> Q b
failQ = const (fail "The QuasiQuoter can only work to generate code as pattern.")

anypat :: QuasiQuoter
anypat = QuasiQuoter failQ ((liftFail >=> unionCaseFunc True) . parsePatternSequence) failQ failQ

maypat :: QuasiQuoter
maypat = QuasiQuoter failQ ((liftFail >=> unionCaseFunc False) . parsePatternSequence) failQ failQ
