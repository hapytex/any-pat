{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}

module Data.Pattern.Any (allPats, patVars, sortedUnion, anypat, maypat) where

import Control.Arrow (first)
import Control.Monad.Fail (MonadFail)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Debug.Trace (traceShow)
import Language.Haskell.Exts.Parser (ParseResult (ParseFailed, ParseOk), parsePat)
import Language.Haskell.Exts.SrcLoc (SrcLoc (SrcLoc))
import qualified Language.Haskell.Exts.Syntax as S
import Language.Haskell.Meta (toPat)
import Language.Haskell.TH (Body (NormalB), Exp (AppE, ConE, LamCaseE, TupE, VarE), Match (Match), Name, Pat (AsP, BangP, ConP, InfixP, ListP, LitP, ParensP, RecP, SigP, TildeP, TupP, UInfixP, UnboxedSumP, UnboxedTupP, VarP, ViewP, WildP))
import Language.Haskell.TH.Quote (QuasiQuoter (QuasiQuoter))

data HowPass = Simple | AsJust | AsNothing deriving (Eq, Ord, Read, Show)

patVars :: Pat -> [Name]
patVars = (`go` [])
  where
    go (LitP _) = id
    go (VarP n) = (n :)
    go (TupP ps) = go' ps
    go (UnboxedTupP ps) = go' ps
    go (UnboxedSumP p _ _) = go p
    go (ConP _ _ ps) = go' ps
    go (InfixP p1 _ p2) = go p1 . go p2
    go (UInfixP p1 _ p2) = go p1 . go p2
    go (ParensP p) = go p
    go (TildeP p) = go p
    go (BangP p) = go p
    go (AsP n p) = (n :) . go p
    go WildP = id
    go (RecP _ ps) = go' (map snd ps)
    go (ListP ps) = go' ps
    go (SigP p _) = go p
    go (ViewP _ p) = go p
    go' = foldr ((.) . go) id

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

bodyPat :: [Name] -> (Exp, Pat)
bodyPat [] = (ConE 'False, ConP 'True [] [])
bodyPat [n] = (ConE 'Nothing, ConP 'Just [] [VarP n])
bodyPat ns = (ConE 'Nothing, ConP 'Just [] [TildeP (TupP (map VarP ns))])

transName' :: HowPass -> Name -> Exp
transName' Simple = VarE
transName' AsNothing = const (ConE 'Nothing)
transName' AsJust = AppE (ConE 'Just) . VarE

transName :: (HowPass, Name) -> Exp
transName = uncurry transName'

bodyExp :: [(HowPass, Name)] -> Exp
bodyExp [] = ConE 'True
bodyExp [n] = ConE 'Just `AppE` transName n
bodyExp ns = ConE 'Just `AppE` TupE (map (Just . transName) ns)

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
  ParseFailed (SrcLoc _ _ n) _ -> let ~(xs, ~(_ : ys)) = splitAt (n - 1) s in cmb <$> go xs <*> rec ys
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

failQ :: Q a
failQ = fail "The QuasiQuoter can only work to generate code as pattern."

anypat :: QuasiQuoter
anypat = QuasiQuoter failQ ((liftFail >=> unionCaseFunc True) . parsePatternSequence) failQ failQ

maypat :: QuasiQuoter
maypat = QuasiQuoter failQ ((liftFail >=> unionCaseFunc False) . parsePatternSequence) failQ failQ
