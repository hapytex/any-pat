{-# LANGUAGE TemplateHaskellQuotes #-}

module Data.Pattern.Any (allPats, patVars) where

import Data.List(sort)
import Data.List.NonEmpty(NonEmpty((:|)))
import Debug.Trace(traceShow)
import Language.Haskell.TH(Body(NormalB), Exp(AppE, ConE, LamCaseE, TupE, VarE), Match(Match), Name, Pat(LitP, VarP, TupP, UnboxedTupP, UnboxedSumP, ConP, InfixP, UInfixP, ParensP, TildeP, BangP, AsP, WildP, RecP, ListP, SigP, ViewP))
import qualified Language.Haskell.Exts.Syntax as S
import Language.Haskell.Meta (toPat)
import Language.Haskell.Exts.Parser(ParseResult(ParseOk, ParseFailed), parsePat)
import Language.Haskell.Exts.SrcLoc(SrcLoc(SrcLoc))
import Language.Haskell.TH.Quote(QuasiQuoter(QuasiQuoter))

patVars :: Pat -> [Name]
patVars = (`go` [])
  where go (LitP _) = id
        go (VarP n) = (n:)
        go (TupP ps) = go' ps
        go (UnboxedTupP ps) = go' ps
        go (UnboxedSumP p _ _) = go p
        go (ConP _ _ ps) = go' ps
        go (InfixP p1 _ p2) = go p1 . go p2
        go (UInfixP p1 _ p2) = go p1 . go p2
        go (ParensP p) = go p
        go (TildeP p) = go p
        go (BangP p) = go p
        go (AsP n p) = (n:) . go p
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
  where p0 = go x
        go = sort . patVars

bodyPat :: [Name] -> (Exp, Exp, Pat)
bodyPat [] = (ConE 'True, ConE 'False, ConP 'True [] [])
bodyPat [n] = (ConE 'Just `AppE` VarE n, ConE 'Nothing, ConP 'Just [] [VarP n])
bodyPat ns = (ConE 'Just `AppE` TupE (map (Just . VarE) ns), ConE 'Nothing, ConP 'Just [] [TildeP (TupP (map VarP ns))])

unionCaseFunc' :: [Pat] -> [Name] -> (Exp, Pat)
unionCaseFunc' ps ns = (LamCaseE (map (\p -> Match p b0 []) ps ++ [Match WildP b1 []]), p)
  where ~(e0, e1, p) = bodyPat ns
        b0 = NormalB e0
        b1 = NormalB e1


unionCaseFunc :: NonEmpty Pat -> Pat
unionCaseFunc ps@(p0 :| ps')
  | Just ns <- allPats ps = uncurry ViewP (unionCaseFunc' (p0 : ps') ns)
  | otherwise = undefined

-- unionCaseFunc' :: [Pat] -> (Exp

parsePatternSequence' :: (Pat -> b) -> (Pat -> a -> b) -> (String -> ParseResult a) -> String -> ParseResult b
parsePatternSequence' zer cmb rec s = case go s of
    ParseFailed (SrcLoc _ _ n) _ -> let ~(xs, ~(_:ys)) = splitAt (n-1) s in cmb <$> go xs <*> rec ys
    ParseOk p -> pure (zer p)
  where go = fmap toPat . parsePat

parsePatternSequence'' :: String -> ParseResult [Pat]
parsePatternSequence'' = parsePatternSequence' pure (:) parsePatternSequence''

parsePatternSequence :: String -> ParseResult (NonEmpty Pat)
parsePatternSequence = parsePatternSequence' (:| []) (:|) parsePatternSequence''

liftFail :: MonadFail m => ParseResult a -> m a
liftFail (ParseOk x) = pure x
liftFail (ParseFailed _ s) = fail s

anyqq :: QuasiQuoter
anyqq = QuasiQuoter undefined (fmap unionCaseFunc . liftFail . parsePatternSequence) undefined undefined
