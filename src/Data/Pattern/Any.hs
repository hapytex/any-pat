{-# LANGUAGE TemplateHaskellQuotes #-}

module Data.Pattern.Any (allPats, patVars) where

import Data.List(sort)
import Data.List.NonEmpty(NonEmpty((:|)))
import Language.Haskell.TH(Body(NormalB), Exp(AppE, ConE, LamCaseE, TupE, VarE), Match(Match), Name, Pat(LitP, VarP, TupP, UnboxedTupP, UnboxedSumP, ConP, InfixP, UInfixP, ParensP, TildeP, BangP, AsP, WildP, RecP, ListP, SigP, ViewP))
import qualified Language.Haskell.Exts.Syntax as S
import Language.Haskell.Meta (toPat)

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

unionCaseFunc :: [Pat] -> (Exp, Pat)
unionCaseFunc ps@(p0:ps')
  | Just ns <- allPats (p0 :| ps') = let b = NormalB (ConE 'Just `AppE` TupE (map (Just . VarE) ns)) in (LamCaseE (map (\p -> Match p b []) ps ++ [Match WildP (NormalB (ConE 'Nothing)) []]), p0)
  | otherwise = undefined

{-
nameToName :: S.Name a -> Name
nameToName (S.Ident _ n) = mkName n
nameToName (S.Symbol _ n) = mkName n

patToPat :: S.Pat a -> Pat
patToPat (S.PVar _ n) = VarP (nameToName n)
patToPat (S.PLit _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
patToPat (S. _) =
-}
