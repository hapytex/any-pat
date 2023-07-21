module Data.Pattern.Any (allPats, patVars) where

import Data.List(sort)
import Data.List.NonEmpty(NonEmpty((:|)))
import Language.Haskell.TH(Name, Pat(LitP, VarP, TupP, UnboxedTupP, UnboxedSumP, ConP, InfixP, UInfixP, ParensP, TildeP, BangP, AsP, WildP, RecP, ListP, SigP, ViewP))

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

-- unionFunc :: [Pat] -> Exp
-- unionFunc a

