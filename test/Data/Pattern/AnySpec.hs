{-# LANGUAGE ExplicitForAll, TypeApplications #-}

module Data.Pattern.AnySpec where

import Data.Word(Word8, Word16)
import Data.Pattern.Any(RangeObj(FromRange, FromThenRange, FromToRange, FromThenToRange), rangeToList, inRange)
import Test.Hspec(describe, it)
import Test.Hspec.Discover(Spec)
import Test.QuickCheck(property)
import Test.QuickCheck.Arbitrary(Arbitrary(arbitrary))
import Test.QuickCheck.Gen(oneof)

instance Arbitrary a => Arbitrary (RangeObj a) where
  arbitrary = oneof [FromRange <$> arbitrary, FromThenRange <$> arbitrary <*> arbitrary, FromToRange <$> arbitrary <*> arbitrary, FromThenToRange <$> arbitrary <*> arbitrary <*> arbitrary]


testInRange :: forall a . (Enum a, Eq a) => RangeObj a -> a -> Bool
testInRange r x = (x `elem` rangeToList r) == inRange r x

spec :: Spec
spec = describe "range membership check" $ do
    it "Word8" (property (testInRange @Word8))
    it "Char" (property (testInRange @Char))
    it "Word16" (property (testInRange @Int))
