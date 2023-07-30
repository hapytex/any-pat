{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeApplications #-}

module Data.Pattern.AnySpec where

import Data.Bool(bool)
import Data.Int(Int8, Int16)
import Data.Pattern.Any (RangeObj (FromRange, FromThenRange, FromThenToRange, FromToRange), inRange, rangeToList)
import Data.Word (Word16, Word8)
import Test.Hspec (describe, it)
import Test.Hspec.Discover (Spec)
import Test.QuickCheck (property)
import Test.QuickCheck.Arbitrary (Arbitrary (arbitrary))
import Test.QuickCheck.Gen (oneof)

allSame :: Eq a => RangeObj a -> Bool
allSame (FromThenRange a b) = a == b
allSame (FromThenToRange a b _) = a == b
allSame _ = False

instance Arbitrary a => Arbitrary (RangeObj a) where
  arbitrary = oneof [FromRange <$> arbitrary, FromThenRange <$> arbitrary <*> arbitrary, FromToRange <$> arbitrary <*> arbitrary, FromThenToRange <$> arbitrary <*> arbitrary <*> arbitrary]

testInRange :: forall a. (Enum a, Eq a) => RangeObj a -> a -> Bool
testInRange r x = (x `elem` bool id (take 10) (allSame r) (rangeToList r)) == inRange r x

allInRange :: forall a . (Enum a, Eq a) => RangeObj a -> a -> Bool
allInRange r x = all (inRange r) (bool id (take 10) (allSame r) (rangeToList r))

spec :: Spec
spec = do
  describe "range membership check" $ do
    it "Int8" (property (testInRange @Int8))
    it "Int16" (property (testInRange @Int16))
    it "Word8" (property (testInRange @Word8))
    it "Word16" (property (testInRange @Word16))
    it "Char" (property (testInRange @Char))
  describe "all in range membercheck" $ do
    it "Int8" (property (allInRange @Int8))
    it "Int16" (property (allInRange @Int16))
    it "Word8" (property (allInRange @Word8))
    it "Word16" (property (allInRange @Word16))
    it "Char" (property (allInRange @Char))
