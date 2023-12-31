{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Pattern.AnySpec where

import Data.Bool (bool)
import Data.Int (Int16, Int8)
import Data.Pattern.Any (RangeObj, inRange, rangeLastValue, rangeLength, rangeToList, rangepat, pattern FromRange, pattern FromThenRange, pattern FromThenToRange, pattern FromToRange)
import Data.Proxy (Proxy (Proxy))
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

limitRangeList :: (Enum a, Eq a) => RangeObj a -> [a]
limitRangeList r = bool id (take 10) (allSame r) (rangeToList r)

instance Arbitrary a => Arbitrary (RangeObj a) where
  arbitrary = oneof [FromRange <$> arbitrary, FromThenRange <$> arbitrary <*> arbitrary, FromToRange <$> arbitrary <*> arbitrary, FromThenToRange <$> arbitrary <*> arbitrary <*> arbitrary]

testInRange :: forall a. (Enum a, Eq a) => RangeObj a -> a -> Bool
testInRange r x = (x `elem` limitRangeList r) == inRange r x

lastValueTest :: (Enum a, Eq a) => RangeObj a -> Bool
lastValueTest r
  | Just l <- rangeLastValue r = l == last (limitRangeList r)
  | otherwise = True

allInRange :: forall a. (Enum a, Eq a) => RangeObj a -> Bool
allInRange r = all (inRange r) (limitRangeList r)

rangepatFromCheck :: forall a. Enum a => a -> a -> Bool
rangepatFromCheck b x = f x == inRange (FromRange b) x
  where
    f [rangepat|b ..|] = True
    f _ = False

rangepatFromThenCheck :: forall a. Enum a => a -> a -> a -> Bool
rangepatFromThenCheck b s x = f x == inRange (FromThenRange b s) x
  where
    f [rangepat|b, s .. |] = True
    f _ = False

rangepatFromToCheck :: forall a. Enum a => a -> a -> a -> Bool
rangepatFromToCheck b e x = f x == inRange (FromToRange b e) x
  where
    f [rangepat|b .. e|] = True
    f _ = False

rangepatFromThenToCheck :: forall a. Enum a => a -> a -> a -> a -> Bool
rangepatFromThenToCheck b s e x = f x == inRange (FromThenToRange b s e) x
  where
    f [rangepat|b, s .. e|] = True
    f _ = False

rangepatCheck :: forall a. (Arbitrary a, Enum a, Show a) => Proxy a -> Spec
rangepatCheck _ = do
  it "from" (property (rangepatFromCheck @a))
  it "fromThen" (property (rangepatFromThenCheck @a))
  it "fromThenTo" (property (rangepatFromThenToCheck @a))
  it "fromTo" (property (rangepatFromToCheck @a))

rangeLengthCheck :: Enum a => RangeObj a -> Bool
rangeLengthCheck r
  | Just n <- rangeLength r = length (rangeToList r) == n
  | otherwise = True

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
  describe "rangeLength" $ do
    it "Int8" (property (rangeLengthCheck @Int8))
    it "Int16" (property (rangeLengthCheck @Int16))
    it "Word8" (property (rangeLengthCheck @Word8))
    it "Word16" (property (rangeLengthCheck @Word16))
    it "Char" (property (rangeLengthCheck @Char))
  describe "rangeLastValue" $ do
    it "Int8" (property (lastValueTest @Int8))
    it "Int16" (property (lastValueTest @Int16))
    it "Word8" (property (lastValueTest @Word8))
    it "Word16" (property (lastValueTest @Word16))
    it "Char" (property (lastValueTest @Char))
  describe "range pattern checks" $ do
    describe "Int8" (rangepatCheck (Proxy :: Proxy Int8))
    describe "Int16" (rangepatCheck (Proxy :: Proxy Int16))
    describe "Word8" (rangepatCheck (Proxy :: Proxy Word8))
    describe "Word16" (rangepatCheck (Proxy :: Proxy Word16))
    describe "Char" (rangepatCheck (Proxy :: Proxy Char))
