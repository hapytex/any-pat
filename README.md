# any-pat
[![Build Status of the package by GitHub actions](https://github.com/hapytex/any-pat/actions/workflows/build-ci.yml/badge.svg)](https://github.com/hapytex/any-pat/actions/workflows/build-ci.yml)
[![Hackage version badge](https://img.shields.io/hackage/v/any-pat.svg)](https://hackage.haskell.org/package/any-pat)

Combine multiple patterns in a single pattern and range membership checks.

## Usage

This package ships with three `QuasiQuoter`s: `anypat`, `maypat` and `rangepat`.

### `anypat` and `maypat`

`anypat` and `maypat` have the same purpose. Defining multiple possible patterns in a single clause. Indeed, consider the following example:

```
mightBe ∷ (Int, a, a) → Maybe a
mightBe (0, a, _) = Just a
mightBe (1, _, a) = Just a
mightBe _ = Nothing
```

the first two clauses have some repetitive elements. We can combine the two through the `anypat` or `maypat` quasiquoter:

```
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}

mightBe ∷ (Int, a, a) → Maybe a
mightBe [anypat|(0, a, _), (1, _, a)|] = Just a
mightBe _ = Nothing
```

or with `maypat`:

```
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}

mightBe ∷ (Int, a, a) → Maybe a
mightBe [maypat|(0, a _), (1, _, a), _|] = a
```

and that's it. No, there is no need to wrap `a` in a `Just` in the last code example.

We can also use the `maypat` and `anypat` to generate expressions, with:

```
{-# LANGUAGE QuasiQuotes #-}

mightBe ∷ (Int, a, a) → Maybe a
mightBe = [maypat|(0, a _), (1, _, a), _|]
```

If it is used as pattern, the `ViewPatterns` language extension should be enabled. Furthermore the `QuasiQuotes` extension should of course be enabled for any use of the quasi quoters.

The difference between the two QuasiQuoters (`anypat` and `maypat`) is in how they handle variable names. Variable names defined in the patterns are used in the body of the function, so it makes sense that if the clause "fires", they have a value. This means that a reasonable condition is that all patterns have the same set of variable names and that the variable names have the same type.

The `anypat` requires that all patterns have the same variables. So, `[anypat|(0, a), (1, _)|]` will raise an error *at compile time*. This is because if the second pattern `(1, _)` "fires", it will not provide a value for the a variable. This is a problem, because the body of the function expects a value for the a variable.

One possible solution would be to pass a value like `undefined` or an infinite loop (i.e. `y = let x = x in x` for example) as the value for the a variable. However, this is not a good solution, because it would cause a lot of trouble.

Therefore, `maypat` comes with a different solution. It performs analysis on the variables used in the different patterns. Variables that occur in all patterns are simply passed with the real value. Variables that occur only in a (strict) subset of the listed patterns are passed as a `Maybe a` value. If the first pattern that "fires" (left-to-right) for the value has that variable, it will be wrapped in a `Just`. Otherwise, it will pass `Nothing` as that variable.

Some functions in the `base` package, for example, have a simple equivalent with `anypat` or `maypat`, for example [**`listToMaybe ∷ [a] → Maybe a`**](https://hackage.haskell.org/package/base-4.18.0.0/docs/Data-Maybe.html#v:listToMaybe) can be implemented as:

```
{-# LANGUAGE QuasiQuotes #-}

listToMaybe ∷ [a] → Maybe a
listToMaybe = [maypat|(a:_), _|]
```

### `hashpat`

`hashpat` is a quasi quoter for patterns to make lookups on `HashMap`s more convenient. Indeed, we can for example create a function:

```
sumab ∷ HashMap String Int → Int
sumab [hashpat|"a" → a, "b" → b|] = a + b
sumab _ = 0
```

this will "fire" the first clause given the `HashMap` has both an `"a"` and `"b"` as key, and it will thus perform the corresponding lookups and unify `a` and `b` with the corresponding output. This thus means that a `HashMap` that contains `"a"` and `"b"`, we will sum up the values for that `HashMap`, and if not return `0`.

The keys can take arbitrary expressions, and we thus can for example use `"a" ++ "b"` as key. Furthermore we can use an arbitrary pattern at the right side of the arrow, such that it only "fires" if it matches a given pattern. For example:

```
bifanothing ∷ HashMap String (Maybe Int) → Int
bifanothing [hashpat|"a" ++ "b" → Nothing, "b" → Just x|] = x
bifanothing _ = 0
```

this will thus fire the first clause if the `HashMap` has a key `"ab"` that maps to `Nothing`, and a key `"b"` that maps to a `Just x`, and in that case return the `x`. Essentially it thus compiles the pattern, which is a sequence of view patterns into a function that will perform `lookup`s and then pattern match on the result of these lookups.

Since `HashMap`s with strings as keys are common, and unpacking these into variables with the same name is a common usecase, one can also just list variable names. These will then be translated into lookups with strings, or if the `OverloadedStrings` extension is enabled, a `HashMap` where the key type is both a member of `Hashable` and `IsString`:

```
{-# LANGUAGE OverloadedStrings, QuasiQuotes, ViewPatterns #-}

sumab :: (Hashable s, IsString s, Num n) => HashMap s n -> n
sumab [hashpat|a, b|] = a + b
sumab _ = 0
```

this thus makes it possible to handle optional named paramters, although these all have to have the same type of corresponding values. The dictionary can thus to some extend ???

### `rangepat`

`rangepat` defines patterns for range memberships. For example:

```
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ViewPatterns #-}

isInRange ∷ Int → Bool
isInRange [rangepat|0, 5 .. 50|] = True
isInRange _ = False
```

This will check in constant time if the number is in the given range (here `[0, 5 .. 50]`). The pattern has however some caveats, especially with floating point numbers, and likely any other type where `fromEnum` en `toEnum` are not *bijective*.

## Package structure

The package has only one module: `Data.Pattern.Any` that exports the two `QuasiQuoter`s named `anypat` and `maypat` together with some utility functions to obtain the variables names from a pattern.

## Behind the curtains

The package transforms a sequence of patterns to a *view pattern*, or an *expression*, depending on where the quasi quoter is used. If we create a pattern <code>[anypat|p<sub>1</sub>, p<sub>2</sub>, &hellip;, p<sub>n</sub>|]</code>, it will create a view pattern that looks like:

<pre><code>\case
  p<sub>1</sub> &rarr; Just n&#8407;
  p<sub>2</sub> &rarr; Just n&#8407;
  &vellip;   &vellip;    &vellip;
  p<sub>n</sub> &rarr; Just n&#8407;
  _ &rarr; Nothing</code></pre>

with <code>n&#8407;</code> the (sorted) tuple of names found in the patterns. It then makes a view pattern <code>e &rarr; n&#8407;</code> that thus maps the found values for the variables to the names that can then be used in the body of the function.

There are some (small) optimizations that for example are used if no variable names are used in the patterns, or only one. If a wildcard pattern is used, it can also omit the `Maybe` data type.

For `rangepat`, it first converts the range to a `RangeObj`, and then checks membership in constant time (given we assume that operations on `Int` run in constant time).

## `any-pat` is ***inferred** safe* Haskell

It can not be marked safe, since the modules it depends on are not marked safe, but its safeness can be inferred by the compiler.

## Contribute

You can contribute by making a pull request on the [*GitHub
repository*](https://github.com/hapytex/any-pat).

You can contact the package maintainer by sending a mail to
[`hapytexeu+gh@gmail.com`](mailto:hapytexeu+gh@gmail.com).

---

This package is dedicated to professor <abbr title="for the Pat-rick of course.">**P̲a̲t̲**rick</abbr> De Causmaecker, who taught most of the basic programming courses at university, not Haskell however.
