# any-pat
[![Build Status of the package by GitHub actions](https://github.com/hapytex/any-pat/actions/workflows/build-ci.yml/badge.svg)](https://github.com/hapytex/any-pat/actions/workflows/build-ci.yml)
[![Hackage version badge](https://img.shields.io/hackage/v/any-pat.svg)](https://hackage.haskell.org/package/any-pat)

Combine multiple patterns in a single pattern.

## Usage

This package ships with two `QuasiQuoter`s: `anypat` and `maypat`. Both have the same purpose. Defining multiple possible patterns in a single clause. Indeed, consider the following example:

```
mightBe :: (Int, a, a) -> Maybe a
mightBe (0, a, _) = Just a
mightBe (1, _, a) = Just a
mightBe _ = Nothing
```

the first two clauses have some repetitive elements. We can combine the two through the `anypat` or `maypat` quasiquoter:

```
{-# LANGUAGE QuasiQuoters #-}
{-# LANGUAGE ViewPatterns #-}

mightBe :: (Int, a, a) -> Maybe a
mightBe [anypat|(0, a, _), (1, _, a)|] = Just a
mightBe _ = Nothing
```

or with `maypat`:

```
{-# LANGUAGE QuasiQuoters #-}
{-# LANGUAGE ViewPatterns #-}

mightBe :: (Int, a, a) -> Maybe a
mightBe [maypat|(0, a _), (1, _, a), _|] = a
```

and that's it. No, there is no need to wrap `a` in a `Just` in the last code example.

The difference between the two `QuasiQuoter`s (`anypat` and `maypat`) are the handling of variable names. Variable names defined in the pattern(s) are used in the body of the function, so it makes sense that if the clause "fires", these have a value. This thus means that a reasonable condition is that all patterns have the same set of variable names and that the variable names have the same type. The `anypat` requires that all patterns have the same variables, so `[anypat|(0, a), (1, _)|]` will raise an error: if the second pattern `(1, _)` would "fire" it would not provide a value for the `a` variable, and then we have a problem. A possible solution would be to pass a value like `undefined`, or an infinite loop (i.e. `y = let x = x in x` for example) as value, but this looks like something that would only cause a lot of trouble.

Therefore `maypat` comes with a different solution: it performs analysis on the variables used in the different patterns. Variables that occur in all patterns are just passed with the real value, variables that occur only in a (strict) subset of the listed patterns, are passed as a `Maybe a` value with `Just x` in case the first pattern that "fires" (left-to-right) for the value has that variable, it will be wrapped in a `Just`, and otherwise, it will pass `Nothing` as that variable.

## Package structure


## `any-pat` is **inferred** *safe* Haskell

## Contribute

You can contribute by making a pull request on the [*GitHub
repository*](https://github.com/hapytex/any-pat).

You can contact the package maintainer by sending a mail to
[`hapytexeu+gh@gmail.com`](mailto:hapytexeu+gh@gmail.com).

