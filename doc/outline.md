---
title: any-pat: a poor man's solution to group patterns
author: Willem Van Onsem
---

# Introduction

Haskell aims to be a very concise language where repitive code is excluded as much as possible. There are however still cases where the same expression is used for different patterns. Indeed, for example if we want to specify the blocks for different elements:

...

A popular programming task is *FizzBuzz*, where one enters a number, and the program prints all numbers up to that number. If the item is however dividable by three, it prints `Fizz`, if it is dividable by five, it prints `Buzz`, and if it is dividable both by three and five, it prints `FizzBuzz`. We can implement this in Haskell with:

```
fizzBuzz :: Int -> String
fizzBuzz n
  | n `mod` 15 = "FizzBuzz"
  | n `mod` 3 = "Fizz"
  | n `mod` 5 = "Buzz"
  | otherwise = show n
```

this however introduces extra syntax: we now have a variable named `n` for example, that is linked

In this paper, we discuss a few `QuasiQuoter`s that can make functions shorter, or at least the code more self-explaining. For example `rangepat` can work with a specified *range* and allows us to define the *FizzBuzz* solution as:

```
fizzBuzz :: Int -> String
fizzBuzz [rangepat|0, 15 ..|] = "FizzBuzz"
fizzBuzz [rangepat|0, 3 ..|] = "Fizz"
fizzBuzz [rangepat|0, 5 ..|] = "Buzz"
fizzBuzz n = show n
```

but it is still not completely straightforward, since we have to do the math that the intersection of the two ranges `[0, 3 ..]` and `[0, 5 ..]` is `[0, 15 ..]`, we can simplify this further to:

```
fizzBuzz :: Int -> String
fizzBuzz [rangepat|[0, 3 ..] <> [0, 5 ..]|] = "FizzBuzz"
fizzBuzz [rangepat|0, 3 ..|] = "Fizz"
fizzBuzz [rangepat|0, 5 ..|] = "Buzz"
fizzBuzz n = show n
```

or:

```
three :: RangeObj Int
three = [rangepat|0, 3 ..|]

five :: RangeObj Int
five = [rangepat|0, 3 ..|]

fizzBuzz :: Int -> String
fizzBuzz [rangepat|three <> five|] = "FizzBuzz"
fizzBuzz [rangepat|three|] = "Fizz"
fizzBuzz [rangepat|five|] = "Buzz"
fizzBuzz n = show n
```

# View patterns and quasi quoters

Functions in Haskell work with pattern matching. A function typically constists of a number of clauses with in the "head" patterns for the parameters that can contain variable names, and in the body expressions that work with variables in these patterns and variables define in an outer scope. The line will "fire" in case the pattern matches, and it the result will be the expression where it uses the matching variables from the pattern in the expression.

Simple pattern syntax consists out of variables, and patterns with a data constructor with patterns as parameters. But several extensions have been added including *view patterns*. A view pattern is of the form <code><i>e</i> -&gt; <i>p</i></code> with *`e`* a function that takes one parameter, and `p` a pattern. In a view pattern, the function is called on that parameter, and the result is matched on a certain *`p`*, the clause fires. The type of the pattern *`p`* thus has to match the type of the result of the function *`e*`.

*Quasi quoters* are another extension of Haskell, it allows to parse an arbitrary string, and the quasi quoter then transforms this into arbitrary code. This can be done in several modes: as an expression, a pattern, a type or a declaration. Depending on where the quasi quoter is used, it picks a different mode. Not all quasi quoters have functions for all modes, that seldomly the case. Quasi quoters are often used to allow programmers to write complicated and large code blocks in a compact "sub language", for example the `rex` package allows to write regular expressions. At compile time, the regex is then validated and converted into Haskell code, which can for example already (partially) optimize the regex handling. Therefore quasi quoters are often used to validate values at compile time, and work with a compact language that can produce code blocks that might be harder to inspect and validate. It is thus a mechanism that makes implementing sublanguages convenient.

In this paper we combine the above extensions, by implementing a quasi quoters that can be used both to generate expressions or patterns. In this case we generate view patterns that aim to work with shorter patterns.

# Range objects

Haskell has syntax for ranges. Indeed, the `Enum` typeclass exports four functions to work with ranges: `enumFrom :: Enum a => a -> [a]`, `enumFromThen :: Enum a => a -> a -> [a]`, `enumFromThenTo :: Enum a => a -> a -> a -> [a]`, and `enumFromTo :: Enum a => a -> a -> [a]`. Haskell has range syntax that maps on these functions: `[1, 3 .. 10]` is mapped on `enumFromThenTo 1 3 10`, which will then generate a list.

The fact that the ranges map to function calls that produce lists is perhaps not ideal in a lot of scenarios. While generating a list might indeed be a common use case, we might be interested in other use cases. For example checking if an item is a *member* of a given range. In Python, `range` and `slice` are builtin classes that are used to specify ranges. The `range` object is commonly used to enumerate over a range with a start, stop and step parameter, whereas `slice`s have special syntax for *subscripting*. A `range` object however has some extra use-cases. For example one can perform membership checks, for integers this can be done in constant time. One can also determine the number of elements in a range without having to generate the list in the first place.

This thus means that a range object `RangeFromThenTo 1 3 10` is "richer" than a list `[1, 3, 5, 7, 9]`.

## Membership checks



## Floating points and other caveats

Haskell's `Enum` instances have some caveats though, and therefore `rangepat` can have unwanted or at least unexpected behavior. One if the problems is that `fromEnum` maps to `Int`, this means that the function is guaranteed not to be *injective* for certain types: the number of values the range spans over, is larger than the `Int`. Indeed, for example `Integer` can store any possible integral value[^1], whereas `Int` is on most systems a 32-bit integer or 64-bit integer. This means that there are two (different) `Integer` values that map on the same `Int` value with `fromEnum`. This thus means that for these two values, the `RangeObj` will not make a difference in membership check, this might not be a problem for *some* `RangeObj` objects, but very likely for others it will. For `Float` and `Double` this is very clear since `fromEnum 1.2` and `fromEnum 1.5` for example all map to one, and it thus acts as a `truncate`.

For floating point numbers, there are more severe problems. A range object assumes that the values are *equidistant*, indeed `[a, a+b ..]` includes all values $$a + n\cdot{} b$$ with $n$ a natural number (including zero), but floating points do not define values in an equidistant manner: eventually the exponent increases and so floating point values become scarser (???) as the value increases. Eventually this means that a range for `[1 ..]` will not contain all integral numbers, since there are no floating point values to represent these numbers, and therefore the `[1 ..]`.

[^1] Unless the integral value can no longer be stored in the available memory.
