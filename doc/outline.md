---
title: any-pat: a poor man's solution to group patterns
author: Willem Van Onsem
---

# Introduction

Haskell aims to be a very concise language where repitive code is excluded as much as possible. There are however still cases where the same expression is used for different patterns. Indeed, for example if we want to specify the blocks for different elements:

```
data Element = H | He | Li | Be | B | C | N | O | F | Ne
data Block = BlockS | BlockP | BlockD | BlockF

block :: Element -> Block
block H = BlockS
block He = BlockS
block Li = BlockS
block Be = BlockS
block B = BlockP
block C = BlockP
block N = BlockP
block O = BlockP
block F = BlockP
block Ne = BlockP
```

here several lines of code have most elements in common. A simple way to improve this is with guards that perform range checks, like:

block :: Element -> Block
block e
  | H <= e && e <= Be = BlockS
  | B <= e && e <= Ne = BlockP
```

this however introduces extra syntax: we now have a variable named `e` for example we do not per se need in the body of the functions. 

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

A simple

## Floating points and other caveats

Haskell's `Enum` instances have some caveats though. 