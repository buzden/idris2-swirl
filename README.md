<!-- idris
module README

import Data.Swirl

%default total
-->

# Swirl

A library for streams of monadic actions

## Table of contents

* [Terminology](#what-is-swirl-anyway)
* [Type alignments](#type-alignments)
* [Running](#running)
* [On stack safety](#stack-safety)
* [Creation](#basic-creation)
* [Composition](#combinations)
* [Foldings](#foldings)
* [Error handling](#error-handling-and-bracket-pattern)
* [On design](#design)

## What is swirl anyway?

`Swirl m e r o` is a stream of monadic actions of a monad `m`,
which may produce zero or more values of type `o` along its execution,
and which results either with a value of type `r` or an error of type `e`.

It can be thought as a (potentially) long-running process with intermediate and final results (`o` and `r` respectively).
<!-- TODO some good example here? -->

Also, it can be thought as a lazy collection of type `o`,
which elements can be retrieved sequentially in the context of a monad `m`.

> For example, contents of a whole file can be represented by a `Swirl IO FileError () String`.
> Also, `Swirl Identity Void () a` is essentially equivalent to a `LazyList a`.

### Special cases

As you can see, you can use `Void` data type to disable particular "channel" of information and control.

That is, having `Void` as the error type means that this swirl can't fail by the means of swirl.
Notice, that in a sense the stream still can fail by the means of monad `m`, if it supports this.

> **Note**
>
> Say, execution of `Swirl (Either String) Void Nat Void` still can fail, in a sense, but
> this failure is captured purely inside the underlying monad,
> and thus swirl's facilities of [error handling](#error-handling-and-bracket-pattern)
> cannot be used to [handle](#throwing-and-catching) or recover such errors,
> or to [ensure resource releases](#ensuring-resource-releasing) despite the error.

Having `Void` as the result type means that this stream never ends, at least successfully.
Since the meaning of a swirl is a finite process,
this value cannot be created with a `total` function,
but still it can be created with a `covering` one.
If you want to you express that the process will finish, but you are not interested in a particular result value,
you can use the `Unit` type (which can be written as `()`, as in couple examples above).

Usage of `Void` as the output type effectively simply turns out this facility,
turning such `Swirl` into an analogue of `EitherT e m r`
with extended [error handling](#error-handling-and-bracket-pattern) facilities.

## Type alignments

### Forgetting

You can always turn your swirl's result or output type "off",
i.e. to make it forget its result or output:

<!-- idris
SomeMonad : Type -> Type
%hint SomeMonadFunctor : Functor SomeMonad
SomeError, SomeResult, SomeOutput : Type
-->

```idris
someSwirl : Swirl SomeMonad SomeError SomeResult SomeOutput

forgottenResult : Swirl SomeMonad SomeError () SomeOutput
forgottenResult = forgetR someSwirl

forgottenOutput : Swirl SomeMonad SomeError SomeResult Void
forgottenOutput = forgetO someSwirl
```

Forgetting the result does not make the given swirl to become infinite,
thus the result type is translated to `()`.
All outputs stop emitting, thus we can use `Void` to mark that.

### Defaulting throughout the API

Actually, the whole swirl's API tries to be as polymorphic as reasonable.

For example, result forgetting actually can produce not only a `Unit` type, but any monoid:

```idris
forgottenResult' : Swirl SomeMonad SomeError (List Nat) SomeOutput
forgottenResult' = forgetR someSwirl
```

Output forgetting can produce absolutely any type, not only `Void`:

```idris
forgottenOutput' : Swirl SomeMonad SomeError SomeResult (List Nat)
forgottenOutput' = forgetO someSwirl
```

> **Note**
>
> Many functions working with swirls have this property, i.e.
> we try to return any type when pragmatically one can use `Void` there,
> and we try to return an instance of `Monoid` when one can use `Unit`.
>
> Also, in a lot of places, we will use `Semigroup` and `Monoid` to ask to a way of combining intermediate results.

### Solving the unsolved type problem

As you may know, a lot of polymorphism leads to a problem of unsolved types.

Say, you have a polymorphic producer of a value and a polymorphic consumer combined together.
In this case you may get a "unsolved hole" error.
Consider a silly and artificial, but sufficient example.

```idris
failing "Unsolved hole"

  producer : String -> List a
  consumer : List a -> Nat

  combination : String -> Nat
  combination = consumer . producer
```

In this case you may want to have a defaulting mechanism,
which says which type to use when any type would go.
The library [if-unsolved-implicit](https://github.com/buzden/idris2-if-unsolved-implicit) is used for such mechanism.
With small change of a signature and no change at runtime the example above would compile:

```idris
producer : (0 _ : IfUnsolved a Void) => String -> List a
consumer : List a -> Nat

combination : String -> Nat
combination = consumer . producer
```

> **Note**
>
> This trick is used everywhere in the swirl API.
> In particular, the output type of the `forgetO` function is handled precisely as the polymorphic parameter above.
> As another example, `forgetR` has its result type having `IfUnsolved r ()`
> making it `Unit` by default, or any other `Monoid` on the first demand.

## Running

### Stack safety

## Basic creation

## Combinations

### Map on everything

### Sequence on results

### Manage outputs

### Interleaving and racing

### There should be more

## Foldings

## Error handling and bracket pattern

### Throwing and catching

### Ensuring (resource releasing)

<!-- don't forget mentioning breaking actions like `System.die` -->

## Design

<!-- credits for influence of a design to fs2 and GHC's streams -->

<!-- can swirls be run in parallel? -->

<!-- can swirls hold asynchrony? -->
