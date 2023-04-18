<!-- idris
module README

import Control.Monad.Writer.Interface

import Data.Maybe
import Data.List
import Data.List.Lazy
import Data.Swirl

import System

%default total
-->

# Swirl

A library for streams of monadic actions

## Table of contents

* [Terminology](#what-is-swirl-anyway)
* [Type alignments](#type-alignments)
* Polymorphism in API design
  * [When API is more polymorphic than could](#defaulting-throughout-the-api)
  * [Getting rid of "unsolved type"](#solving-the-unsolved-type-problem)
  * [Interactive editing and typed holes](#defaulting-and-typed-holes)
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
%hint SomeMonadApplicative : Applicative SomeMonad
%hint SomeMonadMonad : Monad SomeMonad
%hint SomeMonadMonadRec : MonadRec SomeMonad
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

### Defaulting and typed holes

Notice that these "default" types pop out in the context of typed holes.
This may surprise a little bit during interactive development.

Say, you, for some reason, attempted to you map the result with a function *after* you applied `forgetR` in them
(you can see more about such combinations in a [special section](#combinations)).

<!-- idris
namespace HoleWithDefault {
-->

```idris
mapped : Swirl SomeMonad SomeError Nat SomeOutput
mapped = mapFst ?mapping_function $ forgetR someSwirl
```

<!-- idris
  }
-->

If you ask the compiler about the type of the `mapping_function` typed hole, it says `() -> Nat`,
since `forgetR` maps the result type to `()` *by default*.

But as soon as you try to actually use the result as some other monoid type, say, `List Nat`,
you can perfectly do it:

<!-- idris
namespace NonHoleWithNonDefault {
-->

```idris
mapped : Swirl SomeMonad SomeError Nat SomeOutput
mapped = mapFst (fromMaybe 5 . List.head') $ forgetR someSwirl
```

<!-- idris
  }
-->

Here we have replaced the hole of type `() -> Nat` with an expression of type `List Nat -> Nat` and all typechecks,
because `()` is chosen only when this type is unsolved.

## Running

Once you have a swirl that cannot raise errors and does not have outputs, you can use the `runSwirl` function.
Basically, it compiles the swirl down to an underlying monad.

```idris
run : Swirl SomeMonad Void SomeResult Void -> SomeMonad SomeResult
run = runSwirl
```

Why do we require outputs to be `Void` here?
It is done to ensure you do not lose you data by mistake,
similarly, say, yo `Monad`'s `(>>)` operation, which takes `m ()` at the left-hand side.
You can either explicitly forget outputs using `forgetO`,
or you can fold outputs using [special operations](#foldings),
or you can [manage outputs](#manage-outputs) by other swirls.

If you don't have all errors managed on the swirl side, you can run it using
`runSwirlE`, which returns `m (Either e r)` instead of just `m r`,
since it does not require the error type to be `Void`.
Despite that, rules for the output type are the same as for `runSwirl`.

### Stack safety

Both `runSwirl` and `runSwirlE` require the underlying monad to implement the `MonadRec` interface.
It is a subinterface of the usual `Monad` one defined in the [`tailrec`](https://github.com/stefan-hoeck/idris2-tailrec/) library.
It describes such monads that support tail recursion,
thus allowing is to run long-running monadic processes in a stack-safe manner.

A lot of standard monads, like `IO`, `Identity`, `List`, `Maybe`, `Either` and standard transformers
like `ReaderT`, `StateT` and `WriterT` support `MonadRec`.
Usually, you can implement `MonadRec` for your own monads.

In case if absolutely needed, one can run swirls in a non-stack-safe manner
for any monad that implements ordinary `Monad` interface.
For this you can use special `NonStackSafe` implementation as the first `auto`-argument:

```idris
unsafe : Swirl SomeMonad Void SomeResult Void -> SomeMonad SomeResult
unsafe = runSwirl @{NonStackSafe}
```

> **Warning**
>
> Please keep in mind that this is highly discouraged and
> is done mainly for compatibility with monads, for which one cannot have a `MonadRec` implementation.

## Basic creation

### Emitting output values

One of the simplest ways of creating a swirl is to emit a single output value:

```idris
singleEleven : Swirl SomeMonad Void () Nat
singleEleven = emit 11
```

> **Note**
>
> Recall that instead of `Void` you can use any type,
> and instead of `()` you can use any monoid.
>
> All such API functions are polymorphic and [have these types as defaults](#defaulting-throughout-the-api).

If you want to emit several values at once, you can use `emits` function:

```idris
threeElevens : Swirl SomeMonad Void () Nat
threeElevens = emits [11, 11, 11]
```

Notice that `emits` takes a lazy list at the input.
There is an eager version called `emits'`, which takes any `Foldable`.

> **Note**
>
> If you want to emit values produced with an effect, see [this part](#effectful-emitting-and-finishing).

Functions described above produce a swirl that ends with a neutral element of a monoid.
If you want to end the produces swirl by some another swirl after the emittings,
you can use their generalised variants:

```idris
prependEleven : Lazy (Swirl SomeMonad e r Nat) -> Swirl SomeMonad e r Nat
prependEleven sw = preEmitTo sw 11
```

```idris
prependElevens : Lazy (Swirl SomeMonad e r Nat) -> Swirl SomeMonad e r Nat
prependElevens sw = preEmitsTo sw [11, 11, 11]
```

### Finishing the swirl

Swirls end with a result or an error value.
Consequently, there are functions that produce successfully or non-successfully ending swirls.

```idris
succeedsInTwelve : Swirl SomeMonad Void Nat Void
succeedsInTwelve = succeed 12
```

```idris
failsInThirteen : Swirl SomeMonad Nat Void Void
failsInThirteen = fail 13
```

Notice that in the failure case the resulting type may be `Void`,
showing that there is not way this swirl can return a resulting values.
As with all other polymorphic API of this type, you can use any any in the place of `Void` when using `succeed` or `fail`.

> **Note**
>
> If you have the result or failure value produced in an effect, see [this part](#effectful-emitting-and-finishing).

### Conditional failure

If you have an immediate `Either` value for containing either a result value or a failure value, you can use `succeedOrFail` function.

Similar function for emitting-or-failing exists and is called `emitOrFail`.
Notice that this function requires a `Monoid` for the resulting type, as `emit` does,
since when it is not failing, there is a need to provide successful end of the swirl.

### Effectful emitting and finishing

All basic creation operations described above take pure values as their main arguments.
Say, `emit` takes a pure output value, `succeed` takes a pure result value and `fail` takes a pure error value.

Since swirl is an effectful collection of values, there may be a need to take such values in an appropriate monadic context.

For this universal functions called `(.by)` and `by` exist, and here how they can be used:

```idris
emitTelling : MonadWriter String m => Swirl m Void () Nat
emitTelling = emit.by $ do
  tell "while emitting a number"
  pure 11
```

```idris
emitInputAndMore : HasIO m => Swirl m Void () String
emitInputAndMore = preEmitTo (emits ["second", "third"]) `by` getLine
  -- Here the resulting swirl would at first emit the result of reading from the console,
  -- and then constant strings `"second"` and `"third"`.
```

```idris
args : HasIO m => Swirl m Void () String
args = emits'.by getArgs
```

There is also a similar, but distinct approach of constructing an effectful swirl,
which looks like traversing a lazy list of effectful actions.
Say, you cannot have `m (LazyList a)` having a `LazyList (m a)` without losing the laziness.
But you can get a swirl over `m` using emitting and `swallowM`:

```idris
aLaLazySequence : Functor m => LazyList (m a) -> Swirl m Void () a
aLaLazySequence = swallowM . emits
```

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

### Design of API

<!-- Copy here "discussion" comment from the `Swirl.idr` -->

### Global questions

<!-- credits for influence of a design to fs2 and GHC's streams -->

<!-- can swirls be run in parallel? -->

<!-- can swirls hold asynchrony? -->

<!-- ## Installation -->
