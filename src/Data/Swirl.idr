module Data.Swirl

import Control.MonadRec
import Control.WellFounded

import public Language.Implicits.IfUnsolved

%default total

export
data Swirl : (Type -> Type) -> (result, output : Type) -> Type where
  Done   : r -> Swirl m r o
  Yield  : o -> Lazy (Swirl m r o) -> Swirl m r o
  Effect : m (Lazy (Swirl m r o)) -> Swirl m r o

-- `m (Lazy ...)` exploits totality checker's bug to make the type as if it's strictly positive.

--- Basic mapping ---

%inline
mapLazy : (a -> b) -> Lazy a -> Lazy b
mapLazy f = delay . f . force

export
Functor m => Bifunctor (Swirl m) where
  bimap fr fo $ Done r       = Done $ fr r
  bimap fr fo $ Yield o rest = Yield (fo o) (bimap fr fo rest)
  bimap fr fo $ Effect ef    = Effect $ ef <&> mapLazy (assert_total $ bimap fr fo)

export
mapCtx : Functor m => (forall a. m a -> n a) -> Swirl m r o -> Swirl n r o
mapCtx f $ Done x     = Done x
mapCtx f $ Yield x ys = Yield x $ mapCtx f ys
mapCtx f $ Effect xs  = Effect $ f $ xs <&> mapLazy (assert_total $ mapCtx f)

--- Basic combinators ---

export
concatWithRes : Functor m => (resultComp : rl -> rr -> r) -> Swirl m rl o -> Lazy (Swirl m rr o) -> Swirl m r o
concatWithRes fr (Done r)     ys = mapFst (fr r) ys
concatWithRes fr (Yield x xs) ys = Yield x $ concatWithRes fr xs ys
concatWithRes fr (Effect xs)  ys = Effect $ xs <&> mapLazy (\xs => assert_total concatWithRes fr xs ys)

export %inline
(++) : Functor m => Semigroup r => Swirl m r o -> Lazy (Swirl m r o) -> Swirl m r o
(++) = concatWithRes (<+>)

-- Ignores the resutl of the left operand.
-- should be equivalent to `(>>) @{ByResult} . forgetRes`, but slightly more effective and does not require `Monoid r`
export
andThen : Functor m => (0 _ : IfUnsolved r' ()) => Swirl m r' o -> Lazy (Swirl m r o) -> Swirl m r o
andThen (Done _)     ys = ys
andThen (Yield x xs) ys = Yield x $ xs `andThen` ys
andThen (Effect xs)  ys = Effect $ xs <&> mapLazy (assert_total (`andThen` ys))

infixl 1 `andThen` -- as `>>`

-- experimental; if this clutters monad instance usage, it will be removed
export %inline
(>>) : Functor m => (0 _ : IfUnsolved r' ()) => Swirl m r' o -> Lazy (Swirl m r o) -> Swirl m r o
(>>) = andThen

--- Interleaving ---

export
interleave : Applicative m => (resultComp : rl -> rr -> r) -> Swirl m rl o -> Swirl m rr o -> Swirl m r o
interleave fr (Done x) ys = mapFst (fr x) ys
interleave fr xs (Done y) = mapFst (`fr` y) xs
interleave fr (Yield x xs)  (Yield y ys) = Yield x $ Yield y $ interleave fr xs ys
interleave fr (Yield x xs)  (Effect ys)  = Yield x $ Effect $ ys <&> mapLazy (interleave fr xs)
interleave fr e@(Effect xs) (Yield x ys) = Effect $ xs <&> mapLazy (\xs => interleave fr (assert_smaller e xs) ys)
interleave fr e@(Effect xs) (Effect ys)  = Effect [| f xs ys |] where
  %inline f : Lazy (Swirl m rl o) -> Lazy (Swirl m rr o) -> Lazy (Swirl m r o)
  f x y = interleave fr (assert_smaller e x) y

--- Filtration ---

export
filter : Functor m => (a -> Bool) -> Swirl m r a -> Swirl m r a
filter _ $ Done x     = Done x
filter f $ Yield x ys = if f x then Yield x (filter f ys) else filter f ys
filter f $ Effect xs  = Effect $ xs <&> mapLazy (assert_total $ filter f)

export
mapMaybe : Functor m => (a -> Maybe b) -> Swirl m r a -> Swirl m r b
mapMaybe _ $ Done x     = Done x
mapMaybe f $ Yield x ys = case f x of
                            Just y  => Yield y $ mapMaybe f ys
                            Nothing => mapMaybe f ys
mapMaybe f $ Effect xs  = Effect $ xs <&> mapLazy (assert_total $ mapMaybe f)

--- Creation ---

export
emit : Functor m => Monoid r => (0 _ : IfUnsolved r ()) => m a -> Swirl m r a
emit mx = Effect $ mx <&> \x => delay $ Yield x $ Done neutral

export
done : (0 _ : IfUnsolved o Void) => a -> Swirl m a o
done = Done

export
finish : Functor m => (0 _ : IfUnsolved o Void) => m a -> Swirl m a o
finish mx = Effect $ mx <&> \x => Done x

--- Internal foldings ---

export
foldResOutsBy : Functor m => (0 _ : IfUnsolved o Void) => (a -> b -> b) -> Swirl m b a -> Swirl m b o
foldResOutsBy f $ Done x     = Done x
foldResOutsBy f $ Yield x ys = assert_total foldResOutsBy f $ mapFst (f x) ys
foldResOutsBy f $ Effect xs  = Effect $ xs <&> mapLazy (assert_total $ foldResOutsBy f)

export
foldResOuts : Semigroup a => Functor m => (0 _ : IfUnsolved o Void) => Swirl m a a -> Swirl m a o
foldResOuts = foldResOutsBy (<+>)

export
foldOutsBy : Functor m =>
             (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
             (a -> b -> b) -> b -> Swirl m r a -> Swirl m b o
foldOutsBy f x = foldResOutsBy f . mapFst (const x)

export
foldOuts : Monoid a => Functor m =>
           (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
           Swirl m r a -> Swirl m a o
foldOuts = foldResOuts . mapFst (const neutral)

export
outputs : Functor m =>
          (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
          Swirl m r a -> Swirl m (List a) o
outputs = foldOutsBy (::) []

--- Adapters ---

export
emitRes : Functor m => Monoid r =>
          (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
          Swirl m a o -> Swirl m r a
emitRes $ Done x     = Yield x $ Done neutral
emitRes $ Yield _ xs = emitRes xs
emitRes $ Effect xs  = Effect $ xs <&> mapLazy (assert_total emitRes)

export
forgetOuts : Functor m => (0 _ : IfUnsolved o Void) => Swirl m r a -> Swirl m r o
forgetOuts $ Done x     = Done x
forgetOuts $ Yield _ ys = forgetOuts ys
forgetOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total forgetOuts)

export
forgetRes : Functor m => Monoid r => (0 _ : IfUnsolved r ()) => Swirl m r' a -> Swirl m r a
forgetRes $ Done _     = Done neutral
forgetRes $ Yield x ys = Yield x $ forgetRes ys
forgetRes $ Effect xs  = Effect $ xs <&> mapLazy (assert_total forgetRes)

--- Flattenings ---

export
mergeCtxs : Monoid r => Applicative m => Applicative n => Swirl m r (Swirl n r o) -> Swirl (m . n) r o
mergeCtxs $ Done x     = Done x
mergeCtxs $ Yield x ys = (mapCtx pure x ++ mergeCtxs ys) @{Compose}
mergeCtxs $ Effect xs  = Effect $ xs <&> pure . mapLazy (assert_total mergeCtxs)

squashOuts' : Functor m => Swirl m r (Swirl m r o) -> Swirl m (List r) o
squashOuts' $ Done x     = Done [x]
squashOuts' $ Yield x ys = concatWithRes (::) x $ squashOuts' ys
squashOuts' $ Effect xs  = Effect $ xs <&> mapLazy (assert_total squashOuts')

squashOuts : Monoid r => Functor m => Swirl m r (Swirl m r o) -> Swirl m r o
squashOuts $ Done x     = Done x
squashOuts $ Yield x ys = x ++ squashOuts ys
squashOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total squashOuts)

squashRes : Functor m => Swirl m (Swirl m r o) o -> Swirl m r o
squashRes $ Done x     = x
squashRes $ Yield x ys = Yield x $ squashRes ys
squashRes $ Effect xs  = Effect $ xs <&> mapLazy (assert_total squashRes)

--- Functor, Applicative, Monad ---

-- Implementations over the last type argument --

export
Functor m => Functor (Swirl m r) where
  map = mapSnd

export
Monoid r => Functor m => Applicative (Swirl m r) where
  pure x = Yield x $ Done neutral
  fs <*> xs = squashOuts $ fs <&> flip map xs

-- Caution! This implementation is, actually, not associative
export
Monoid r => Applicative m => Alternative (Swirl m r) where
  empty = Done neutral
  xs <|> ys = interleave (<+>) xs ys

export
Monoid r => Functor m => Monad (Swirl m r) where
  join = squashOuts

export
HasIO io => Monoid r => HasIO (Swirl io r) where
  liftIO = emit . liftIO

-- Implementations over the second type argument --

namespace Functor

  export
  [ByResult] Functor m => Functor (\r => Swirl m r o) where
    map = mapFst

namespace Applicative

  export
  [ByResult] Functor m => Applicative (\r => Swirl m r o)
    using Functor.ByResult where
      pure = Done
      fs <*> xs = squashRes $ map @{ByResult} (flip (map @{ByResult}) xs) fs

namespace Monad

  export
  [ByResult] Functor m => Monad (\r => Swirl m r o)
    using Applicative.ByResult where
      join = squashRes
      x >>= f = join @{ByResult} $ map @{ByResult} f x

--- Hardcore processing ---

||| Allows to alter the whole rest of the stream with a decision function on output.
||| Decision function is given the current output and the original continuation and
||| returns a swirl which as a result has a new continuation, which replaces the orignal one.
||| Later this function goes onto the new continuation.
export covering
wriggleOuts : Functor m =>
              ((curr : o) -> (cont : Swirl m r o) -> Swirl m (Swirl m r o) o) ->
              Swirl m r o -> Swirl m r o
wriggleOuts f d@(Done x)   = d
wriggleOuts f $ Yield x ys = (f x ys >>= wriggleOuts f) @{ByResult}
wriggleOuts f $ Effect xs  = Effect $ xs <&> mapLazy (wriggleOuts f)

||| Allows to alter the whole rest of the stream with a decision function on output.
||| Decision function is given the current output and the original continuation and
||| returns a swirl which outputs new continuations, which being concatenated replace the orignal one.
||| Later this function goes onto the new continuations.
export covering
wiggleOuts : Functor m =>
             Monoid r =>
             (0 _ : IfUnsolved r' ()) =>
             ((curr : o) -> (cont : Swirl m r o) -> Swirl m r' (Swirl m r o)) ->
             Swirl m r o -> Swirl m r o
wiggleOuts f d@(Done _)   = d
wiggleOuts f $ Yield x ys = join $ forgetRes $ map (wiggleOuts f) $ f x ys
wiggleOuts f $ Effect xs  = Effect $ xs <&> mapLazy (wiggleOuts f)

--- Extension ---

-- Effects of the separator happen before the next yield of an output
export
intersperseOuts' : Functor m => (r' -> r -> r) -> (sep : Swirl m r' o) -> Swirl m r o -> Swirl m r o
intersperseOuts' fr sep $ d@(Done _) = d
intersperseOuts' fr sep $ Yield x ys = Yield x $ assert_total flip wriggleOuts ys $ \o, cont =>
                                         (sep <&> \r' => Yield o $ map @{ByResult} (fr r') cont) @{ByResult}
intersperseOuts' fr sep $ Effect xs  = Effect $ xs <&> mapLazy (assert_total intersperseOuts' fr sep)

-- Ignores the result of `sep`, the same as `intersperseOuts' (const id)`, but slighly more effective
export
intersperseOuts_ : Functor m => (0 _ : IfUnsolved r' ()) => (sep : Swirl m r' o) -> Swirl m r o -> Swirl m r o
intersperseOuts_ sep $ d@(Done _) = d
intersperseOuts_ sep $ Yield x ys = Yield x $ assert_total flip wriggleOuts ys $ \o, cont => (sep <&> const (Yield o cont)) @{ByResult}
intersperseOuts_ sep $ Effect xs  = Effect $ xs <&> mapLazy (assert_total intersperseOuts_ sep)

export
intersperseOuts : Functor m => Semigroup r => (sep : Swirl m r o) -> Swirl m r o -> Swirl m r o
intersperseOuts = intersperseOuts' (<+>)

--- Eliminators ---

namespace NoTailRec

  export
  result : Monad m => Swirl m a Void -> m a
  result $ Done x    = pure x
  result $ Effect xs = xs >>= assert_total result . force

namespace TailRec

  covering
  WellFounded () Equal where
    wellFounded () = Access $ \(), Refl => wellFounded ()

  export covering
  result : MonadRec m => Swirl m a Void -> m a
  result sw = tailRecM () sw (wellFounded ()) $ \wf => \case
    Done x    => pure $ Done x
    Effect xs => Cont wf Refl . force <$> xs
