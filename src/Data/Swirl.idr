module Data.Swirl

import Control.MonadRec
import Control.WellFounded

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
(++) : Functor m => Semigroup r => Swirl m r o -> Lazy (Swirl m r o) -> Swirl m r o
(++) (Done r)     ys = mapFst (<+> r) ys
(++) (Yield x xs) ys = Yield x $ xs ++ ys
(++) (Effect xs)  ys = Effect $ xs <&> mapLazy (assert_total (++ ys))

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
emit : Functor m => m a -> Swirl m () a
emit mx = Effect $ mx <&> \x => delay $ Yield x $ Done ()

export
done : a -> Swirl m a Void
done = Done

export
finish : Functor m => m a -> Swirl m a Void
finish mx = Effect $ mx <&> \x => Done x

--- Extension ---

-- Intersperse an action between yields? Or intersperse an action between any two actions/yields?
-- intersperse :

--- Internal foldings ---

export
foldResOutsBy : Functor m => (a -> b -> b) -> Swirl m b a -> Swirl m b Void
foldResOutsBy f $ Done x     = Done x
foldResOutsBy f $ Yield x ys = assert_total foldResOutsBy f $ mapFst (f x) ys
foldResOutsBy f $ Effect xs  = Effect $ xs <&> mapLazy (assert_total $ foldResOutsBy f)

export
foldResOuts : Semigroup a => Functor m => Swirl m a a -> Swirl m a Void
foldResOuts = foldResOutsBy (<+>)

export
foldOutsBy : Functor m => (a -> b -> b) -> b -> Swirl m () a -> Swirl m b Void
foldOutsBy f x = foldResOutsBy f . mapFst (const x)

export
foldOuts : Monoid a => Functor m => Swirl m () a -> Swirl m a Void
foldOuts = foldResOuts . mapFst (const neutral)

export
outputs : Functor m => Swirl m () a -> Swirl m (List a) Void
outputs = foldOutsBy (::) []

--- Adapters ---

export
emitRes : Functor m => Swirl m a Void -> Swirl m () a
emitRes $ Done x    = Yield x $ Done ()
emitRes $ Effect xs = Effect $ xs <&> mapLazy (assert_total emitRes)

export
forgetOuts : Functor m => Swirl m r a -> Swirl m r Void
forgetOuts $ Done x     = Done x
forgetOuts $ Yield _ ys = forgetOuts ys
forgetOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total forgetOuts)

export
forgetRes : Functor m => Swirl m r a -> Swirl m () a
forgetRes $ Done _     = Done ()
forgetRes $ Yield x ys = Yield x $ forgetRes ys
forgetRes $ Effect xs  = Effect $ xs <&> mapLazy (assert_total forgetRes)

--- Flattenings ---

export
mergeCtxs : Monoid r => Applicative m => Applicative n => Swirl m r (Swirl n r o) -> Swirl (m . n) r o
mergeCtxs $ Done x     = Done x
mergeCtxs $ Yield x ys = (mapCtx pure x ++ mergeCtxs ys) @{Compose}
mergeCtxs $ Effect xs  = Effect $ xs <&> pure . mapLazy (assert_total mergeCtxs)

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
