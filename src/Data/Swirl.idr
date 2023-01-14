module Data.Swirl

import Control.MonadRec

%default total

export
data Swirl : (Type -> Type) -> (result, output : Type) -> Type where
  Done   : r -> Swirl m r o
  Yield  : o -> Lazy (Swirl m r o) -> Swirl m r o
  Effect : m (Lazy (Swirl m r o)) -> Swirl m r o

-- `m (Lazy ...)` exploits totality checker's bug to make the type as if it's strictly positive.

%inline
mapLazy : (a -> b) -> Lazy a -> Lazy b
mapLazy f = delay . f . force

export
Functor m => Bifunctor (Swirl m) where
  bimap fr fo $ Done r       = Done $ fr r
  bimap fr fo $ Yield o rest = Yield (fo o) (bimap fr fo rest)
  bimap fr fo $ Effect ef    = Effect $ ef <&> mapLazy (assert_total $ bimap fr fo)

export
(++) : Semigroup r => Functor m => Swirl m r o -> Lazy (Swirl m r o) -> Swirl m r o
(++) (Done r)     ys = mapFst (<+> r) ys
(++) (Yield x xs) ys = Yield x $ xs ++ ys
(++) (Effect xs)  ys = Effect $ xs <&> mapLazy (assert_total (++ ys))

--- Internal convertions and combinators ---

export
foldResOuts : Semigroup a => Functor m => Swirl m a a -> Swirl m a Void
foldResOuts $ Done x     = Done x
foldResOuts $ Yield x ys = assert_total foldResOuts $ mapFst (x <+>) ys
foldResOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total foldResOuts)

export
foldOuts : Monoid a => Functor m => Swirl m () a -> Swirl m a Void
foldOuts = foldResOuts . mapFst (const neutral)

export
forgetOuts : Functor m => Swirl m r a -> Swirl m r Void
forgetOuts $ Done x     = Done x
forgetOuts $ Yield _ ys = forgetOuts ys
forgetOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total forgetOuts)

squashOuts : Monoid r => Functor m => Swirl m r (Swirl m r o) -> Swirl m r o
squashOuts $ Done x     = Done x
squashOuts $ Yield x ys = x ++ squashOuts ys
squashOuts $ Effect xs  = Effect $ xs <&> mapLazy (assert_total squashOuts)

squashRes : Functor m => Swirl m (Swirl m r o) o -> Swirl m r o
squashRes $ Done x     = x
squashRes $ Yield x ys = Yield x $ squashRes ys
squashRes $ Effect xs  = Effect $ xs <&> mapLazy (assert_total squashRes)

export
Functor m => Functor (Swirl m r) where
  map = mapSnd

export
Monoid r => Functor m => Applicative (Swirl m r) where
  pure x = Yield x $ Done neutral
  fs <*> xs = squashOuts $ fs <&> flip map xs

export
Monoid r => Functor m => Monad (Swirl m r) where
  join = squashOuts

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

export
result' : Monad m => Swirl m a Void -> m a
result' $ Done x    = pure x
result' $ Effect xs = xs >>= assert_total result' . force

result : MonadRec m => Swirl m a Void -> m a
result sw = tailRecM ?wf sw ?wf_prf $ \wf => \case
  Done x    => pure $ Done x
  Effect xs => Cont ?wf' ?wf'rel . force <$> xs

foldMonoid : Monoid a => Swirl m () a -> m a
foldMonoid $ Done x    = ?foldMonoid_rhs_0
foldMonoid $ Yield x y = ?foldMonoid_rhs_1
foldMonoid $ Effect x  = ?foldMonoid_rhs_2

