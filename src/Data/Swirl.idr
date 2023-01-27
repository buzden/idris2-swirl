module Data.Swirl

import Data.Either
import Data.List.Lazy
import Data.List1
import Data.Maybe
import Data.These

import Control.Monad.Identity
import public Control.MonadRec
import Control.WellFounded

import public Language.Implicits.IfUnsolved

%default total

export
data Swirl : (Type -> Type) -> (error, result, output : Type) -> Type where
  Done   : r -> Swirl m e r o
  Fail   : e -> Swirl m e r o
  Yield  : o -> Lazy (Swirl m e r o) -> Swirl m e r o
  Effect : m (Lazy (Swirl m e r o)) -> Swirl m e r o
  BindR  : Lazy (Swirl m e r' o) -> (r' -> Swirl m e r o) -> Swirl m e r o
  BindE  : Lazy (Swirl m e' r o) -> (e' -> Swirl m e r o) -> Swirl m e r o
  Ensure : Lazy (Swirl m e' r' o) -> Lazy (Swirl m e r o) -> Swirl m (These e' e) (r', r) o

%name Swirl sw, sv, su

-- `m (Lazy ...)` in `Effect` exploits totality checker's bug to make the type as if it's strictly positive.

%inline %tcinline
mapLazy : (a -> b) -> Lazy a -> Lazy b
mapLazy f = delay . f . force

--- Basic mapping ---

export
Functor m => Bifunctor (Swirl m e) where
  bimap fr fo $ Done x     = Done $ fr x
  bimap fr fo $ Fail x     = Fail x
  bimap fr fo $ Yield o sw = Yield (fo o) (bimap fr fo sw)
  bimap fr fo $ Effect msw = Effect $ msw <&> mapLazy (assert_total bimap fr fo)
  bimap fr fo $ BindR x f  = BindR (bimap id fo x) (bimap fr fo . f)
  bimap fr fo $ BindE x h  = BindE (bimap fr fo x) (bimap fr fo . h)
  bimap fr fo $ Ensure l x = Ensure (bimap id fo l) (bimap id fo x) `BindR` Done . fr

%transform "swirl: mapFst id" mapFst {f=Swirl m e} (\x => x) x = x
%transform "swirl: mapSnd id" mapSnd {f=Swirl m e} (\x => x) x = x
%transform "swirl: bimap id id" bimap {f=Swirl m e} (\x => x) (\x => x) x = x

export
mapCtx : Functor m => (forall a. m a -> n a) -> Swirl m e r o -> Swirl n e r o
mapCtx f $ Done x     = Done x
mapCtx f $ Fail x     = Fail x
mapCtx f $ Yield x sw = Yield x $ mapCtx f sw
mapCtx f $ Effect msw = Effect $ f $ msw <&> mapLazy (assert_total mapCtx f)
mapCtx f $ BindR x g  = BindR (mapCtx f x) (mapCtx f . g)
mapCtx f $ BindE x h  = BindE (mapCtx f x) (mapCtx f . h)
mapCtx f $ Ensure l x = Ensure (mapCtx f l) (mapCtx f x)

export
mapError : (e -> e') -> Swirl m e r o -> Swirl m e' r o
mapError f $ Done x     = Done x
mapError f $ Fail x     = Fail $ f x
mapError f $ BindE x h  = BindE x (mapError f . h)
mapError f sw           = BindE sw (Fail . f)
--mapError f $ Yield x sw = Yield x $ mapError f sw
--mapError f $ Effect msw   = Effect $ msw <&> mapLazy (assert_total mapError f)
--mapError f $ BindR x g    = BindR (mapError f x) (mapError f . g)

--- Basic combinators ---

namespace ComposeResults

  export
  concat' : Functor m => (resultComp : rl -> rr -> r) -> Swirl m el rl o -> Lazy (Swirl m er rr o) -> Swirl m (Either el er) r o
  concat' fr (Done x) sv = mapError Right . mapFst (fr x) $ sv
  concat' fr (Fail x) sv = Fail $ Left x
  concat' fr sw       sv = BindR (mapError Left sw) $ \x => mapError Right $ mapFst (fr x) sv

  export
  concat : Functor m => (resultComp : rl -> rr -> r) -> Swirl m e rl o -> Lazy (Swirl m e rr o) -> Swirl m e r o
  concat fr (Done x) sv = mapFst (fr x) sv
  concat fr (Fail x) sv = Fail x
  concat fr sw       sv = BindR sw $ \x => mapFst (fr x) sv
--  concat fr (Yield x sw) sv = Yield x $ concat fr sw sv
--  concat fr (Effect msw) sv = Effect $ msw <&> mapLazy (\sw => assert_total concat fr sw sv)
--  concat fr (BindR x f)  sv = BindR x $ (\sw => assert_total concat fr sw sv) . f
--  concat fr (BindE x h)  sv = BindE (assert_total $ concat fr (mapError Left x) (mapError Right sv)) $ \case
--                                Right e => Fail e -- error from the rhs of concat, rethrow
--                                Left e  => concat fr (h e) sv -- error on the lhs of concat, concat with handler

export %inline
(++) : Functor m => Semigroup r => Swirl m e r o -> Lazy (Swirl m e r o) -> Swirl m e r o
(++) = concat (<+>)

export
andThen : Swirl m e () o -> Lazy (Swirl m e r o) -> Swirl m e r o
andThen sw sv = BindR sw $ const sv

infixl 1 `andThen` -- as `>>`

-- experimental; if this clutters monad instance usage, it will be removed
export %inline
(>>) : Swirl m e () o -> Lazy (Swirl m e r o) -> Swirl m e r o
(>>) = andThen

--- Forgetting ---

export
forgetO : Functor m => (0 _ : IfUnsolved o Void) => Swirl m e r a -> Swirl m e r o
forgetO $ Done x     = Done x
forgetO $ Fail e     = Fail e
forgetO $ Yield x sw = forgetO sw
forgetO $ Effect msw = Effect $ msw <&> mapLazy (assert_total forgetO)
forgetO $ BindR sw g = BindR (forgetO sw) (forgetO . g)
forgetO $ BindE sw h = BindE (forgetO sw) (forgetO . h)
forgetO $ Ensure l x = Ensure (forgetO l) (forgetO x)

export
forgetR : Functor m => Monoid r => (0 _ : IfUnsolved r ()) => Swirl m e r' a -> Swirl m e r a
forgetR $ Done x = Done neutral
forgetR $ Fail e = Fail e
forgetR sw       = BindR sw $ const $ Done neutral
--forgetR $ Yield x sw = Yield x $ forgetR sw
--forgetR $ Effect msw = Effect $ msw <&> mapLazy (assert_total forgetR)
--forgetR $ BindR sw g = BindR sw (forgetR . g)
--forgetR $ BindE sw h = BindE (forgetR sw) (forgetR . h)
--forgetR $ Ensure l x = Ensure l $ forgetR x

--- Basic creation ---

||| A postfix function modifier to create an effected swirl creation.
||| E.g. `emit v` emits `v` without any action, and `emit.by mv` emits a value of type `v` from `mv` of type `m v`.
export %inline
(.by) : Functor m => (x -> Swirl m e r o) -> m x -> Swirl m e r o
f.by = Effect . map (delay . f)

-- Output --

export %inline
emit : Functor m => Monoid r =>
       (0 _ : IfUnsolved e Void) =>
       (0 _ : IfUnsolved r ()) =>
       o -> Swirl m e r o
emit x = Yield x $ Done neutral

-- Result --

export %inline
succeed : (0 _ : IfUnsolved e Void) =>
          (0 _ : IfUnsolved o Void) =>
          r -> Swirl m e r o
succeed = Done

-- Error --

export %inline
fail : Functor m =>
       (0 _ : IfUnsolved r ()) =>
       (0 _ : IfUnsolved o Void) =>
       e -> Swirl m e r o
fail = Fail

-- Result or error --

export
succeedOrFail : Functor m =>
                (0 _ : IfUnsolved o Void) =>
                Either e r -> Swirl m e r o
succeedOrFail = either fail succeed

-- Output or error --

export
emitOrFail : Functor m =>
             Monoid r =>
             (0 _ : IfUnsolved r ()) =>
             Either e o -> Swirl m e r o
emitOrFail = either fail emit

--- Internal foldings ---

--namespace ToResult
--
--  export
--  foldResOutsBy : Functor m => (0 _ : IfUnsolved o Void) => (a -> b -> b) -> Swirl m b a -> Swirl m b o
--  foldResOutsBy f = prY $ \x, ys => assert_total foldResOutsBy f $ mapFst (f x) ys
--
--  export
--  foldResOuts : Semigroup a => Functor m => (0 _ : IfUnsolved o Void) => Swirl m a a -> Swirl m a o
--  foldResOuts = foldResOutsBy (<+>)
--
--  export
--  foldOutsBy : Functor m =>
--               (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
--               (a -> b -> b) -> b -> Swirl m r a -> Swirl m b o
--  foldOutsBy f x = foldResOutsBy f . mapFst (const x)
--
--  export
--  foldOuts : Monoid a => Functor m =>
--             (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
--             Swirl m r a -> Swirl m a o
--  foldOuts = foldResOuts . mapFst (const neutral)
--
--  export
--  outputs : Functor m =>
--            (0 _ : IfUnsolved o Void) => (0 _ : IfUnsolved r ()) =>
--            Swirl m r a -> Swirl m (List a) o
--  outputs = foldOutsBy (::) []
--
--namespace ToOutput
--
--  export
--  foldOutsBy : Functor m => (b -> a -> b) -> b -> Swirl m r a -> Swirl m r b
--  foldOutsBy f init = prDY (\x => Yield init $ Done x) $ \x, cont => assert_total foldOutsBy f (f init x) cont
--
--  export
--  foldOuts : Functor m => Monoid a => Swirl m r a -> Swirl m r a
--  foldOuts = foldOutsBy (<+>) neutral
--
--  export
--  outputs : Functor m => Swirl m r o -> Swirl m r (SnocList o)
--  outputs = foldOutsBy (:<) [<]

--- Flattenings ---

namespace ComposeResults

  -- So strange resulting error type is because the error can occur in the finally section along with an error in the main section.
  -- Several suberrors may occur if is was thrown in finally sections of both main section and outer error handler.
  export
  mergeCtxs' : Applicative m => Applicative n => Swirl m e r (Swirl n e' r' o) -> Swirl (m . n) (These e $ List1 e') (r, List r') o
  mergeCtxs' $ Done x     = Done (x, [])
  mergeCtxs' $ Fail e     = Fail $ This e
  mergeCtxs' $ Yield x sw = concat @{Compose} (mapSnd . (::)) (mapCtx pure $ mapError (That . pure) x) (mergeCtxs' sw)
  mergeCtxs' $ Effect msw = Effect $ msw <&> pure . mapLazy (assert_total mergeCtxs')
  mergeCtxs' $ BindR x f  = BindR (mergeCtxs' x) $ \(y, ys) => let _ = Functor.Compose in mapFst (mapSnd (ys ++)) $ mergeCtxs' $ f y
  mergeCtxs' $ BindE x h  = BindE (mergeCtxs' x) $ \case
                              This y => mergeCtxs' $ h y
                              That y => Fail $ That y
                              Both y z => mapError (mapSnd (z ++)) $ mergeCtxs' $ h y
  mergeCtxs' $ Ensure l x = mapError reorderE (Ensure (mergeCtxs' l) (mergeCtxs' x)) `BindR` \((r', rsl), (r, rsr)) => Done ((r', r), rsl ++ rsr)
    where reorderE : forall e, e', e''. These (These e' (List1 e'')) (These e (List1 e'')) -> These (These e' e) (List1 e'')
          reorderE $ This x = mapFst This x
          reorderE $ That x = mapFst That x
          reorderE $ Both (This x) z = mapFst That z
          reorderE $ Both (That y) z = bimap That (y++) z
          reorderE $ Both (Both x y) z = bimap (Both x) (y++) z

  -- TODO to change `Monoid e` to `Semigroup e` as soon as `These.bifold` would relax its requirement.
  export
  mergeCtxs : Applicative m => Applicative n => Monoid e => (r' -> r -> r) -> Swirl m e r (Swirl n e r' o) -> Swirl (m . n) e r o
  mergeCtxs fr = let _ = Functor.Compose in mapFst (uncurry $ foldr fr) . mapError (bifold . mapSnd (foldl1 (<+>))) . mergeCtxs'

-- TODO to change `Monoid e` to `Semigroup e` as soon as `These.bifold` would relax its requirement.
export
mergeCtxs : Applicative m => Applicative n => Semigroup r => Monoid e => Swirl m e r (Swirl n e r o) -> Swirl (m . n) e r o
mergeCtxs = mergeCtxs (<+>)

namespace ComposeResults

  -- So strange resulting error type is because the error can occur in the finally section along with an error in the main section.
  -- Several suberrors may occur if is was thrown in finally sections of both main section and outer error handler.
  export
  squashOuts' : Functor m => Swirl m e r (Swirl m e' r' o) -> Swirl m (These e $ List1 e') (r, List r') o

  -- TODO to change `Monoid e` to `Semigroup e` as soon as `These.bifold` would relax its requirement.
  export
  squashOuts : Functor m => Monoid e => (r' -> r -> r) -> Swirl m e r (Swirl m e r' o) -> Swirl m e r o
  squashOuts fr = mapFst (uncurry $ foldr fr) . mapError (bifold . mapSnd (foldl1 (<+>))) . squashOuts'

-- TODO to change `Monoid e` to `Semigroup e` as soon as `These.bifold` would relax its requirement.
squashOuts : Functor m => Semigroup r => Monoid e => Swirl m e r (Swirl m e r o) -> Swirl m e r o
squashOuts = squashOuts (<+>)

squashRes : Functor m => Swirl m e (Swirl m e r o) o -> Swirl m e r o
--squashRes = prDY id $ \x, ys => Yield x $ assert_total squashRes ys

--- Filtration ---

export
mapEither' : Functor m =>
             (0 _ : IfUnsolved e Void) =>
             (0 _ : IfUnsolved r ()) =>
             (o -> Either e' o') ->
             Swirl m e r o ->
             Swirl m (Either e e') r o'

export
mapEither : Functor m => (o -> Either e o') -> Swirl m e r o -> Swirl m e r o'


{-

export
mapMaybe : Functor m => (o -> Maybe o') -> Swirl m e r o -> Swirl m e r o'
mapMaybe f $ Done x     = Done x
mapMaybe f $ Fail e     = Fail e
mapMaybe f $ Yield x sw = case f x of
                            Nothing => mapMaybe f sw -- no common subexpression, tail recursion instead
                            Just y  => Yield y $ mapMaybe f sw
mapMaybe f $ Effect msw = Effect $ msw <&> mapLazy (assert_total mapMaybe f)
mapMaybe f $ BindR sw g = BindR (mapMaybe f sw) (assert_total mapMaybe f . g)
mapMaybe f $ BindE sw h = BindE (mapMaybe f sw) (assert_total mapMaybe f . h)

export
filter : Functor m => (a -> Bool) -> Swirl m e r a -> Swirl m e r a
filter f $ Done x     = Done x
filter f $ Fail e     = Fail e
filter f $ Yield x sw = case f x of
                          False => filter f sw -- no common subexpression, tail recursion instead
                          True  => Yield x $ filter f sw
filter f $ Effect msw = Effect $ msw <&> mapLazy (assert_total filter f)
filter f $ BindR sw g = BindR (filter f sw) (assert_total filter f . g)
filter f $ BindE sw h = BindE (filter f sw) (assert_total filter f . h)

--- Interleaving ---

namespace ComposeResults

  export
  interleave : Applicative m => (resultComp : rl -> rr -> r) -> Swirl m e rl o -> Swirl m e rr o -> Swirl m e r o
--  interleave fr (Done x) ys = mapFst (fr x) ys
--  interleave fr xs (Done y) = mapFst (`fr` y) xs
--  interleave fr (Yield x xs)  (Yield y ys) = Yield x $ Yield y $ interleave fr xs ys
--  interleave fr (Yield x xs)  (Effect ys)  = Yield x $ Effect $ ys <&> mapLazy (interleave fr xs)
--  interleave fr e@(Effect xs) (Yield x ys) = Effect $ xs <&> mapLazy (\xs => interleave fr (assert_smaller e xs) ys)
--  interleave fr e@(Effect xs) (Effect ys)  = Effect [| f xs ys |] where
--    %inline f : Lazy (Swirl m rl o) -> Lazy (Swirl m rr o) -> Lazy (Swirl m r o)
--    f x y = interleave fr (assert_smaller e x) y

--- Functor, Applicative, Monad ---

-- Implementations over the last type argument --

export
Functor m => Functor (Swirl m e r) where
  map = mapSnd

export
Monoid r => Functor m => Applicative (Swirl m e r) where
  pure x = Yield x $ Done neutral
  fs <*> xs = squashOuts $ fs <&> flip map xs

export
Monoid r => Functor m => Monad (Swirl m e r) where
  join = squashOuts

export
HasIO io => Monoid r => HasIO (Swirl io e r) where
  liftIO = emit.by . liftIO

-- Implementations over the second type argument --

namespace Functor

  export
  [ByResult] Functor m => Functor (\r => Swirl m e r o) where
    map = mapFst

namespace Applicative

  export
  [ByResult] Functor m => Applicative (\r => Swirl m e r o)
    using Functor.ByResult where
      pure = Done
      fs <*> xs = squashRes $ map @{ByResult} (flip (map @{ByResult}) xs) fs

namespace Monad

  export
  [ByResult] Functor m => Monad (\r => Swirl m e r o)
    using Applicative.ByResult where
      join = squashRes
      x >>= f = join @{ByResult} $ map @{ByResult} f x

--- Error handling ---

export
handleError : (0 _ : IfUnsolved e' Void) =>
              (e -> Swirl m e' r o) -> Swirl m e r o -> Swirl m e' r o
handleError = flip $ BindE . delay

--- Finally funning ---

elimTheseVoid : These e Void -> e
elimTheseVoid $ This x = x

export
withFinally' : Functor m => Swirl m e' () o -> Swirl m e r o -> Swirl m (These e e') r o

export
withFinally : Functor m => Swirl m Void () o -> Swirl m e r o -> Swirl m e r o
withFinally = mapError elimTheseVoid .: withFinally'

export
bracket' : Functor m =>
           (init : Swirl m e res o) ->
           (cleanup : res -> Swirl m e' () o) ->
           (action : res -> Swirl m e r o) ->
           Swirl m (These e e') r o
bracket' init cleanup action = (mapError This init >>= \res => withFinally' (cleanup res) (action res)) @{ByResult}

export
bracket : Functor m =>
          (init : Swirl m e res o) ->
          (cleanup : res -> Swirl m Void () o) ->
          (action : res -> Swirl m e r o) ->
          Swirl m e r o
bracket init = mapError elimTheseVoid .: bracket' init

--- Processes ---

export covering
repeat : Functor m =>
         (0 _ : IfUnsolved e Void) =>
         Swirl m e () o -> Swirl m e Void o
repeat sw = forgetR sw `andThen` repeat sw

||| Emit units until given effect returns `True` or fails
export covering
tickUntil : Functor m =>
            Monoid r =>
            (0 _ : IfUnsolved r ()) =>
            (0 _ : IfUnsolved e Void) =>
            Swirl m e Bool Void -> Swirl m e r ()
tickUntil $ Done True     = Done neutral
tickUntil sw@(Done False) = Yield () $ tickUntil sw
tickUntil $ Fail e        = Fail e
tickUntil sw = (map absurd sw >>= \stop => if stop then succeed neutral else Yield () $ tickUntil sw) @{ByResult}

--- Adapters ---

export
emitRes : Functor m =>
          Monoid r =>
          (0 _ : IfUnsolved r ()) =>
          Swirl m e r' Void -> Swirl m e r r'
emitRes $ Done x     = Yield x $ Done neutral
emitRes $ Fail x     = Fail x
emitRes $ Effect msw = Effect $ msw <&> mapLazy (assert_total emitRes)
emitRes $ BindR x g  = BindR (map absurd x) (assert_total emitRes . g)
emitRes $ BindE x h  = BindE (emitRes x) (assert_total emitRes . h)

--- Cutting ---

export
take' : Functor m => Nat -> Swirl m e r o -> Swirl m e (Maybe r) o

export
takeWhile' : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m e (Maybe r) o

export
take : Functor m => Monoid r => Nat -> Swirl m e r o -> Swirl m e r o
take = mapFst (fromMaybe neutral) .: take'

export
takeWhile : Functor m => Monoid r => (o -> Bool) -> Swirl m e r o -> Swirl m e r o
takeWhile = mapFst (fromMaybe neutral) .: takeWhile'

export
drop : Functor m => Nat -> Swirl m e r o -> Swirl m e r o

export
dropWhile : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m e r o

--- Extension ---

namespace ComposeResults

  -- Effects of the separator happen before the next yield of an output
  export
  intersperseOuts : Functor m => (r' -> r -> r) -> (sep : Swirl m e r' o) -> Swirl m e r o -> Swirl m e r o
  --intersperseOuts fr sep = prY $ \x, ys => Yield x $ assert_total flip wriggleOuts ys $ \o, cont =>
  --  flip mapFst sep $ \r' => Yield o $ mapFst (fr r') cont

-- Ignores the result of `sep`, the same as `ComposeResults.intersperseOuts (const id)`, but slighly more effective
export
intersperseOuts' : Functor m => (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m e r o
intersperseOuts' = intersperseOuts $ const id

export
intersperseOuts : Functor m => Semigroup r => (sep : Swirl m e r o) -> Swirl m e r o -> Swirl m e r o
intersperseOuts = intersperseOuts (<+>)

--- Eliminators ---

--export
--toLazyList : Swirl Identity Void () a -> LazyList a
--toLazyList $ Done ()    = []
--toLazyList $ Yield x sw = x :: toLazyList sw
--toLazyList $ Effect msw = assert_total toLazyList $ runIdentity msw
--toLazyList $ BindR x f  = ?toLazyList_rhs_4
--toLazyList $ BindE x f  = ?toLazyList_rhs_5

namespace NoTailRec

  export
  result : Monad m => Swirl m e a Void -> m $ Either e a
--  result $ Done x    = pure x
--  result $ Effect xs = xs >>= assert_total result . force

  export
  result' : Monad m => Swirl m Void a Void -> m a

namespace TailRec

  covering
  WellFounded () Equal where
    wellFounded () = Access $ \(), Refl => wellFounded ()

  export covering
  result : MonadRec m => Swirl m e a Void -> m $ Either e a
--  result sw = tailRecM () sw (wellFounded ()) $ \wf => \case
--    Done x    => pure $ Done x
--    Effect xs => Cont wf Refl . force <$> xs

  export covering
  result' : MonadRec m => Swirl m Void a Void -> m a
