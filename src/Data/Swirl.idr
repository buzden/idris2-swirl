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
  Effect : m (assert_total $ Swirl m e r o) -> Swirl m e r o
  BindR  : Lazy (Swirl m e r' o) -> (r' -> Swirl m e r o) -> Swirl m e r o
  BindE  : Lazy (Swirl m e' r o) -> (e' -> Swirl m e r o) -> Swirl m e r o
  Ensure : Lazy (Swirl m Void r' Void) -> Lazy (Swirl m e r o) -> Swirl m e (r', r) o

%name Swirl sw, sv, su

-- Discussion:
--
-- - `Effect` constructor.
--
--   The totality assertion is due to a functor requirement on the `m`, which
--   is used for the recursive use of the type.
--   This requirement is not depicted directly in the type of the constructor,
--   since it would lead to ambiguity errors, but it is meant to be present.
--
-- - `Ensure` constructor, output parameter of "finally" section.
--
--   The `finally` part must not emit values because of the following:
--   if the `finally` part can emit a value, it means that one can bind (`>>=`) the whole `Ensure` expression by
--   some `Swirl` which, in its order, may fail. This would lead to either ability of non-full "finally" block to be executed,
--   or the need of failure-ignoring variant of `>>=` to be used for it. Both it possible, but both are counter-intuitive.
--
--   By the way, at least at the time of writing this, the Scala's fs2 library has the same problem and generally the `release`
--   process of a braket pattern *can* be interrupted by an exception in the RHS of the `flatMap` if it emits some values.
--
-- - `Ensure` constructor, error parameter of "finally" action.
--
--   An ability of the "finally" action to fail would lead the joining function to have the following signature
--
--   ```idris
--   squashOuts' : Functor m => Swirl m e r (Swirl m e' r' o) -> Swirl m (These e $ List1 e') (r, List r') o
--   ```
--
--   So strange resulting error type is because the error can occur in the finally section along with an error in the main section.
--   Several suberrors may occur if is was thrown in finally sections of both main section and outer error handler.
--
--   It all means that even if the error type of outer and inner `Swirl`s are the same, we cannot
--   use `Monad` signature for `>>=` and `join`.
--   Also, it means that the `finally` section of `Ensure` can be unintentionally interrupted by the subsequent binds.
--   This may lead a nessesity to use finally sections in finally sections which emit values, which all looks fragile.
--
--   That all lead to a decision of inability to fail for the "finally" action.
--
-- - `Ensure` constructor, its return type.
--
--   Resulting error type of the contructor could be `(r', e)`, to emphasize that finally section always executes,
--   Thus always returning `r'` in both channels.

--- Basic mapping ---

export
Functor m => Bifunctor (Swirl m e) where
  bimap fr fo $ Done x     = Done $ fr x
  bimap fr fo $ Fail x     = Fail x
  bimap fr fo $ Yield o sw = Yield (fo o) (bimap fr fo sw)
  bimap fr fo $ Effect msw = Effect $ msw <&> assert_total bimap fr fo
  bimap fr fo $ BindR x f  = BindR (bimap id fo x) (bimap fr fo . f)
  bimap fr fo $ BindE x h  = BindE (bimap fr fo x) (bimap fr fo . h)
  bimap fr fo $ Ensure l x = Ensure l (bimap id fo x) `BindR` Done . fr

%transform "swirl: mapFst id" mapFst {f=Swirl m e} (\x => x) x = x
%transform "swirl: mapSnd id" mapSnd {f=Swirl m e} (\x => x) x = x
%transform "swirl: bimap id id" bimap {f=Swirl m e} (\x => x) (\x => x) x = x

export
mapCtx : Functor m => (forall a. m a -> n a) -> Swirl m e r o -> Swirl n e r o
mapCtx f $ Done x     = Done x
mapCtx f $ Fail x     = Fail x
mapCtx f $ Yield x sw = Yield x $ mapCtx f sw
mapCtx f $ Effect msw = Effect $ f $ msw <&> assert_total mapCtx f
mapCtx f $ BindR x g  = BindR (mapCtx f x) (mapCtx f . g)
mapCtx f $ BindE x h  = BindE (mapCtx f x) (mapCtx f . h)
mapCtx f $ Ensure l x = Ensure (mapCtx f l) (mapCtx f x)

export
mapError : (e -> e') -> Swirl m e r o -> Swirl m e' r o
mapError f $ Done x     = Done x
mapError f $ Fail x     = Fail $ f x
mapError f $ BindE x h  = BindE x (mapError f . h)
mapError f sw           = BindE sw (Fail . f)

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

export %inline
(++) : Functor m => Semigroup r => Swirl m e r o -> Lazy (Swirl m e r o) -> Swirl m e r o
(++) = concat (<+>)

export
andThen : Swirl m e () o -> Lazy (Swirl m e r o) -> Swirl m e r o
andThen sw sv = BindR sw $ const sv

infixl 1 `andThen` -- as `>>`

--- Forgetting ---

export
forgetO : Functor m => (0 _ : IfUnsolved o Void) => Swirl m e r a -> Swirl m e r o
forgetO $ Done x     = Done x
forgetO $ Fail e     = Fail e
forgetO $ Yield x sw = forgetO sw
forgetO $ Effect msw = Effect $ msw <&> assert_total forgetO
forgetO $ BindR sw g = BindR (forgetO sw) (forgetO . g)
forgetO $ BindE sw h = BindE (forgetO sw) (forgetO . h)
forgetO $ Ensure l x = Ensure (forgetO l) (forgetO x)

export
forgetR : Functor m => Monoid r => (0 _ : IfUnsolved r ()) => Swirl m e r' a -> Swirl m e r a
forgetR $ Done x = Done neutral
forgetR $ Fail e = Fail e
forgetR sw       = BindR sw $ const $ Done neutral

--- Basic creation ---

||| A postfix function modifier to create an effected swirl creation.
||| E.g. `emit v` emits `v` without any action, and `emit.by mv` emits a value of type `v` from `mv` of type `m v`.
export %inline
(.by) : Functor m => (x -> Swirl m e r o) -> m x -> Swirl m e r o
f.by = Effect . map f

-- Output --

export %inline
preEmitTo : (0 _ : IfUnsolved e Void) =>
            Lazy (Swirl m e r o) ->
            o ->
            Swirl m e r o
preEmitTo = flip Yield

export %inline
emit : Monoid r =>
       (0 _ : IfUnsolved e Void) =>
       (0 _ : IfUnsolved r ()) =>
       o -> Swirl m e r o
emit = preEmitTo $ Done neutral

export %inline
preEmitsTo : (0 _ : IfUnsolved e Void) =>
             Lazy (Swirl m e r o) ->
             LazyList o ->
             Swirl m e r o
preEmitsTo = foldrLazy Yield

export %inline
emits : Monoid r =>
        (0 _ : IfUnsolved e Void) =>
        (0 _ : IfUnsolved r ()) =>
        LazyList o ->
        Swirl m e r o
emits = preEmitsTo $ Done neutral

--export %inline
--preEmitMsTo : Functor m =>
--              (0 _ : IfUnsolved e Void) =>
--              Lazy (Swirl m e r o) ->
--              LazyList (m o) ->
--              Swirl m e r o
--preEmitMsTo = foldrLazy $ \mx, xs => Effect $ mx <&> \x => Yield x xs

-- Result --

export %inline
succeed : (0 _ : IfUnsolved e Void) =>
          (0 _ : IfUnsolved o Void) =>
          r -> Swirl m e r o
succeed = Done

-- Error --

export %inline
fail : (0 _ : IfUnsolved r ()) =>
       (0 _ : IfUnsolved o Void) =>
       e -> Swirl m e r o
fail = Fail

-- Result or error --

export
succeedOrFail : (0 _ : IfUnsolved o Void) =>
                Either e r -> Swirl m e r o
succeedOrFail = either fail succeed

-- Output or error --

export
emitOrFail : Monoid r =>
             (0 _ : IfUnsolved r ()) =>
             Either e o -> Swirl m e r o
emitOrFail = either fail emit

--- Adapters ---

export
emitRes' : Functor m => (r -> r') -> Swirl m e r Void -> Swirl m e r' r
emitRes' f $ Done x = Yield x $ Done $ f x
emitRes' f $ Fail x = Fail x
emitRes' f sw       = mapSnd absurd sw `BindR` \r => Yield r $ Done $ f r

export %inline
emitRes : Functor m =>
          Monoid r =>
          (0 _ : IfUnsolved r ()) =>
          Swirl m e r' Void -> Swirl m e r r'
emitRes = emitRes' $ const neutral

export
swallowM : Functor m => Swirl m e r (m o) -> Swirl m e r o
swallowM $ Done x     = Done x
swallowM $ Fail e     = Fail e
swallowM $ Yield x sw = Effect $ x <&> \x' => Yield x' $ swallowM sw
swallowM $ Effect msw = Effect $ msw <&> assert_total swallowM
swallowM $ BindR sw g = BindR (swallowM sw) (swallowM . g)
swallowM $ BindE sw h = BindE (swallowM sw) (swallowM . h)
swallowM $ Ensure l x = Ensure l $ swallowM x

--- Internal foldings ---

namespace ToResult

  export
  foldlRO : Functor m => (0 _ : IfUnsolved o'' Void) => (o' -> o -> o') -> o' -> (o' -> r -> r') -> Swirl m e r o -> Swirl m e r' o''
  foldlRO fo inito fr $ Done x     = Done $ fr inito x
  foldlRO fo inito fr $ Fail e     = Fail e
  foldlRO fo inito fr $ Yield x sw = foldlRO fo (fo inito x) fr sw
  foldlRO fo inito fr $ Effect msw = Effect $ msw <&> assert_total foldlRO fo inito fr
  foldlRO fo inito fr $ BindR x f  = BindR (foldlRO fo inito (,) x) $ \(into, r') => foldlRO fo into fr $ f r'
  foldlRO fo inito fr $ BindE x h  = BindE (foldlRO fo inito fr x) (foldlRO fo inito fr . h)
  foldlRO fo inito fr $ Ensure l x = Ensure l (foldlRO fo inito (,) x) `BindR` \(r', o', r) => Done $ fr o' (r', r)

  export %inline
  foldlRO' : Functor m => (0 _ : IfUnsolved o' Void) => (o -> o -> o) -> (o -> r -> r) -> Swirl m e r o -> Swirl m e r o'
  foldlRO' f g = foldlRO (Just .: maybe id f) Nothing (maybe id g)

  export %inline
  foldRO : Functor m => Semigroup o => (0 _ : IfUnsolved o' Void) => Swirl m e o o -> Swirl m e o o'
  foldRO = foldlRO' (<+>) (<+>)

  export %inline
  foldlO : Functor m =>
           (0 _ : IfUnsolved o' Void) =>
           (r -> o -> r) ->
           r ->
           Swirl m e () o ->
           Swirl m e r o'
  foldlO f x = foldlRO f x const

  export %inline
  foldO : Functor m =>
          Monoid o =>
          (0 _ : IfUnsolved o' Void) =>
          Swirl m e () o ->
          Swirl m e o o'
  foldO = foldRO . mapFst (const neutral)

  export %inline
  outputs : Functor m =>
            (0 _ : IfUnsolved o' Void) =>
            Swirl m e () o ->
            Swirl m e (SnocList o) o'
  outputs = foldlO (:<) [<]

namespace ToOutput

  foldlO'R : Functor m => (o' -> o -> o') -> o' -> Swirl m e r o -> Swirl m (e, o') (r, o') Void
  foldlO'R op init $ Done x     = Done (x, init)
  foldlO'R op init $ Fail e     = Fail (e, init)
  foldlO'R op init $ Yield x sw = foldlO'R op (init `op` x) sw
  foldlO'R op init $ Effect msw = Effect $ msw <&> assert_total foldlO'R op init
  foldlO'R op init $ BindR x f  = BindR (foldlO'R op init x) $ \(r', into) => foldlO'R op into $ f r'
  foldlO'R op init $ BindE x h  = BindE (foldlO'R op init x) $ \(e, into) => foldlO'R op into $ h e
  foldlO'R op init $ Ensure l x = Ensure l (foldlO'R op init x) `BindR` \(r', r, o') => Done ((r', r), o')

  ||| Emits the folded value once before both successful and failing ending.
  export
  foldlO' : Functor m => (o' -> o -> o') -> o' -> Swirl m e r o -> Swirl m e r o'
  foldlO' f i =
    (`BindE` \(e, o') => Yield o' $ Fail e) .
    (`BindR` \(x, o') => Yield o' $ Done x) .
      mapSnd absurd . foldlO'R f i

  ||| Emits the folded value once and only before the successful ending.
  export
  foldlO : Functor m => (o' -> o -> o') -> o' -> Swirl m e r o -> Swirl m e r o'
  foldlO f i =
    (`BindR` \(x, o') => Yield o' $ Done x) .
      mapError fst . mapSnd absurd . foldlO'R f i

  export
  foldO : Functor m => Monoid o => Swirl m e r o -> Swirl m e r o
  foldO = foldlO (<+>) neutral

  export
  outputs : Functor m => Swirl m e r o -> Swirl m e r (SnocList o)
  outputs = foldlO (:<) [<]

--- Flattenings ---

mergeSemi : Semigroup r => (r, Maybe r) -> r
mergeSemi (x, Nothing) = x
mergeSemi (x, Just y)  = x <+> y

namespace ComposeResults

  export
  mergeCtxs' : Applicative m => Applicative n => (r'' -> r' -> r'') -> r'' -> Swirl m e r (Swirl n e' r' o) -> Swirl (m . n) (Either e e') (r, r'') o
  mergeCtxs' ff fi $ Done x     = Done (x, fi)
  mergeCtxs' ff fi $ Fail e     = Fail $ Left e
  mergeCtxs' ff fi $ Yield x sw = mapCtx pure (mapError Right x) `BindR` \lr => mergeCtxs' ff (fi `ff` lr) sw
  mergeCtxs' ff fi $ Effect msw = Effect $ msw <&> pure . assert_total mergeCtxs' ff fi
  mergeCtxs' ff fi $ BindR x f  = BindR (mergeCtxs' ff fi x) $ \(y, ys) => mergeCtxs' ff ys $ f y
  mergeCtxs' ff fi $ BindE x h  = BindE (mergeCtxs' ff fi x) $ either (mergeCtxs' ff fi . h) (Fail . Right)
  mergeCtxs' ff fi $ Ensure l x = Ensure (mapCtx (map pure) l) (mergeCtxs' ff fi x) `BindR` \(rl, rr, rs) => succeed ((rl, rr), rs)

export
mergeCtxs : Applicative m => Applicative n => Semigroup r => Swirl m e r (Swirl n e r o) -> Swirl (m . n) e r o
mergeCtxs = (`BindR` Done . mergeSemi) . mapError fromEither . mergeCtxs' (\a, x => (a <+> Just x) @{Deep}) Nothing

namespace ComposeResults

  export
  squashOuts' : Functor m => (r'' -> r' -> r'') -> r'' -> Swirl m e r (Swirl m e' r' o) -> Swirl m (Either e e') (r, r'') o
  squashOuts' ff fi $ Done x     = Done (x, fi)
  squashOuts' ff fi $ Fail e     = Fail $ Left e
  squashOuts' ff fi $ Yield x sw = mapError Right x `BindR` \lr => squashOuts' ff (fi `ff` lr) sw
  squashOuts' ff fi $ Effect msw = Effect $ msw <&> assert_total squashOuts' ff fi
  squashOuts' ff fi $ BindR x f  = BindR (squashOuts' ff fi x) $ \(y, ys) => squashOuts' ff ys $ f y
  squashOuts' ff fi $ BindE x h  = BindE (squashOuts' ff fi x) $ either (squashOuts' ff fi . h) (Fail . Right)
  squashOuts' ff fi $ Ensure l x = Ensure l (squashOuts' ff fi x) `BindR` \(rl, rr, rs) => succeed ((rl, rr), rs)

export
squashOuts' : Functor m => Swirl m e r (Swirl m e' () o) -> Swirl m (Either e e') r o
squashOuts' = mapFst fst . squashOuts' (const id) ()

squashOuts : Functor m => Semigroup r => Swirl m e r (Swirl m e r o) -> Swirl m e r o
squashOuts = mapFst mergeSemi . mapError fromEither . squashOuts' (\a, x => (a <+> Just x) @{Deep}) Nothing

-- Unlike the `BindR` constuctor, this function is significantly not lazy on its first argument.
export %inline
bindR : Swirl m e r' o -> (r' -> Swirl m e r o) -> Swirl m e r o
bindR (Done x) f = f x
bindR (Fail e) _ = Fail e
bindR sw       f = BindR sw f

export %inline
handleRes : (r' -> Swirl m e r o) -> Swirl m e r' o -> Swirl m e r o
handleRes = flip bindR

squashRes : Swirl m e (Swirl m e r o) o -> Swirl m e r o
squashRes sw = sw `bindR` id

--- Filtration ---

export
mapEither' : Functor m =>
             (0 _ : IfUnsolved e Void) =>
             (0 _ : IfUnsolved r ()) =>
             (o -> Either e' o') ->
             Swirl m e r o ->
             Swirl m (Either e e') r o'
mapEither' f = squashOuts' . mapSnd (emitOrFail . f)

export
mapEither : Functor m => (o -> Either e o') -> Swirl m e r o -> Swirl m e r o'
mapEither = mapError fromEither .: mapEither'


export
mapMaybe : Functor m => (o -> Maybe o') -> Swirl m e r o -> Swirl m e r o'
mapMaybe f $ Done x     = Done x
mapMaybe f $ Fail e     = Fail e
mapMaybe f $ Yield x sw = case f x of
                            Nothing => mapMaybe f sw -- no common subexpression, tail recursion instead
                            Just y  => Yield y $ mapMaybe f sw
mapMaybe f $ Effect msw = Effect $ msw <&> assert_total mapMaybe f
mapMaybe f $ BindR sw g = BindR (mapMaybe f sw) (mapMaybe f . g)
mapMaybe f $ BindE sw h = BindE (mapMaybe f sw) (mapMaybe f . h)
mapMaybe f $ Ensure l x = Ensure l (mapMaybe f x)

export
filter : Functor m => (a -> Bool) -> Swirl m e r a -> Swirl m e r a
filter f $ Done x     = Done x
filter f $ Fail e     = Fail e
filter f $ Yield x sw = case f x of
                          False => filter f sw -- no common subexpression, tail recursion instead
                          True  => Yield x $ filter f sw
filter f $ Effect msw = Effect $ msw <&> assert_total filter f
filter f $ BindR sw g = BindR (filter f sw) (filter f . g)
filter f $ BindE sw h = BindE (filter f sw) (filter f . h)
filter f $ Ensure l x = Ensure l (filter f x)

--- Interleaving ---

namespace ComposeResults

--  mirrorAll : Functor m => Swirl m (Either e e') (r, r') (Either o o') -> Swirl m (Either e' e) (r', r) (Either o' o)
--  mirrorAll = mapError mirror . bimap swap mirror
--
--  ||| Interleaves both output emits and effects of both streams
--  export
--  interleaveOE : Functor m => Swirl m e r o -> Swirl m e' r' o' -> Swirl m (Either e e') (r, r') (Either o o')
--  interleaveOE (Done x)     sv = mapError Right $ bimap (x,) Right sv
--  interleaveOE (Fail e)     sv = Fail $ Left e -- maybe, try to continue as much as possible?
--  interleaveOE (Yield x sw) sv = Yield (Left x) $ mirrorAll $ interleaveOE {m} sv sw
--  interleaveOE (Effect msw) sv = Effect $ msw <&> \sw => mirrorAll $ assert_total $ interleaveOE sv sw
--  interleaveOE (BindR x f)  sv = ?interleave'_rhs_4
--  interleaveOE (BindE x h)  sv = ?interleave'_rhs_5
--  interleaveOE (Ensure l x) sv = ?interleave'_rhs_6

--- Functor, Applicative, Monad ---

-- Implementations over the last type argument --

export %inline
Functor m => Functor (Swirl m e r) where
  map = mapSnd

export
Functor m => Monoid r => Applicative (Swirl m e r) where
  pure x = Yield x $ Done neutral
  fs <*> xs = squashOuts $ fs <&> flip map xs

export
Functor m => Monoid r => Monad (Swirl m e r) where
  join = squashOuts

-- particular cases of monad combinators, ignoring the result
infixl 1 :>>=, =<<:, :>>

export %inline
(=<<:) : Functor m => (o' -> Swirl m e () o) -> Swirl m e r o' -> Swirl m e r o
(=<<:) = mapError fromEither .: squashOuts' .: mapSnd

export %inline
(:>>=) : Functor m => Swirl m e r o' -> (o' -> Swirl m e () o) -> Swirl m e r o
(:>>=) = flip (=<<:)

export %inline
(:>>) : Functor m => Swirl m e r () -> Lazy (Swirl m e () o) -> Swirl m e r o
(:>>) sw sv = mapError fromEither $ squashOuts' $ mapSnd (const sv) sw

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
      fs <*> xs = fs `bindR` (`mapFst` xs)

namespace Monad

  export
  [ByResult] Functor m => Monad (\r => Swirl m e r o)
    using Applicative.ByResult where
      join = squashRes
      (>>=) = bindR

namespace HasIO

  export
  [ByResult] HasIO io => HasIO (\r => Swirl io e r o)
    using Monad.ByResult where
      liftIO = succeed.by . liftIO

--- Error handling ---

export
handleError : (0 _ : IfUnsolved e' Void) =>
              (e -> Swirl m e' r o) -> Swirl m e r o -> Swirl m e' r o
handleError = flip $ BindE . delay

--- Finally funning ---

export
withFinally' : Functor m => Swirl m Void r' Void -> Swirl m e r o -> Swirl m e (r', r) o
withFinally' l x = Ensure l x

export
withFinally : Functor m => Swirl m Void () Void -> Swirl m e r o -> Swirl m e r o
withFinally = mapFst snd .: withFinally'

export
bracket' : Functor m =>
           (0 _ : IfUnsolved e Void) =>
           (0 _ : IfUnsolved o Void) =>
           (init : Swirl m e res o) ->
           (cleanup : res -> Swirl m Void r' Void) ->
           (action : res -> Swirl m e r o) ->
           Swirl m e (r', r) o
bracket' init cleanup action = init `bindR` \res => withFinally' (cleanup res) (action res)

export
bracket : Functor m =>
          (0 _ : IfUnsolved e Void) =>
          (0 _ : IfUnsolved o Void) =>
          (init : Swirl m e res o) ->
          (cleanup : res -> Swirl m Void () Void) ->
          (action : res -> Swirl m e r o) ->
          Swirl m e r o
bracket init cleanup action = init `bindR` \res => withFinally (cleanup res) (action res)

export
bracketO : Functor m =>
           Monoid r =>
           (0 _ : IfUnsolved e Void) =>
           (0 _ : IfUnsolved r ()) =>
           (init : Swirl m e res Void) ->
           (cleanup : res -> Swirl m Void r Void) ->
           Swirl m e r res
bracketO init cleanup = bimap fst snd $ emitRes' id $ bracket' init cleanup succeed

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
tickUntil sw = map absurd sw `bindR` \stop => if stop then succeed neutral else Yield () $ tickUntil sw

--- Cutting outputs ---

take' : Functor m => Nat -> Swirl m e r o -> Swirl m (Nat, e) (Nat, r) o
take' Z     sw           = mapError (Z,) $ mapFst (Z,) $ forgetO sw
take' (S k) $ Yield x sw = Yield x $ take' k sw
take' n     $ Done x     = Done (n, x)
take' n     $ Fail e     = Fail (n, e)
take' n     $ Effect msw = Effect $ msw <&> assert_total take' n
take' n     $ BindR x f  = BindR (take' n x) $ \(n', r') => take' n' $ f r'
take' n     $ BindE x h  = BindE (take' n x) $ \(n', e') => take' n' $ h e'
take' n     $ Ensure l x = Ensure l (take' n x) `BindR` \(r', n', r) => Done (n, r', r)

export
take : Functor m => Nat -> Swirl m e r o -> Swirl m e r o
take = mapError snd .: mapFst snd .: take'

-- Additional bool parameter's semantics is roughtly the last value returned by the condition function
%inline %tcinline
twCont : Functor m =>
         Bool ->
         (succMap : Lazy (Swirl m (Bool, e) (Bool, r) o) -> Swirl m (Bool, e) (Bool, r) o) ->
         (o -> Bool) ->
         Swirl m e r o ->
         Swirl m (Bool, e) (Bool, r) o
takeWhile' : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
takeWhile' _ $ Done x     = Done (True, x)
takeWhile' _ $ Fail e     = Fail (True, e)
takeWhile' w $ Yield x sw = twCont (w x) (Yield x) w sw
takeWhile' w $ Effect msw = Effect $ msw <&> assert_total takeWhile' w
takeWhile' w $ BindR x f  = BindR (takeWhile' w x) $ \(ct, r') => twCont ct force w $ f r'
takeWhile' w $ BindE x h  = BindE (takeWhile' w x) $ \(ct, e') => twCont ct force w $ h e'
takeWhile' w $ Ensure l x = Ensure l (takeWhile' w x) `BindR` \(r', b', r) => Done (b', r', r)
twCont False s _ sw = mapError (False,) $ mapFst (False,) $ forgetO sw
twCont True  s w sw = s $ delay $ takeWhile' w sw

export
takeWhile : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m e r o
takeWhile = mapError snd .: mapFst snd .: takeWhile'

drop' : Functor m => Nat -> Swirl m e r o -> Swirl m (Nat, e) (Nat, r) o
drop' Z     sw           = mapError (Z,) $ mapFst (Z,) sw
drop' (S k) $ Yield x sw = drop' k sw
drop' n     $ Done x     = Done (n, x)
drop' n     $ Fail e     = Fail (n, e)
drop' n     $ Effect msw = Effect $ msw <&> assert_total drop' n
drop' n     $ BindR x f  = BindR (drop' n x) $ \(n', r') => drop' n' $ f r'
drop' n     $ BindE x h  = BindE (drop' n x) $ \(n', e') => drop' n' $ h e'
drop' n     $ Ensure l x = Ensure l (drop' n x) `BindR` \(r', n', r) => Done (n, r', r)

export
drop : Functor m => Nat -> Swirl m e r o -> Swirl m e r o
drop = mapError snd .: mapFst snd .: drop'

-- Additional bool parameter's semantics is roughtly the last value returned by the condition function
%inline %tcinline
dwCont : Functor m =>
         Bool ->
         (succMap : Lazy (Swirl m e r o) -> Swirl m e r o) ->
         (o -> Bool) ->
         Swirl m e r o ->
         Swirl m (Bool, e) (Bool, r) o
dropWhile' : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
dwCont True  s w sw = dropWhile' w sw
dwCont False s _ sw = mapError (False,) $ mapFst (False,) $ s sw
dropWhile' _ $ Done x     = Done (True, x)
dropWhile' _ $ Fail e     = Fail (True, e)
dropWhile' w $ Yield x sw = dwCont (w x) (Yield x) w sw
dropWhile' w $ Effect msw = Effect $ msw <&> assert_total dropWhile' w
dropWhile' w $ BindR x f  = BindR (dropWhile' w x) $ \(ct, r') => dwCont ct force w $ f r'
dropWhile' w $ BindE x h  = BindE (dropWhile' w x) $ \(ct, e') => dwCont ct force w $ h e'
dropWhile' w $ Ensure l x = Ensure l (dropWhile' w x) `BindR` \(r', b', r) => Done (b', r', r)

export
dropWhile : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m e r o
dropWhile = mapError snd .: mapFst snd .: dropWhile'

--- Extension ---

intersperseOuts' : Functor m => (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
%inline prepO : Functor m => Bool -> (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
prepO True  sep sw = mapError ((True,) . fromEither) $ mapFst (True,) $ squashOuts' $ map (\x' => concat const sep $ emit x') sw
prepO False sep sw = intersperseOuts' sep sw
intersperseOuts' sep $ Done x     = Done (False, x)
intersperseOuts' sep $ Fail e     = Fail (False, e)
intersperseOuts' sep $ Yield x sw = Yield x $ prepO True sep sw
intersperseOuts' sep $ Effect msw = Effect $ msw <&> assert_total intersperseOuts' sep
intersperseOuts' sep $ BindR x f  = BindR (intersperseOuts' sep x) $ \(fwas, r') => prepO fwas sep $ f r'
-- CAUTION! the following `assert_total` has no clear evidence of being valid
intersperseOuts' sep $ BindE x h  = BindE (assert_total intersperseOuts' (mapError Right sep) (mapError Left x)) $ \(fwas, ee) =>
                                      case ee of
                                        Left e' => prepO fwas sep $ h e'
                                        Right e => Fail (fwas, e)
intersperseOuts' sep $ Ensure l x = Ensure l (intersperseOuts' sep x) `BindR` \(r', b, r) => Done (b, r', r)

export
intersperseOuts : Functor m => (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m e r o
intersperseOuts = mapError snd .: mapFst snd .: intersperseOuts'

export
iterateAlong : Functor m => (i -> i) -> i -> Swirl m e r o -> Swirl m e r (i, o)
iterateAlong next = mapError snd .: mapFst snd .: go where
  go : forall e, r. i -> Swirl m e r o -> Swirl m (i, e) (i, r) (i, o)
  go n $ Done x     = Done (n, x)
  go n $ Fail e     = Fail (n, e)
  go n $ Yield x sw = Yield (n, x) $ go (next n) sw
  go n $ Effect msw = Effect $ msw <&> assert_total go n
  go n $ BindR x f  = go n x `BindR` \(n', r') => go n' $ f r'
  go n $ BindE x h  = go n x `BindE` \(n', e') => go n' $ h e'
  go n $ Ensure l x = Ensure l (go n x) `BindR` \(r', i, r) => Done (i, r', r)

export %inline
zipWithIndex : Functor m => Swirl m e r o -> Swirl m e r (Nat, o)
zipWithIndex = iterateAlong S Z

--- Eliminators ---

--toLazyList : Swirl Identity e r o -> (Either e r, LazyList o)
--toLazyList $ Done x       = (Right x, [])
--toLazyList $ Fail e       = (Left e, [])
--toLazyList $ Yield x sw   = x :: toLazyList sw
--toLazyList e@(Effect msw) = toLazyList $ assert_smaller e $ runIdentity msw
--toLazyList $ BindR x f    = ?toLazyList_rhs_4
--toLazyList $ BindE x h    = ?toLazyList_rhs_5

data Ctx : (Type -> Type) -> (inE, inR, outE, outR : Type) -> Type where
  Nil : Ctx m e r e r
  BiR : (r' -> Swirl m e r Void) -> Ctx m e r e0 r0 -> Ctx m e r' e0 r0
  BiE : (e' -> Swirl m e r Void) -> Ctx m e r e0 r0 -> Ctx m e' r e0 r0
  Ens : Swirl m Void r' Void -> Ctx m e (r', r) e0 r0 -> Ctx m e r e0 r0

data St : (Type -> Type) -> (finalE, finalR : Type) -> Type where
  AtCtx : Swirl m e' r' Void -> Ctx m e' r' e r -> St m e r

data StLT : St m e r -> St m e r -> Type where
  BiRLT : (sw `AtCtx` ctx) `StLT` (sv `AtCtx` BiR f ctx)
  BiELT : (sw `AtCtx` ctx) `StLT` (sv `AtCtx` BiE f ctx)
  EnsLT : (sw `AtCtx` ctx) `StLT` (sv `AtCtx` Ens l ctx)

  SwBR : (Force sw `AtCtx` BiR f         ctx) `StLT` (BindR sw f `AtCtx` ctx)
  SwBE : (Force sw `AtCtx` BiE f         ctx) `StLT` (BindE sw f `AtCtx` ctx)
  SwEn : (Force sw `AtCtx` Ens (Force l) ctx) `StLT` (Ensure l sw `AtCtx` ctx)

  EfLT : (sw `AtCtx` ctx) `StLT` (Effect msw `AtCtx` ctx)
  -- No relation between `sw` and `msw` depicted here :-(

covering
WellFounded (St m e r) StLT where
  wellFounded st = wellFounded st

-- Why does the following function pass totality checker once we have only covering wellfoundness implementation?

export
runSwirlE : MonadRec m => Swirl m e r Void -> m $ Either e r
runSwirlE sw = trWellFounded (sw `AtCtx` []) () $ \sw, () => case sw of

  Done x `AtCtx` []        => pure $ Done $ Right x
  Done x `AtCtx` BiR f ct  => pure $ Cont (f x `AtCtx` ct) BiRLT ()
  Done x `AtCtx` BiE _ ct  => pure $ Cont (Done x `AtCtx` ct) BiELT ()
  Done x `AtCtx` Ens sv ct => pure $ Cont ((mapError absurd $ mapFst (,x) $ sv) `AtCtx` ct) EnsLT ()

  Fail e `AtCtx` []        => pure $ Done $ Left e
  Fail e `AtCtx` BiR _ ct  => pure $ Cont (Fail e `AtCtx` ct) BiRLT ()
  Fail e `AtCtx` BiE h ct  => pure $ Cont (h e `AtCtx` ct) BiELT ()
  Fail e `AtCtx` Ens sv ct => pure $ Cont ((mapError absurd (forgetR sv) `andThen` Fail e) `AtCtx` ct) EnsLT ()

  Effect msw `AtCtx` ct => msw <&> \sw => Cont (sw `AtCtx` ct) EfLT ()

  BindR sw f  `AtCtx` ct => pure $ Cont (sw `AtCtx` BiR f ct) SwBR ()
  BindE sw h  `AtCtx` ct => pure $ Cont (sw `AtCtx` BiE h ct) SwBE ()
  Ensure l sw `AtCtx` ct => pure $ Cont (sw `AtCtx` Ens l ct) SwEn ()

export
runSwirl : MonadRec m => Swirl m Void a Void -> m a
runSwirl = map (\(Right x) => x) . runSwirlE
