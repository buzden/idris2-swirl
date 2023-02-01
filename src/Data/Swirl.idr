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
  Ensure : Lazy (Swirl m Void r' Void) -> Lazy (Swirl m e r o) -> Swirl m e (r', r) o

%name Swirl sw, sv, su

-- Discussion:
--
-- - `Effect` constructor
--
--   `m (Lazy ...)` in `Effect` exploits totality checker's bug to make the type as if it's strictly positive.
--   Actually, it seems, the whole `data` definition should be `covering`.
--   But, by the idea, this `m` must be `Functor`, and I'm not sure whether this is possible to get the situation
--   when this data type really is not total.
--
-- - `Ensure` constructor, output parameter of "finally" section.
--
--   the `finally` part must not emit values because of the following:
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
  bimap fr fo $ Ensure l x = Ensure l (bimap id fo x) `BindR` Done . fr

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

--- Basic creation ---

||| A postfix function modifier to create an effected swirl creation.
||| E.g. `emit v` emits `v` without any action, and `emit.by mv` emits a value of type `v` from `mv` of type `m v`.
export %inline
(.by) : Functor m => (x -> Swirl m e r o) -> m x -> Swirl m e r o
f.by = Effect . map (delay . f)

-- Output --

export %inline
emit : Monoid r =>
       (0 _ : IfUnsolved e Void) =>
       (0 _ : IfUnsolved r ()) =>
       o -> Swirl m e r o
emit x = Yield x $ Done neutral

export
preEmits : (0 _ : IfUnsolved e Void) =>
           Swirl m e r o ->
           LazyList o ->
           Swirl m e r o
preEmits = foldrLazy Yield . delay

export
emits : Monoid r =>
        (0 _ : IfUnsolved e Void) =>
        (0 _ : IfUnsolved r ()) =>
        LazyList o ->
        Swirl m e r o
emits = preEmits $ Done neutral

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

--- Internal foldings ---

namespace ToResult

  export
  foldrRO : Functor m => (0 _ : IfUnsolved o' Void) => (o -> r -> r) -> Swirl m e r o -> Swirl m e r o'

  export
  foldRO : Functor m => Semigroup o => (0 _ : IfUnsolved o' Void) => Swirl m e o o -> Swirl m e o o'
  foldRO = foldrRO (<+>)

  export
  foldrO : Functor m =>
           (0 _ : IfUnsolved o' Void) =>
           (o -> r -> r) ->
           r ->
           Swirl m e () o ->
           Swirl m e r o'
  foldrO f x = foldrRO f . mapFst (const x)

  export
  foldO : Functor m =>
          Monoid o =>
          (0 _ : IfUnsolved o' Void) =>
          Swirl m e () o ->
          Swirl m e o o'
  foldO = foldRO . mapFst (const neutral)

  export
  outputs : Functor m =>
            (0 _ : IfUnsolved o' Void) =>
            Swirl m e () o ->
            Swirl m e (List o) o'
  outputs = foldrO (::) []

namespace ToOutput

  export
  foldlO : Functor m => (o' -> o -> o') -> o' -> Swirl m e r o -> Swirl m e r o'
  foldlO op init $ Done x     = Done x
  foldlO op init $ Fail e     = Fail e
  foldlO op init $ Yield x sw = foldlO op (init `op` x) sw
  foldlO op init $ Effect msw = Effect $ msw <&> mapLazy (assert_total foldlO op init)
  foldlO op init $ BindR x f  = BindR (foldlO op init x) (foldlO op init . f)
  foldlO op init $ BindE x h  = BindE (foldlO op init x) (foldlO op init . h)
  foldlO op init $ Ensure l x = Ensure l (foldlO op init x)

  export
  foldO : Functor m => Monoid o => Swirl m e r o -> Swirl m e r o
  foldO = foldlO (<+>) neutral

  export
  outputs : Functor m => Swirl m e r o -> Swirl m e r (SnocList o)
  outputs = foldlO (:<) [<]

--- Flattenings ---

namespace ComposeResults

  export
  mergeCtxs' : Applicative m => Applicative n => Swirl m e r (Swirl n e'' r'' o) -> Swirl (m . n) (Either e e'') (r, List r'') o
  mergeCtxs' $ Done x     = Done (x, [])
  mergeCtxs' $ Fail e     = Fail $ Left e
  mergeCtxs' $ Yield x sw = concat @{Compose} (mapSnd . (::)) (mapCtx pure $ mapError Right x) (mergeCtxs' sw)
  mergeCtxs' $ Effect msw = Effect $ msw <&> pure . mapLazy (assert_total mergeCtxs')
  mergeCtxs' $ BindR x f  = BindR (mergeCtxs' x) $ \(y, ys) => let _ = Functor.Compose in mapFst (mapSnd (ys ++)) $ mergeCtxs' $ f y
  mergeCtxs' $ BindE x h  = BindE (mergeCtxs' x) $ either (mergeCtxs' . h) (Fail . Right)
  mergeCtxs' $ Ensure l x = Ensure (mapCtx (map pure) l) (mergeCtxs' x) `BindR` \(rl, rr, rs) => succeed ((rl, rr), rs)

  export
  mergeCtxs : Applicative m => Applicative n => (r' -> r -> r) -> Swirl m e r (Swirl n e r' o) -> Swirl (m . n) e r o
  mergeCtxs fr = let _ = Functor.Compose in mapFst (uncurry $ foldr fr) . mapError fromEither . mergeCtxs'

export
mergeCtxs : Applicative m => Applicative n => Semigroup r => Swirl m e r (Swirl n e r o) -> Swirl (m . n) e r o
mergeCtxs = mergeCtxs (<+>)

namespace ComposeResults

  -- TODO The following function stores the results of the whole process as its result
  --      with no intemediate joining, which must be uneffective and should be redone.
  --      The same applies to the `mergeCtxs'` above.

  export
  squashOuts' : Functor m => Swirl m e r (Swirl m e' r' o) -> Swirl m (Either e e') (r, List r') o
  squashOuts' $ Done x     = Done (x, [])
  squashOuts' $ Fail e     = Fail $ Left e
  squashOuts' $ Yield x sw = concat (mapSnd . (::)) (mapError Right x) (squashOuts' sw)
  squashOuts' $ Effect msw = Effect $ msw <&> mapLazy (assert_total squashOuts')
  squashOuts' $ BindR x f  = BindR (squashOuts' x) $ \(y, ys) => mapFst (mapSnd (ys ++)) $ squashOuts' $ f y
  squashOuts' $ BindE x h  = BindE (squashOuts' x) $ either (squashOuts' . h) (Fail . Right)
  squashOuts' $ Ensure l x = Ensure l (squashOuts' x) `BindR` \(rl, rr, rs) => succeed ((rl, rr), rs)

  export
  squashOuts : Functor m => (r' -> r -> r) -> Swirl m e r (Swirl m e r' o) -> Swirl m e r o
  squashOuts fr = mapFst (uncurry $ foldr fr) . mapError fromEither . squashOuts'

squashOuts : Functor m => Semigroup r => Swirl m e r (Swirl m e r o) -> Swirl m e r o
squashOuts = squashOuts (<+>)

squashRes : Swirl m e (Swirl m e r o) o -> Swirl m e r o
squashRes $ Done sw = sw
squashRes $ Fail x  = Fail x
squashRes sw        = sw `BindR` id

--- Filtration ---

export
mapEither' : Functor m =>
             (0 _ : IfUnsolved e Void) =>
             (0 _ : IfUnsolved r ()) =>
             (o -> Either e' o') ->
             Swirl m e r o ->
             Swirl m (Either e e') r o'
mapEither' f = mapFst fst . squashOuts' . mapSnd (emitOrFail . f)

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
mapMaybe f $ Effect msw = Effect $ msw <&> mapLazy (assert_total mapMaybe f)
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
filter f $ Effect msw = Effect $ msw <&> mapLazy (assert_total filter f)
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
--  interleaveOE (Effect msw) sv = Effect $ msw <&> mapLazy (\sw => mirrorAll $ assert_total $ interleaveOE sv sw)
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
bracket' init cleanup action = (init >>= \res => withFinally' (cleanup res) (action res)) @{ByResult}

export
bracket : Functor m =>
          (0 _ : IfUnsolved e Void) =>
          (0 _ : IfUnsolved o Void) =>
          (init : Swirl m e res o) ->
          (cleanup : res -> Swirl m Void () Void) ->
          (action : res -> Swirl m e r o) ->
          Swirl m e r o
bracket init cleanup action = (init >>= \res => withFinally (cleanup res) (action res)) @{ByResult}

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
tickUntil sw = (map absurd sw >>= \stop => if stop then succeed neutral else Yield () $ tickUntil sw) @{ByResult}

--- Cutting outputs ---

take' : Functor m => Nat -> Swirl m e r o -> Swirl m (Nat, e) (Nat, r) o
take' Z     sw           = mapError (Z,) $ mapFst (Z,) $ forgetO sw
take' (S k) $ Yield x sw = Yield x $ take' k sw
take' n     $ Done x     = Done (n, x)
take' n     $ Fail e     = Fail (n, e)
take' n     $ Effect msw = Effect $ msw <&> mapLazy (assert_total take' n)
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
takeWhile' w $ Effect msw = Effect $ msw <&> mapLazy (assert_total takeWhile' w)
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
drop' n     $ Effect msw = Effect $ msw <&> mapLazy (assert_total drop' n)
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
dropWhile' w $ Effect msw = Effect $ msw <&> mapLazy (assert_total dropWhile' w)
dropWhile' w $ BindR x f  = BindR (dropWhile' w x) $ \(ct, r') => dwCont ct force w $ f r'
dropWhile' w $ BindE x h  = BindE (dropWhile' w x) $ \(ct, e') => dwCont ct force w $ h e'
dropWhile' w $ Ensure l x = Ensure l (dropWhile' w x) `BindR` \(r', b', r) => Done (b', r', r)

export
dropWhile : Functor m => (o -> Bool) -> Swirl m e r o -> Swirl m e r o
dropWhile = mapError snd .: mapFst snd .: dropWhile'

--- Extension ---

intersperseOuts' : Functor m => (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
%inline prepO : Functor m => Bool -> (sep : Swirl m e () o) -> Swirl m e r o -> Swirl m (Bool, e) (Bool, r) o
prepO True  sep sw = mapError (True,) $ mapFst (True,) $ squashOuts (const id) $ map (\x' => concat const sep $ emit x') sw
prepO False sep sw = intersperseOuts' sep sw
intersperseOuts' sep $ Done x     = Done (False, x)
intersperseOuts' sep $ Fail e     = Fail (False, e)
intersperseOuts' sep $ Yield x sw = Yield x $ prepO True sep sw
intersperseOuts' sep $ Effect msw = Effect $ msw <&> mapLazy (assert_total intersperseOuts' sep)
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

--- Eliminators ---

--export
--toLazyList : Swirl Identity Void () a -> LazyList a
--toLazyList $ Done ()    = []
--toLazyList $ Yield x sw = x :: toLazyList sw
--toLazyList $ Effect msw = assert_total toLazyList $ runIdentity msw
--toLazyList $ BindR x f  = ?toLazyList_rhs_4
--toLazyList $ BindE x h  = ?toLazyList_rhs_5

{-

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
