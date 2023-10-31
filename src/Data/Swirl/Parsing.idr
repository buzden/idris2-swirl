module Data.Swirl.Parsing

import public Data.Swirl

%default total

--- Parsing ---

-- TODO to add a documantation example, say, by a swirl of chars produce a swirl of strings separated by EOL

public export
data WhetherConsumeLast a = ConsumeLast a | DoNotConsumeLast a

export
(.val) : WhetherConsumeLast a -> a
(.val) $ ConsumeLast x      = x
(.val) $ DoNotConsumeLast x = x

export
ifConsumes : WhetherConsumeLast a -> (cons, notCons : Lazy b) -> b
ifConsumes (ConsumeLast _     ) cons notCons = cons
ifConsumes (DoNotConsumeLast _) cons notCons = notCons

public export
Functor WhetherConsumeLast where
  map f $ ConsumeLast x      = ConsumeLast $ f x
  map f $ DoNotConsumeLast x = DoNotConsumeLast $ f x

public export
record Parser m st e' r r' o o' where
  [search o' o]
  constructor MkParser
  initSeed  : st
  parseStep : o -> st -> Either st $ WhetherConsumeLast $ Swirl m e' () o'
  manageFin : st -> r -> Swirl m e' r' o'

%name Parser pr, ps

export
Functor m => Functor (Parser m st e' r r' o) where
  map f = {parseStep $= (map @{Compose} (mapSnd f) .:), manageFin $= (mapSnd f .:)}

%inline
(.passFin) : Parser m st e' r'' r' o o' -> Parser m st e' r (st, r) o o'
(.passFin) = {manageFin := curry succeed}

export
parseOnce : Functor m =>
            (0 _ : IfUnsolved r' ()) =>
            (0 _ : IfUnsolved o' Void) =>
            Parser m st e'' r r' o o' ->
            Swirl m e r o -> Swirl m (Either e e'') (Either r' $ Swirl m e r o) o'
parseOnce pr = mapError (mapFst snd) . go pr pr.initSeed where
  go : forall st, e, e'', r, r', o, o'.
       Parser m st e'' r r' o o' ->
       st ->
       Swirl m e r o ->
       Swirl m (Either (st, e) e'') (Either r' $ Swirl m e r o) o'
  go pr s $ Done x         = mapError Right $ mapFst Left $ pr.manageFin s x
  go pr s $ Fail e         = fail $ Left (s, e)
  go pr s sw'@(Yield x sw) = case pr.parseStep x s of
                               Left s'   => go pr s' sw
                               Right sub => mapFst (const $ Right $ ifConsumes sub sw sw') $ mapError Right sub.val
  go pr s $ Effect msw     = Effect $ msw <&> assert_total go pr s
  go pr s $ BindR sw g     = go pr.passFin s sw `bindR` \case
                               Left (s', ir) => go pr s' $ g ir
                               Right cont    => succeed $ Right $ cont `bindR` g
  go pr s $ BindE sw h     = BindE (mapFst (map Left) $ go pr.passFin s sw) (\case
                                 Left (s', ei) => mapFst (map Right) $ go pr.passFin s' $ h ei
                                 Right ep      => fail $ Right ep
                               ) `BindR` \case
                                 Left (s', r) => mapFst Left $ mapError Right $ pr.manageFin s' r
                                 Right cont   => succeed $ Right $ either (`BindE` h) id cont
  go pr s $ Ensure l x     = Ensure l (go pr.passFin s x) `BindR` \case
                               (rf, Left (s', r)) => mapError Right $ mapFst Left $ pr.manageFin s' (rf, r)
                               (rf, Right cont)   => succeed $ Right $ mapFst (rf,) cont

export
parseAll : Functor m =>
           (0 _ : IfUnsolved r' ()) =>
           (0 _ : IfUnsolved o' Void) =>
           Parser m st e' r r' o o' ->
           Swirl m e r o -> Swirl m (Either e e') r' o'
parseAll pr sw = (parseAll' sw >>= mapError Right . uncurry pr.manageFin) @{ByResult} where
  parseAll' : Swirl m e r o -> Swirl m (Either e e') (st, r) o'
  parseAll' sw = parseOnce pr.passFin sw `bindR` \case
                   Left x     => succeed x
                   Right cont => parseAll' $ assert_smaller sw cont
