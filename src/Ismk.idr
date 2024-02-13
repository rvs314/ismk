module Ismk

import KStream
import Decidable.Equality
import Data.Fuel

data Stage = StagingTime | RunTime

interface Persist (k : Stage -> Type) where
  persist : k StagingTime -> k RunTime

record Name (s : Stage) where
  constructor MkName
  unName : Nat

DecEq (Name s) where
  decEq (MkName k) (MkName j) with (decEq k j)
    decEq (MkName k) (MkName k) | (Yes Refl) = Yes Refl
    decEq (MkName k) (MkName j) | (No contra) = No (\case Refl => contra Refl)

Eq (Name s) where
  (==) = (==) `on` unName

Ord (Name s) where
  compare = compare `on` unName

Persist Name where
  persist (MkName unName) = MkName unName

incr : Name s -> Name s
incr (MkName k) = MkName (S k)

data Val : Stage -> Type where
  Nil  : Val s
  (::) : Val s -> Val s -> Val s
  Sym  : String -> Val s
  Var  : Name s -> Val s

FromString (Val s) where
  fromString = Sym

Persist Val where 
  persist []        = []
  persist (x :: y)  = persist x :: persist y
  persist (Sym str) = Sym str
  persist (Var nm)  = Var $ persist nm

record Trail (s : Stage) where
  constructor MkTrail
  unTrail : List (Name s, Val s)

Persist Trail where
  persist = MkTrail . map (bimap persist persist) . unTrail

infixr 2 /\ 
infixl 3 \/ 
infix 6 =:=

data Goal : Stage -> Type where
  Fail : Goal s 
  Succeed : Goal s 
  (=:=) : Val s -> Val s -> Goal s
  (/\) : Lazy (Goal s) -> Lazy (Goal s) -> Goal s
  (\/) : Lazy (Goal s) -> Lazy (Goal s) -> Goal s
  Fresh : (Name s -> Goal s) -> Goal s
  Later : Goal RunTime -> Goal StagingTime
  Gather : Goal StagingTime -> Goal StagingTime
  Fallback : Goal StagingTime -> Goal StagingTime

fresh : (Val s -> Goal s) -> Goal s
fresh f = Fresh (f . Var)

Persist Goal where
  persist Fail = Fail
  persist Succeed = Succeed
  persist (x =:= y) = persist x =:= persist y
  persist (x /\ y) = persist x /\ persist y
  persist (x \/ y) = persist x \/ persist y
  persist (Fresh f) = Fresh (\case (MkName nm) => persist $ f (MkName nm))
  persist (Later x) = x
  persist (Gather x) = persist x
  persist (Fallback x) = persist x

disj : List (Goal s) -> Goal s
disj = foldl ((\/) `on` delay) Fail

conj : List (Goal s) -> Goal s
conj = foldl ((/\) `on` delay) Succeed

data FallbackStatus = OutsideFallback | InsideFallback

Payload : Stage -> Type
Payload StagingTime = (Goal RunTime, FallbackStatus)
Payload RunTime = ()

record State (s : Stage) where
  constructor MkState
  trail : Trail s
  counter : Name s
  payload : Payload s

Persist State where
  persist (MkState trail counter payload) = MkState (persist trail) (persist counter) ()

empty : {s : Stage} -> State s
empty {s} = MkState (MkTrail []) (MkName 0) (payload s)
  where
    payload : (s : Stage) -> Payload s
    payload StagingTime = (Succeed, OutsideFallback)
    payload RunTime = ()

bind : Name s -> Val s -> State s -> State s
bind n v (MkState (MkTrail bindings) counter payload) = 
     MkState (MkTrail ((n, v) :: bindings)) counter payload

gensym : State s -> (Name s, State s)
gensym (MkState trail counter payload) = (counter, MkState trail (incr counter) payload)

walk : (trail : Trail s) -> (val : Val s) -> Val s
walk (MkTrail []) (Var x) = Var x
walk (MkTrail ((nm, z) :: xs)) (Var x) with (decEq nm x)
  walk (MkTrail ((nm, z) :: xs)) (Var nm) | (Yes Refl) = walk (MkTrail xs) z
  walk (MkTrail ((nm, z) :: xs)) (Var x)  | (No contra) = walk (MkTrail xs) (Var x)
walk trail con = con

walks : (trail : Trail s) -> (val : Val s) -> Val s
walks trail val with (walk trail val)
  walks trail val | [] = []
  walks trail val | (x :: y) = walk trail x :: walk trail y
  walks trail val | (Sym     str) = val
  walks trail val | (Var     x) = val

unify : Val s -> Val s -> State s -> KStream (State s)
unify l r z with (walk (trail z) l, walk (trail z) r)
  unify l r z | ((Var x), (Var y)) = 
                let mx = max x y
                    mn = min x y
                in [bind mx (Var mn) z]
  unify l r z | (x, y@(Var _))     = unify y x z
  unify l r z | ((Var x),    y)    = [bind x y z]
  unify l r z | ((Sym str),  (Sym str1)) = if str == str1 then [z] else []
  unify l r z | ((a :: d), (p :: q)) = unify a p z >>= unify d q
  unify l r z | ([],         [])   = [z]
  unify l r z | (_,         _)    = []

passOnFallback : State StagingTime -> Lazy (KStream (State StagingTime)) -> KStream (State StagingTime)
passOnFallback s@(MkState trail counter (x, InsideFallback)) y  = [s]
passOnFallback (MkState trail counter (x, OutsideFallback)) y = Force y

interpret : Goal s -> (State s) -> KStream (State s)
interpret Fail y = []
interpret Succeed y = [y]
interpret (x =:= z) y = unify x z y
interpret (x /\ z) y = interpret x y >>= interpret z
interpret (x \/ z) y = interpret x y <|> interpret z y
interpret (Fresh f) y = let (fresh, st) = gensym y in 
                        interpret (f fresh) st
interpret {s=StagingTime} (Later x) s@(MkState trail counter (code, fbs)) = 
  [ MkState trail counter ((x /\ code), fbs) ]
interpret {s=StagingTime} (Gather x) y = 
  passOnFallback y $
  let options = toList forever $ interpret x y in 
  [ MkState (trail y) (counter y) 
            (disj $ map (\case (MkState _ _ (c, _)) => c) options, OutsideFallback) ]
interpret {s=StagingTime} (Fallback x) y = 
  passOnFallback y $
  case take forever 2 $ interpret x ({ payload $= mapSnd (const InsideFallback) } y) of
    []  => []
    [x] => [x]
    _   => interpret (Later (persist x)) y

Error : Type
Error = String

run : Goal RunTime -> KStream (State RunTime)
run x = interpret x empty

runStaged : Goal StagingTime -> Either Error (KStream (State RunTime))
runStaged x = let results = interpret x empty
                  result = !(case fst $ split forever 2 results of
                              []  => Left "Staging failed"
                              [x] => Right x
                              _   => Left "Staging was non-deterministic")
              in pure $ interpret (fst (payload result)) $ persist result

oneOrTwoO : Goal s
oneOrTwoO = fresh $ \x => x =:= "one" \/ x =:= "two"
