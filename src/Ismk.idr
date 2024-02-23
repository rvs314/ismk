module Ismk

import IStream
import Decidable.Equality
import Data.Fuel
import Data.Vect

%default total

public export
data Stage = StagingTime | RunTime

public export
interface Persist (k : (0 s : Stage) -> Type) where
  persist : k StagingTime -> k RunTime

public export
record Name (0 s : Stage) where
  constructor MkName
  unName : Nat

public export
DecEq (Name s) where
  decEq (MkName k) (MkName j) with (decEq k j)
    decEq (MkName k) (MkName k) | (Yes Refl) = Yes Refl
    decEq (MkName k) (MkName j) | (No contra) = No (\case Refl => contra Refl)

public export
Eq (Name s) where
  (==) = (==) `on` unName

public export
Ord (Name s) where
  compare = compare `on` unName

public export
Persist Name where
  persist (MkName unName) = MkName unName

public export
incr : Name s -> Name s
incr (MkName k) = MkName (S k)

public export
data Val : (0 _ : Stage) -> Type where
  Nil  : Val s
  Numb : Integer -> Val s
  (::) : Val s -> Val s -> Val s
  Sym  : String -> Val s
  Var  : Name s -> Val s

export
FromString (Val s) where
  fromString = Sym

export
fromInteger : Integer -> Val s
fromInteger = Numb

public export
Persist Val where 
  persist []        = []
  persist (x :: y)  = persist x :: persist y
  persist (Sym str) = Sym str
  persist (Numb n)  = Numb n
  persist (Var nm)  = Var $ persist nm

public export
Eq (Val s) where
  [] == [] = True
  (x :: y) == (z :: w) = x == z && y == w
  (Sym str) == (Sym str1) = str == str1
  (Var x) == (Var y) = x == y
  (Numb k) == (Numb j) = k == j
  _ == _ = False

-- TODO: Rename to 'Substitution'
public export
record Trail (0 s : Stage) where
  constructor MkTrail
  unTrail : List (Name s, Val s)

public export
Persist Trail where
  persist = MkTrail . map (bimap persist persist) . unTrail

infixr 3 /\ 
infixl 2 \/ 
infix 6 =:=

public export
data Goal : (0 s : Stage) -> Type where
  Fail : Goal s 
  Succeed : Goal s 
  Unify : Val s -> Val s -> Goal s
  And : Lazy (Goal s) -> Lazy (Goal s) -> Goal s
  Or : Lazy (Goal s) -> Lazy (Goal s) -> Goal s
  Fresh : (Name s -> Goal s) -> Goal s
  Later : Goal RunTime -> Goal StagingTime
  Gather : Goal StagingTime -> Goal StagingTime
  Fallback : Goal StagingTime -> Goal StagingTime

export
(\/) : Lazy (Goal s) -> Lazy (Goal s) -> Lazy (Goal s)
x \/ y = Or x y
-- (Delay Succeed) \/ (Delay r) = Succeed
-- (Delay l)       \/ (Delay Succeed) = Succeed
-- (Delay Fail)    \/ (Delay r = r
-- (Delay l) \/ (Delay r) = Or l r
-- (Delay Succeed) \/ r = Delay Succeed
-- l \/ Succeed = Succeed
-- Fail \/ r = r
-- l \/ Fail = l
-- l \/ r = Or l r

export
(/\) : Lazy (Goal s) -> Lazy (Goal s) -> Lazy (Goal s)
x /\ y = And x y

export
(=:=) : Val s -> Val s -> Goal s
[] =:= [] = Succeed
[] =:= (Var x) = Unify [] (Var x)
[] =:= _ = Fail
(Numb i) =:= (Numb j) = if i == j then Succeed else Fail
(Numb i) =:= (Var x) = Unify (Numb i) (Var x)
(Numb i) =:= _ = Fail
(x :: z) =:= (w :: y) = x =:= w /\ z =:= y 
l@(x :: z) =:= r@(Var n) = Unify l r
(x :: z) =:= _ = Fail
(Sym str) =:= (Sym str1) = if str == str1 then Succeed else Fail
l@(Sym str) =:= r@(Var x) = Unify l r
(Sym str) =:= _ = Fail
(Var x) =:= y = Unify (Var x) y

export
fresh : (Val s -> Goal s) -> Goal s
fresh f = Fresh (f . Var)

export
freshN : (n : Nat) -> (Vect n (Val s) -> Goal s) -> Goal s
freshN 0 f = f []
freshN (S k) f = fresh $ \a => freshN k $ \as => f (a :: as)

export
succeed : Goal s  
succeed = Succeed
 
export   
fail : Goal s  
fail = Fail

export
later : Goal RunTime -> Goal StagingTime
later = Later

export
gather : Goal StagingTime -> Goal StagingTime
gather = Gather

export
fallback : Goal StagingTime -> Goal StagingTime
fallback = Fallback

Persist Goal where
  persist Fail = Fail
  persist Succeed = Succeed
  persist (Unify x y) = persist x =:= persist y
  persist (And x y) = persist x /\ persist y
  persist (Or x y) = persist x \/ persist y
  persist (Fresh f) = Fresh (persist . f . unPersist)
    where
      -- This is a "staging unsafe" operation
      unPersist : Name RunTime -> Name StagingTime
      unPersist = MkName . unName
  persist (Later x) = x
  persist (Gather x) = persist x
  persist (Fallback x) = persist x

public export
disj : List (Lazy (Goal s)) -> Lazy (Goal s)
disj = foldl (\/) fail

public export
conj : List (Lazy (Goal s)) -> Lazy (Goal s)
conj = foldl (/\) succeed

data FallbackStatus = OutsideFallback | InsideFallback

Payload : Stage -> Type
Payload StagingTime = (Goal RunTime, FallbackStatus)
Payload RunTime = ()

public export
record State (0 s : Stage) where
  constructor MkState
  trail : Trail s
  counter : Name s
  payload : Payload s

Persist State where
  persist (MkState trail counter payload) = MkState (persist trail) (persist counter) ()

public export
empty : {s : Stage} -> State s
empty {s} = MkState (MkTrail []) (MkName 0) (payload s)
  where
    payload : (s : Stage) -> Payload s
    payload StagingTime = (Succeed, OutsideFallback)
    payload RunTime = ()

-- ext-S
public export
bind : Name s -> Val s -> State s -> State s
bind n v (MkState (MkTrail bindings) counter payload) = 
     MkState (MkTrail ((n, v) :: bindings)) counter payload

public export
gensym : State s -> (Name s, State s)
gensym (MkState trail counter payload) = (counter, MkState trail (incr counter) payload)

-- gensymN : (n : Nat) -> State s -> (Vect n (Name s), State s)
-- gensymN 0 x = ([], x)
-- gensymN (S k) x = let (ks, x')  = gensymN k x
--                       (k,  x'') = gensym x'
--                   in (k :: ks, x'')

public export
walk : (trail : Trail s) -> (val : Val s) -> Val s
walk (MkTrail []) (Var x) = Var x
walk t@(MkTrail ((nm, z) :: xs)) (Var x) with (decEq nm x)
  walk t@(MkTrail ((nm, z) :: xs)) (Var nm) | (Yes Refl) = 
    walk (assert_smaller t (MkTrail xs)) z
  walk t@(MkTrail ((nm, z) :: xs)) (Var x)  | (No contra) = 
    walk (assert_smaller t (MkTrail xs)) (Var x)
walk trail con = con

public export
walks : (trail : Trail s) -> (val : Val s) -> Val s
walks trail val with (walk trail val)
  walks trail val | []         = []
  walks trail val | (x :: y)   = walks trail (assert_smaller val x) :: walks trail (assert_smaller val y)
  walks trail val | (Sym  str) = (Sym str)
  walks trail val | (Var  x)   = Var x
  walks trail val | (Numb n)   = Numb n

public export
unify : Val s -> Val s -> State s -> IStream (State s)
unify l r z with (walk (trail z) l, walk (trail z) r)
  unify l r z | ((Var x), (Var y)) = 
                let mx = max x y
                    mn = min x y
                in [bind mx (Var mn) z]
  unify l r z | (x, y@(Var _))     = 
    unify (assert_smaller r y) (assert_smaller l x) z
  unify l r z | ((Var x),    y)    = [bind x y z]
  unify l r z | ((Sym str),  (Sym str1)) = if str == str1 then [z] else []
  unify l r z | ((a :: d), (p :: q)) = 
    unify (assert_smaller l a) (assert_smaller r p) z 
      >>= unify (assert_smaller l d) (assert_smaller r q)
  unify l r z | ([],         [])   = [z]
  unify l r z | (_,         _)    = []

public export
passOnFallback : State StagingTime -> Lazy (IStream (State StagingTime)) -> IStream (State StagingTime)
passOnFallback s@(MkState trail counter (x, InsideFallback)) y  = [s]
passOnFallback (MkState trail counter (x, OutsideFallback)) y = Force y

collapse : State StagingTime -> Goal RunTime 
collapse (MkState trail counter (code, fallbackStatus)) = 
  code /\ conj (map (\(nm, vl) => Var (persist nm) =:= persist vl) (unTrail trail))

public export
interpret : Fuel -> Goal s -> State s -> IStream (State s)
interpret k Fail y = []
interpret k Succeed y = [y]
interpret k (Unify x z) y = unify x z y
interpret k (And x z) y = (Wait (interpret k x y)) >>= interpret k z
interpret k (Or x z) y = interpret k x y <|> interpret k z y
interpret k (Fresh f) y = let (fresh, st) = gensym y in 
                        interpret k (f fresh) st
interpret {s=StagingTime} k (Later x) s@(MkState trail counter (code, fbs)) = 
  [ MkState trail counter ((x /\ code), fbs) ]
interpret {s=StagingTime} k (Gather x) y = 
  passOnFallback y $
  case toList k $ interpret k x y of
    [] => []
    [x] => [x]
    options => [ MkState (trail y) (counter y) 
                         (disj $ map (delay . collapse) options, OutsideFallback) ]
interpret {s=StagingTime} k (Fallback x) y = 
  passOnFallback y $
  case take k 2 $ interpret k x ({ payload $= mapSnd (const InsideFallback) } y) of
    []  => []
    [x] => [x]
    _   => interpret k (assert_smaller x (Later (persist x))) y

Error : Type
Error = String

public export
run : Fuel -> (Val RunTime -> Goal RunTime) -> IStream (Val RunTime)
run k x = (\case (MkState trail counter payload) => walks trail (Var (MkName 0))) 
      <$> interpret k (fresh x) empty

-- public export
-- runN : (n : Nat) -> 

public export
stage : Fuel -> Goal StagingTime -> Either Error (Goal RunTime, State RunTime)
stage k x = let cases = interpret k x empty in
            case split k 2 cases of
              ([],  z) => Left "Staging Failed"
              ([y], z) => Right (fst $ payload y, persist y)
              (_,   z) => Left "Staging was non-deterministic"

public export
runStaged : Fuel -> Goal StagingTime -> Either Error (IStream (State RunTime))
runStaged f x = uncurry (interpret f) <$> stage f x

public export
Relation : (arity : Nat) -> {stage : Stage} -> Type
Relation 0 {stage = stage} = Goal stage
Relation (S k) {stage = stage} = Val stage -> Relation k {stage=stage}
  
{-
(run 1 (q)              ;; q is later
 (staged
  (fresh (x)            ;; x is now
    (gather
      (conde
        [(fresh (y) (== x y) (== y 1))]
        [(fresh (y) (== x 2) (== y 2))]))    ;; now unification
    (== x q)))) ;; later unification, with csp of x


(let ((y 3))
  (staged (lambda (x) y))
  (set! y 4))
-}
