import Ismk
import Data.Vect
import Data.Fuel
import IStream

bito : Relation 1
bito x = x =:= 1 \/ x =:= 0

(>>=) : ((k -> Goal s) -> Goal s) -> (k -> Goal s) -> Goal s
(>>=) = ($)

(>>) : Lazy (Goal s) -> Lazy (Goal s) -> Lazy (Goal s)
(>>) = (/\)

appendo : Val s -> Val s -> Val s -> Goal s
appendo x y z =  x =:= [] /\ y =:= z
              \/ do [l, r, w] <- freshN 3
                    x =:= l :: r
                    appendo r y w
                    z =:= l :: w

-- appendo x y z = x =:= [] /\ y =:= z
--              \/ (freshN 3 $ \[l, r, w] => 
--                                 x =:= l :: r 
--                              /\ appendo r y w
--                              /\ z =:= l :: w)

-- runtimeCheckOneOrZero : (run $ fresh $ Main.oneOrZero) = [MkState (MkTrail [(MkName 0, Numb 1)]) (MkName 1) (),
--  MkState (MkTrail [(MkName 0, Numb 0)]) (MkName 1) ()]

-- applyToAllZeros : {n : Nat} -> ((Vect n Nat) -> a) -> a
-- applyToAllZeros {n} f = f $ replicate n 0

anyAppend : Val s -> Goal s
anyAppend x = do [a, b, c] <- freshN 3
                 x =:= [a, b, c]
                 appendo a b c
