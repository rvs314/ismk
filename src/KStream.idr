module KStream

import Data.Fuel
import Data.Zippable

%default total

public export
data KStream a = (::) a (KStream a)
               | Nil
               | Wait (Inf (KStream a))

public export
immature : {0 a : Type} -> KStream a
immature {a} = Wait (Delay (immature {a}))

public export
mature : KStream a -> KStream a
mature (x :: y) = x :: y
mature []       = []
mature (Wait x) = x

public export
repeat : a -> KStream a
repeat x = x :: Wait (repeat x)

public export
split : Fuel -> Nat -> KStream a -> (List a, KStream a)
split Dry k y = ([], y)
split (More x) 0 y = ([], y)
split (More x) (S k) (y :: z) = let (head, tail) = split (More x) k z 
                               in (y :: head, tail)
split (More x) (S k) [] = ([], [])
split (More x) (S k) (Wait y) = split x k y

public export
take : Fuel -> Nat -> KStream a -> List a 
take x k y = fst $ split x k y

public export
toList : Fuel -> KStream a -> List a
toList Dry y = []
toList (More x) (y :: z) = y :: toList (More x) z
toList (More x) [] = []
toList (More x) (Wait y) = toList x y

mapApp : (a -> b) -> KStream a -> KStream b -> KStream b
mapApp f (x :: z) y = f x :: mapApp f z y
mapApp f [] y       = y
mapApp f (Wait x) y = Wait (mapApp f x y)

public export
Semigroup (KStream a) where
  (x :: y) <+> ys = x :: (y <+> ys)
  [] <+> ys       = ys
  (Wait x) <+> ys = Wait (x <+> ys)

public export
Functor KStream where
  map f k = mapApp f k []

public export
Applicative KStream where
  pure x = [x]

  (x :: y) <*> k = mapApp x k (y <*> k)
  []       <*> k = []
  (Wait x) <*> k = Wait (x <*> k)

public export
Monad KStream where
  join (x :: y) = x <+> join y
  join []       = []
  join (Wait x) = Wait $ join x

public export
Alternative KStream where
  empty = []

  (x :: y) <|> r = x :: (y <|> r)
  []       <|> r = r
  (Wait x) <|> r = r <|> x

public export
Zippable KStream where
  zipWith fabc [] bs = []
  zipWith fabc as [] = []
  zipWith fabc as (Wait bs) = Wait (zipWith fabc as bs)
  zipWith fabc (Wait as) bs = Wait (zipWith fabc as bs)
  zipWith fabc (a :: as) (b :: bs) = fabc a b :: zipWith fabc as bs

  unzipWith fabc (x :: y) = let rst : (KStream b, KStream c)
                                rst = unzipWith fabc y 
                                head : (b, c)
                                head = fabc x
                            in (fst head :: fst rst, snd head :: snd rst)
  unzipWith fabc [] = ([], [])
  unzipWith fabc (Wait x) = let rst : Inf (KStream b, KStream c)
                                rst = unzipWith fabc x
                            in (Wait (fst $ Force rst), Wait (snd $ Force rst))

  zipWith3 fabcd as bs cs = zipWith (uncurry . fabcd) as (zip bs cs)

  unzipWith3 fabcd as = let (bs, cds) = unzipWith fabcd as
                            (cs, ds)  = unzip cds
                        in (bs, cs, ds)
