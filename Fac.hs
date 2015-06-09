{-# LANGUAGE RankNTypes #-}
import Prelude hiding (succ, pred)
import RecComb
plus = mcata0 phi where
  phi (+.) Z     m = m
  phi (+.) (S n) m = succ (n +. m)

times = mcata0 phi where
  phi (*.) Z     m = zero
  phi (*.) (S n) m = plus m (n *. m) 

mprim0 :: (forall r. (r -> Mu0 f) -> (r -> a) -> f r -> a) -> Mu0 f -> a
mprim0 phi (In0 x) = phi id (mprim0 phi) x

data N r = Z | S r
type Nat = Mu0 N
zero    = In0 Z
succ n  = In0 (S n)

pred = mprim0 phi where
  phi cast pr Z      = zero
  phi cast pr (S n)  = cast n

factorial = mprim0 phi where
    phi cast fac Z      = succ zero
    phi cast fac (S n)  = times (succ (cast n)) (fac n)
