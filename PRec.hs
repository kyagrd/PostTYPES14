{-# LANGUAGE GADTs, RankNTypes #-}
module PRec where

data Mu_0 f a     = In_0 (f a (Mu_0 f a))       | Var_0 a
data Mu_1 f a i = In_1 (f a (Mu_1 f a) i) | Var_1 (a i)

type Phi0   f a = forall r  .(r a -> a)         -> f a (r a)   -> a
type Phi1 f a = forall r i.(forall i.r a i -> a i) -> f a (r a) i -> a i

mphit0 :: Phi0 f a -> (forall a. Mu_0 f a) -> a 
mphit0 phi x = mphit phi x where
  mphit phi (In_0 x)  = phi (mphit phi) x
  mphit phi (Var_0 a) = a

mphit1 :: Phi1 f a -> (forall a. Mu_1 f a i) -> a i
mphit1 phi x = mphit phi x where
  mphit :: Phi1 f a -> Mu_1 f a i -> a i
  mphit phi (In_1 x)  = phi (mphit phi) x
  mphit phi (Var_1 a) = a
