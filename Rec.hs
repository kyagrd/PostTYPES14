{-# LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleInstances #-}
module Rec where

type a .-> b = forall i. a i -> b i

data Mu_0 f    = In_0 (f (Mu_0 f))
data Mu_1 f i  = In_1 (f (Mu_1 f) i)
-- primitive recursion
                           {- cast -}         {- call -}
type Phi_0 f a = forall r. (r  -> Mu_0 f)  -> (r  -> a)  -> f r  -> a
type Phi_1 f a = forall r. (r .-> Mu_1 f)  -> (r .-> a)  -> f r .-> a

mpr0 :: Phi_0 f a -> Mu_0 f  -> a
mpr0 phi (In_0 x) = phi id (mpr0 phi) x

mpr1 :: Phi_1 f a -> Mu_1 f .-> a
mpr1 phi (In_1 x) = phi id (mpr1 phi) x


data MuC_0 f    = InC_0 (f (MuC_0 f))
data MuC_1 f i  = InC_1 (f (MuC_1 f) i)

-- course-of-values recursion
                            {- out -}       {- cast -}          {- call -}
type PhiC_0 f a = forall r. (r  -> f r)  -> (r  -> MuC_0 f)  -> (r  -> a)  -> f r  -> a
type PhiC_1 f a = forall r. (r .-> f r)  -> (r .-> MuC_1 f)  -> (r .-> a)  -> f r .-> a

unInC_0 (InC_0 x) = x
unInC_1 (InC_1 x) = x

mcvpr0 :: PhiC_0 f a -> MuC_0 f  -> a
mcvpr0 phi (InC_0 x) = phi unInC_0 id (mcvpr0 phi) x

mcvpr1 :: PhiC_1 f a -> MuC_1 f .-> a
mcvpr1 phi (InC_1 x) = phi unInC_1 id (mcvpr1 phi) x



data MuH_0 f a    = InH_0 (f (MuH_0 f a))    | Inverse_0 a
data MuH_1 f a i  = InH_1 (f (MuH_1 f a) i)  | Inverse_1 (a i)

-- iteration over HOAS
                            {- Inv -}      {- call -}
type PhiH_0 f a = forall r. (a  -> r a) -> (r a  -> a) -> f (r a)  -> a
type PhiH_1 f a = forall r. (a .-> r a) -> (r a .-> a) -> f (r a) .-> a

msfit0 :: PhiH_0 f a -> (forall a. MuH_0 f a) -> a 
msfit0 phi x = msfit phi x where
  msfit phi (InH_0 x) = phi Inverse_0 (msfit phi) x
  msfit phi (Inverse_0 a) = a

msfit1 :: PhiH_1 f a -> (forall a. MuH_1 f a i) -> a i
msfit1 phi x = msfit phi x where
  msfit :: PhiH_1 f a -> MuH_1 f a .-> a
  msfit phi (InH_1 x) = phi Inverse_1 (msfit phi) x
  msfit phi (Inverse_1 a) = a


type PhiHC_0 f a = forall r. (a  -> r a) -> (r a  -> Maybe(f (r a)))
                          -> (r a  -> a) -> f (r a)  -> a
type PhiHC_1 f a = forall r. (a .-> r a) -> (forall i. r a i -> Maybe(f (r a) i))
                          -> (r a .-> a) -> f (r a) .-> a

unInH_0 (InH_0 x) = Just x
unInH_0 _         = Nothing
unInH_1 (InH_1 x) = Just x
unInH_1 _         = Nothing

msfcv0 :: PhiHC_0 f a -> (forall a. MuH_0 f a) -> a 
msfcv0 phi x = msfcv phi x where
  msfcv phi (InH_0 x) = phi Inverse_0 unInH_0 (msfcv phi) x
  msfcv phi (Inverse_0 a) = a

msfcv1 :: PhiHC_1 f a -> (forall a. MuH_1 f a i) -> a i
msfcv1 phi x = msfcv phi x where
  msfcv :: PhiHC_1 f a -> MuH_1 f a .-> a
  msfcv phi (InH_1 x) = phi Inverse_1 unInH_1 (msfcv phi) x
  msfcv phi (Inverse_1 a) = a

-- parallel reduction
reduce :: Exp -> Exp
reduce = msfcv0 phi where
  phi inv out red (App e1 e2) = case out e1 of
                                  Just(Lam f) -> (red . f . inv) (red e2)
                                  _           -> app (red e1) (red e2)
  phi inv out red (Lam f)     = lam (red . f . inv)
  phi inv out red (Let e f)   = (red . f . inv) (red e)





data E r = App r r | Lam (r -> r) | Let r (r ->r)
type Exp' a = MuH_0 E a
type Exp = forall a. Exp' a
lam f = InH_0 (Lam f)
app e1 e2 = InH_0 (App e1 e2)
let_ e f = InH_0 (Let e f)



vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ]

myexp = let_ (lam(\f -> (lam(\x -> app f (app f x)))))
             (\twice -> app twice twice)

-- formatting PHOAS expression
showExp :: Exp -> String
showExp e = msfit0 phi e vars where
  phi inv sh (App e1 e2) = \vs     -> "("++sh e1 vs++" "++sh e2 vs++")"
  phi inv sh (Lam f)     = \(v:vs) -> "(\\"++v++"."
                                           ++sh(f(inv $ const v)) vs++")"
  phi inv sh (Let e f)   = \(v:vs) -> "(let "++v++"="++sh e vs++" in "
                                            ++sh(f(inv $ const v)) vs++")"

-- desugaring let
desugar :: Exp -> Exp
desugar = msfit0 phi where
  phi inv desug (App e1 e2) = app (desug e1) (desug e2)
  phi inv desug (Lam f)     = lam (desug . f . inv)
  phi inv desug (Let e f)   = lam (desug . f . inv) `app` (desug e)



