{-# LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleInstances
           , NoMonoLocalBinds #-}
module Rec2 where

import Control.Monad

type a .-> b = forall i. a i -> b i

data Mu_0 f    = In_0 (f (Mu_0 f) (Mu_0 f))
data Mu_1 f i  = In_1 (f (Mu_1 f) (Mu_1 f) i)
-- primitive recursion
                           {- cast -}         {- call -}
type Phi_0 f a = forall r. (r  -> Mu_0 f)  -> (r  -> a)  -> f r r  -> a
type Phi_1 f a = forall r. (r .-> Mu_1 f)  -> (r .-> a)  -> f r r .-> a

mpr0 :: Phi_0 f a -> Mu_0 f  -> a
mpr0 phi (In_0 x) = phi id (mpr0 phi) x

mpr1 :: Phi_1 f a -> Mu_1 f .-> a
mpr1 phi (In_1 x) = phi id (mpr1 phi) x


data Void

data MuC_0 f    = InC_0 (f Void (MuC_0 f))
data MuC_1 f i  = InC_1 (f Void (MuC_1 f) i)

-- course-of-values recursion
                            {- out -}            {- cast -}          {- call -}
type PhiC_0 f a = forall r. (r  -> f Void r)  -> (r  -> MuC_0 f)  -> (r  -> a)  -> f Void r  -> a
type PhiC_1 f a = forall r. (r .-> f Void r)  -> (r .-> MuC_1 f)  -> (r .-> a)  -> f Void r .-> a

unInC_0 (InC_0 x) = x
unInC_1 (InC_1 x) = x

mcvpr0 :: PhiC_0 f a -> MuC_0 f  -> a
mcvpr0 phi (InC_0 x) = phi unInC_0 id (mcvpr0 phi) x

mcvpr1 :: PhiC_1 f a -> MuC_1 f .-> a
mcvpr1 phi (InC_1 x) = phi unInC_1 id (mcvpr1 phi) x



data MuP_0 f a    = InP_0 (f a (MuP_0 f a))    | Var_0 a
data MuP_1 f a i  = InP_1 (f a (MuP_1 f a) i)  | Var_1 (a i)

-- iteration over PHOAS
                            {- call -}
type PhiP_0 f a = forall r. (r a  -> a) -> f a (r a)  -> a
type PhiP_1 f a = forall r. (r a .-> a) -> f a (r a) .-> a


mphit0 :: PhiP_0 f a -> MuP_0 f a -> a 
mphit0 phi (InP_0 x) = phi (mphit0 phi) x
mphit0 phi (Var_0 a) = a

mphit1 :: PhiP_1 f a -> MuP_1 f a .-> a 
mphit1 phi (InP_1 x) = phi (mphit1 phi) x
mphit1 phi (Var_1 a) = a

{-
mphit0 :: PhiP_0 f a -> (forall a. MuP_0 f a) -> a 
mphit0 phi x = mphit phi x where
  mphit phi (InP_0 x) = phi (mphit phi) x
  mphit phi (Var_0 a) = a

mphit1 :: PhiP_1 f a -> (forall a. MuP_1 f a i) -> a i
mphit1 phi x = mphit phi x where
  mphit :: PhiP_1 f a -> MuP_1 f a .-> a
  mphit phi (InP_1 x) = phi (mphit phi) x
  mphit phi (Var_1 a) = a
-}

-- primitive recursion over PHOAS
                             {- cast -}             {- call -}
type PhiPR_0 f a = forall r. (r a  -> MuP_0 f a) -> (r a  -> a) -> f a (r a)  -> a
type PhiPR_1 f a = forall r. (r a .-> MuP_1 f a) -> (r a .-> a) -> f a (r a) .-> a

mphpr0 :: PhiPR_0 f a -> MuP_0 f a -> a 
mphpr0 phi (Var_0 a) = a
mphpr0 phi (InP_0 x) = phi id (mphpr0 phi) x
                                            
                                            

mphpr1 :: PhiPR_1 f a -> MuP_1 f a .-> a 
mphpr1 phi (Var_1 a) = a
mphpr1 phi (InP_1 x) = phi id (mphpr1 phi) x
                                            


-- course-of-values iteration over PHOAS
type PhiPC_0 f a = forall r. (r a  -> Maybe(f a (r a))) -- out
                          -> (r a  -> MuP_0 f a) -- cast
                          -> (r a  -> a) {- call -} -> f a (r a)  -> a
type PhiPC_1 f a = forall r. (forall i. r a i-> Maybe(f a (r a) i)) -- out
                          -> (r a .-> MuP_1 f a) -- cast
                          -> (r a .-> a) {- call -} -> f a (r a) .-> a
-- unInP_0 :: MuP_0 f a -> Maybe (f a (MuP_0 f a))
unInP_0 (InP_0 x) = Just x
unInP_0 _         = Nothing
-- unInP_1 :: MuP_1 f a i -> Maybe (f a (MuP_1 f a) i)
unInP_1 (InP_1 x) = Just x
unInP_1 _         = Nothing

mphcv0 :: PhiPC_0 f a -> MuP_0 f a -> a
mphcv0 phi (InP_0 x) = phi unInP_0 id (mphcv0 phi) x
mphcv0 phi (Var_0 a) = a

mphcv1 :: PhiPC_1 f a -> MuP_1 f a .-> a
mphcv1 phi (InP_1 x) = phi unInP_1 id (mphcv1 phi) x
mphcv1 phi (Var_1 a) = a

{-
mphcv0 :: PhiPC_0 f a -> (forall a. MuP_0 f a) -> a
mphcv0 phi x = mphcv phi x where
  mphcv :: PhiPC_0 f a -> MuP_0 f a -> a
  mphcv phi (InP_0 x) = phi unInP_0 (mphcv phi) x
  mphcv phi (Var_0 a) = a

mphcv1 :: PhiPC_1 f a -> (forall a. MuP_1 f a i) -> a i
mphcv1 phi x = mphcv phi x where
  mphcv :: PhiPC_1 f a -> MuP_1 f a .-> a
  mphcv phi (InP_1 x) = phi unInP_1 (mphcv phi) x
  mphcv phi (Var_1 a) = a
-}




class Functor2nd f where
  fmap2nd :: (a -> b) -> f x a -> f x b

-- Functor2nd instance isn't very useful though because
-- it is an incorherent overlapping instances with other
-- functor instances such as ((,) a) or ((->) r).
instance Functor2nd f => Functor (f a) where
  fmap f = fmap2nd f

class Functor2nd f => Positive f where
  lemmPositive :: f x r -> f y r

-- cousre-of-values recursion fixpoint to primitive recursion fixpoint
muc2mu :: Positive f => MuC_0 f -> Mu_0 f
muc2mu x = mcvpr0 phi x where
  phi out cast call v = In_0 $ lemmPositive $ fmap2nd call v

-- primitive recursion fixpoint to cousre-of-values recursion fixpoint
mu2muc :: Positive f => Mu_0 f -> MuC_0 f
mu2muc x = mpr0 phi x where
  phi cast call v = InC_0 $ lemmPositive $ fmap2nd call v

-- cousre-of-values recursion fixpoint to PHOAS fixpoint
muc2mup :: Positive f => MuC_0 f -> MuP_0 f a
muc2mup x = mcvpr0 phi x where
  phi out cast call v = InP_0 $ lemmPositive $ fmap2nd call v

-- PHOAS fixpoint to course-of-values recursion fixpoint
mup2muc :: Positive f => (forall a.MuP_0 f a) -> MuC_0 f
mup2muc x = mphit0 phi x where
  phi call v = InC_0 $ lemmPositive $ fmap2nd call v

-- PHOAS fixpoint to primitive recursion fixpoint
mup2mu :: Functor2nd f => (forall a.MuP_0 f a) -> Mu_0 f
mup2mu x = mphit0 phi x where
  phi call v = In_0 $ fmap2nd call v


-- -- PHOAS fixpoint to primitive recursion fixpoint
-- mup2mu' :: Functor2nd f => MuP_0 f a -> Mu_0 f
-- mup2mu' x = mphit0 phi x where
--   phi call v = In_0 $ fmap2nd call v


-- primitive recursion fixpoint to PHOAS fixpoint -- not meaningful 
mu2mup :: Positive f => Mu_0 f -> MuP_0 f a
mu2mup x = mpr0 phi x where
  phi cast call v = InP_0 $ lemmPositive $ fmap2nd call v




{- ---------------------------
data MuC_0 f    = InC_0 (forall z. f z (MuC_0 f))
data MuC_1 f i  = InC_1 (forall z. f z (MuC_1 f) i)

type PhiC_0 f a = forall r    .(           r    -> (forall z.f z (MuC_0 f)))    -> (r  -> MuC_0 f) -> (r  -> a) -> (forall z. f z r)   -> a
type PhiC_1 f a = forall r i  .(forall i.  r i  -> (forall z.f z (MuC_1 f) i))  -> (r .-> MuC_1 f) -> (r .-> a) -> (forall z. f z r i) -> a i
--------------------------- -}


data E r_ r = App r r | Lam (r_ -> r) | Let r (r_ ->r)
type Exp' a = MuP_0 E a
type Exp = forall a. Exp' a
lam f = InP_0 (Lam (f . Var_0))
app e1 e2 = InP_0 (App e1 e2)
let_ e f = InP_0 (Let e (f . Var_0))

vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ]

myexp = let_ (lam(\f -> (lam(\x -> app f (app f x)))))
             (\twice -> app twice twice)

-- formatting PHOAS expression
-- showExp :: Exp -> String
showExp e = mphit0 phi e vars where
  phi sh (App e1 e2) = \vs     -> "("++sh e1 vs++" "++sh e2 vs++")"
  phi sh (Lam f)     = \(v:vs) -> "(\\"++v++"."
                                       ++sh(f(const v)) vs++")"
  phi sh (Let e f)   = \(v:vs) -> "(let "++v++"="++sh e vs++" in "
                                            ++sh(f(const v)) vs++")"

-- desugaring let
-- desugar :: Exp -> Exp
desugar e = mphit0 phi e where
  phi desug (App e1 e2) = app (desug e1) (desug e2)
  phi desug (Lam f)     = lam (desug . f)
  phi desug (Let e f)   = lam (desug . f) `app` (desug e)

-- parallel reduction
reduce :: Exp -> Exp
reduce e = mphcv0 phi e where
  phi out cast red (App e1 e2) = case out e1 of
                                   Just(Lam f) -> (red . f) (red e2)
                                   _           -> app (red e1) (red e2)
  phi out cast red (Lam f)     = lam (red . f)
  phi out cast red (Let e f)   = (red . f) (red e)


data ExprF r_ r = LET r (r_ -> r) | ADD r r | LIT Int
type Expr' a = MuP_0 ExprF a
type Expr = forall a. Expr' a
eLet e f = InP_0 (LET e (f . Var_0))
eAdd e1 e2 = InP_0 (ADD e1 e2)
eLit n = InP_0 (LIT n)

evalExpr :: Expr -> Int
evalExpr e = mphit0 phi e where
  phi call (LIT n)     = n
  phi call (ADD e1 e2) = call e1 + call e2
  phi call (LET e f)   = call (f (call e))



-- TODO is it safe to do unInP_0 ????? could be cause we separated neg from pos
constfold' :: Expr -> Expr
constfold' e = mphit0 phi e where
  phi cf (LET e f)   = eLet (cf e) (cf . f)
  phi cf (LIT n)     = eLit n
  phi cf (ADD e1 e2) = case (unInP_0 (cf e1), unInP_0 (cf e2)) of
                         (Just(LIT n),Just(LIT m)) -> eLit(n+m)
                         _                         -> eAdd (cf e1) (cf e2)

constfold :: Expr -> Expr
constfold e = mphcv0 phi e where
  phi out cast cf (LET e f)   = eLet (cf e) (cf . f)
  phi out cast cf (LIT n)     = eLit n
  phi out cast cf (ADD e1 e2) =
    case (out (cf e1), out (cf e2)) of
      (Just(LIT n),Just(LIT m)) -> undefined -- eLit(n+m)
      _                         -> eAdd (cf e1) (cf e2)

-- is ths type what we want????
getLit e = mphit0 phi e where
  phi call (LIT n)     = Just(LIT n)
  phi call _           = Nothing


-- constant folding -- is this type what we want? -- is this type what we want? -- is this type what we want? -- is this type what we want?
cfold :: Expr -> Expr' (Maybe(ExprF r_ r))
cfold e = mphit0 phi e where
  phi cf (LET e f)   = eLet (cf e) (cf . f)
  phi cf (LIT n)     = eLit n
  phi cf (ADD e1 e2) = case (getLit (cf e1), getLit (cf e2)) of
                         (Just(LIT n),Just(LIT m)) -> eLit(n+m)
                         _                         -> eAdd (cf e1) (cf e2)
                 -- where e1' = cf e1
                 --       e2' = cf e2



