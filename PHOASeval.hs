{-# LANGUAGE GADTs, RankNTypes, NoMonoLocalBinds #-}
import PRec

data ExpF r_ r t where
   Lam :: (r_ t1 -> r t2) -> ExpF r_ r (t1 -> t2)
   App :: r (t1 -> t2) -> r t1 -> ExpF r_ r t2

type Exp' a t = Mu_1 ExpF a t
type Exp t = forall a. Exp' a t
-- lam :: (Mu_1 f a t1 -> Mu_1 ExpF a t2) -> Mu_1 ExpF a (t1 -> t2)
lam f = In_1 (Lam (f . Var_1))
-- app :: Mu_1 ExpF a (t1 -> t2) -> Mu_1 ExpF a t1 -> Mu_1 ExpF a t2
app e1 e2 = In_1 (App e1 e2)

data Id a = MkId {unId :: a}

eval :: Exp t -> Id t
eval e = mphit1 phi e where
  phi :: Phi1 ExpF Id
  phi ev (Lam f)   = MkId(\v -> unId(ev (f (MkId v))))
  phi ev (App f x) = MkId(unId(ev f) (unId(ev x)))
