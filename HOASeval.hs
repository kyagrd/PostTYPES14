{-# LANGUAGE GADTs, RankNTypes #-}
import RecComb

data ExpF r t where  Lam :: (r t1 -> r t2) -> ExpF r (t1 -> t2)
                     App :: r (t1 -> t2) -> r t1 -> ExpF r t2
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t
-- lam :: (Exp' a t1 -> Exp' a t2) -> Exp' a (t1 -> t2)
lam e    = Roll1 (Lam e)
-- app :: Exp' a (t1 -> t2) -> Exp' a t1 -> Exp' a t2
app f e  = Roll1 (App f e)

data Id t = MkId {unId :: t}
-- eval :: Exp t -> Id t
eval = msfcata1 phi where
  phi :: Phi1' ExpF Id
  phi inv ev (Lam f)   = MkId(\v -> unId(ev (f (inv (MkId v)))))
  phi inv ev (App f x) = MkId(unId(ev f) (unId(ev x)))
