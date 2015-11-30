{-# LANGUAGE GADTs, RankNTypes #-}
import RecComb

data ExpF r t where  Lam :: (r t1 -> r t2) -> ExpF r (t1 -> t2)
                     App :: r (t1 -> t2) -> r t1 -> ExpF r t2
type Exp' a t = Rec1 ExpF a t
type Exp t = forall a . Exp' a t

data V r t where VFun :: (r t1 -> r t2) -> V r (t1 -> t2)
type Val t = Mu1 V t  -- %\textcomment{user defined value domain%}
val f = In1 (VFun f) 

veval :: Exp t -> Val t
veval e = msfcata1 phi e where
  phi :: Phi1' ExpF (Mu1 V)
  phi inv ev (Lam f) = val(\v -> ev (f (inv v)))
  phi inv ev (App e1 e2) = unVal(ev e1) (ev e2)
-- unVal %\textcomment{does not follow the restrictions of the Mendler style.%}
-- %\textcomment{Its definition relies on pattern matching against%} In1.
unVal :: Val (t1 -> t2) -> (Val t1 -> Val t2)
unVal (In1(VFun f)) = f
