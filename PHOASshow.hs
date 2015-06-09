{-# LANGUAGE RankNTypes #-}
import PRec
vars = [ [i] | i <- ['a'..'z'] ] ++ [ i:show j | j<-[1..], i<-['a'..'z'] ] :: [String]

data ExpF r_ r = Lam (r_ -> r) | App r r
type Exp' a = Mu_0 ExpF a
type Exp = forall a. Exp' a
-- lam :: (Mu_0 f a -> Mu_0 ExpF a) -> Mu_0 ExpF a
lam f = In_0 (Lam (f . Var_0))
-- app :: Mu_0 ExpF a -> Mu_0 ExpF a -> Mu_0 ExpF a
app e1 e2 = In_0 (App e1 e2)

showExp :: Exp -> String
showExp e = mphit0 phi e vars where
  phi :: Phi0 ExpF ([String] -> String)
  phi show' (App x y) = \vs -> "("++show' x vs++" "++show' y vs++")"
  phi show' (Lam z)   = \(v:vs) -> "(\\"++v++"."
                                     ++show' (z(const v)) vs++")"

data ExprF r_ r = LAM (r_ -> r) | APP r r | LET r (r_ -> r)
type Expr' a = Mu_0 ExprF a
type Expr = forall a. Expr' a
-- %\textcomment{omitting constructor function definitions for \textit{Expr} sicne they arn't used in the example%}

desugExp :: Expr -> Exp -- %\textcomment{example from the PCDT paper in Mendler style%}
desugExp e = mphit0 phi e where
  phi :: Phi0 ExprF (Mu_0 ExpF a)
  phi desug (APP e1 e2) = app (desug e1) (desug e2)
  phi desug (LAM f)   = lam (desug . f)
  phi desug (LET e f) = lam (desug . f) `app` (desug e)

