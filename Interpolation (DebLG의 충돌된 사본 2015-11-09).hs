-- import Data.List

data Sig = P | M

data Ty = TV Var | Unit | Void | Ty :-> Ty | Ty :+: Ty | Ty :*: Ty | All Var Ty

-- data Type = Var Var | All Var Type | Type :->: Type

data Tm = Fn (Tm -> Tm) | Tm :$ Tm | Cunit
        | L Tm | R Tm | CaseLR Tm (Tm -> Tm) (Tm -> Tm)
        | Tm :* Tm | Fst Tm | Snd Tm
        | Lift Tm Tm | Phi

type Var = Int

flipSig :: Sig -> Sig
flipSig M = P
flipSig P = M

rTm :: Sig -> Var -> Ty -> Tm -> Tm
rTm _ _ Unit            = id -- const Cunit
rTm _ _ Void            = id
rTm _ x (TV y) | x /= y = id
rTm P _ (TV _)          = Lift Phi
rTm M _ (TV _)          = L
rTm p x (a:->b)         = \f -> Fn (\y -> rTm p x b (f :$ rTm p' x a y))
                        where p' = flipSig p
rTm p x (a:*:b)         = \z -> rTm p x a z :* rTm p x b z
rTm p x (a:+:b)         = \z -> CaseLR z (rTm p x a) (rTm p x b)
rTm p x (All y b) | x /= y =
rTm _ _ (All _ _)          = id

main :: IO ()
main = putStrLn "hello world"
  where
    _ = rTm (flipSig M)
    _ = R
    _ = Fst
    _ = Snd
    _ = Cunit
