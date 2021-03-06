-- import Data.List

data Sig = P | M -- P stands for + and M stands for -

data Ty = TV Var | All Var Ty | Ty :-> Ty
        | Unit | Ty :*: Ty -- these can be encoded too but
        | Void | Ty :+: Ty -- for convenience of presentation
        
data Tm = Fn (Tm -> Tm) | Tm :$ Tm -- using HOAS
        | Cunit | Tm :* Tm | Fst Tm | Snd Tm
        | L Tm | R Tm | CaseLR Tm (Tm -> Tm) (Tm -> Tm)
        | Lift Tm Tm | Phi -- added some constants for lift and phi function

type Var = Int -- give some suitable type for variable

flipSig :: Sig -> Sig
flipSig M = P
flipSig P = M

rTm :: Sig -> Var -> Ty -> Tm -> Tm
rTm _ _ Unit              = id -- const Cunit
rTm _ _ Void              = id
rTm _ r (TV x)   | r /= x = id
rTm P _ (TV _)            = Lift Phi -- apply lift phi in positive occurrence,
rTm M _ (TV _)            = L        -- left injection in negative occurrence. 
rTm p r (a:->b)           = \f -> Fn (\x -> rTm p r b (f :$ rTm p' r a x))
                          where p' = flipSig p
rTm p r (a:*:b)           = \x -> rTm p r a x :* rTm p r b x
rTm p r (a:+:b)           = \x -> CaseLR x (rTm p r a) (rTm p r b)
rTm p r (All x b) | r/= x = rTm p r b
rTm _ _ (All _ _) = error "univ. quant. var. should have been alpha renamed"

main :: IO ()
main = putStrLn "hello world"
  where
    _ = rTm (flipSig M)
    _ = R
    _ = Fst
    _ = Snd
    _ = Cunit
