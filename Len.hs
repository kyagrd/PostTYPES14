import RecComb

data L p r = N | C p r
type List p = Mu0 (L p)
nil        = In0 N
cons x xs  = In0 (C x xs)

-- length :: List p -> Int
length = mcata0 phi where
  phi len N         = 0
  phi len (C x xs)  = 1 + len xs
