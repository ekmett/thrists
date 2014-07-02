{-# LANGUAGE GADTs, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}

data P a
  = P a a

data D a
  = D0
  | D1 a
  | D2 a a

data L a b where
  L :: a -> !(L (P a) b) -> L a b
  NL :: L a a

data R a b where
  R :: !(R a (P b)) -> b -> R a b
  NR :: R a a

data Q a where
  Q0 :: Q a
  Q1 :: a -> Q a
  Q :: !(D a) -> !(L (P a) b) -> !(Q b) -> !(R b (P a)) -> !(D a) -> Q a

(<|) :: a -> Q a -> Q a
a <| Q0                                      = Q1 a
a <| Q1 b                                    = Q (D1 a) NL Q0 NR (D1 b)
a <| Q D0 l m r s                            = Q (D1 a) l m r s
a <| Q (D1 b) l (Q (D2 c d) l' m' r' s') r s = Q (D2 a b) l (dcons D0 (P c d) l' m' r' s') r s
a <| Q (D1 b) l m r s                        = Q (D2 a b) l m r s -- not 2 exposed
a <| Q (D2 b c) l m r s                      = dcons (D1 a) (P b c) l m r s

dcons :: D a -> P a -> L (P a) b -> Q b -> R b (P a) -> D a -> Q a
dcons p a NL Q0 NR s = Q p NL (Q1 a) NR s
dcons p a NL (Q1 b) NR s = Q p (L a NL) Q0 (R NR b) s
dcons p a NL (Q D0 l' m' r' (D1 b)) NR s = Q p (L a l') m' (R r' b) s
dcons p a NL (Q D0 l' m' r' s') NR s     = Q p NL (Q (D1 a) l' m' r' s') NR s
dcons p a NL (Q (D1 b) l' m' r' s') NR s = Q p NL (Q (D2 a b) l' m' r' s') NR s
dcons p a (L b l) m (R r c) s = Q p NL (Q (D2 a b) l m r (D1 c)) NR s
dcons _ _ NL _ R{} _ = error "impossible"
dcons _ _ L{} _ NR _ = error "impossible"
dcons _ _ NL (Q D2{} _ _ _ _) _ _ = error "non-regular"

{-
deep :: D a -> Q (P a) -> D a -> Q a
deep p (Q (D1 a) l m r (D1 b)) s = Q p (L a l) m (R r b) s
deep p m s = Q p NL m NR s

dip :: L a b -> Q b -> R b a -> Q a
dip NL m NR = m
dip (L a l) m (R r b) = Q (D1 a) l m r (D1 b)
-}
