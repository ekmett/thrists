{-# LANGUAGE GADTs, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}

data P r a c where
  P :: r b c -> r a b -> P r a c

data D r a b where
  D0 :: D r a a
  D1 :: r a b -> D r a b
  D2 :: r b c -> r a b -> D r a c

data L l m a c where
  L :: l b c -> !(L (P l) m a b) -> L l m a c
  NL :: L r r a a

data R l m a c where
  R :: !(R l (P m) b c) -> m a b -> R l m a c
  NR :: R r r a a

data Q r a b where
  Q0 :: Q r a a
  Q1 :: r a b -> Q r a b
  Q :: !(D r e f) -> !(L (P r) m d e) -> !(Q m c d) -> !(R m (P r) b c) -> !(D r a b) -> Q r a f

(<|) :: r b c -> Q r a b -> Q r a c
a <| Q0                                      = Q1 a
a <| Q1 b                                    = Q (D1 a) NL Q0 NR (D1 b)
a <| Q D0 l m r s                            = Q (D1 a) l m r s
a <| Q (D1 b) l (Q (D2 c d) l' m' r' s') r s = Q (D2 a b) l (dcons D0 (P c d) l' m' r' s') r s
a <| Q (D1 b) l m r s                        = Q (D2 a b) l m r s -- not 2 exposed
a <| Q (D2 b c) l m r s                      = dcons (D1 a) (P b c) l m r s

dcons :: D r f g -> P r e f -> L (P r) m d e -> Q m c d -> R m (P r) b c -> D r a b -> Q r a g
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
