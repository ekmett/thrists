{-# LANGUAGE GADTs, BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}

import Control.Category.Free.View

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

-- regularity:
-- * 0s and 2s alternate.
-- * Q maximally pushes runs of 1s into the L and R parameters
-- *
data Q r a b where
  Q0 :: Q r a a
  Q1 :: r a b -> Q r a b
  Q :: !(D r e f) -> !(L (P r) m d e) -> !(Q m c d) -> !(R m (P r) b c) -> !(D r a b) -> Q r a f

instance Cons Q where
  a <| Q0                                      = Q1 a
  a <| Q1 b                                    = Q (D1 a) NL Q0 NR (D1 b)
  a <| Q D0 l m r s                            = Q (D1 a) l m r s
  a <| Q (D1 b) l (Q (D2 c d) l' m' r' s') r s = Q (D2 a b) l (dcons D0 (P c d) l' m' r' s') r s
  a <| Q (D1 b) l m r s                        = Q (D2 a b) l m r s -- not 2 exposed
  a <| Q (D2 b c) l m r s                      = dcons (D1 a) (P b c) l m r s

dcons :: D r f g -> P r e f -> L (P r) m d e -> Q m c d -> R m (P r) b c -> D r a b -> Q r a g
dcons p a NL Q0                         NR  s = Q p NL (Q1 a) NR s
dcons p a NL (Q1 b                    ) NR  s = Q p (L a NL) Q0 (R NR b) s
dcons p a NL (Q D0     l' m' r' (D1 b)) NR  s = Q p (L a l') m' (R r' b) s
dcons p a NL (Q D0     l' m' r' s'    ) NR  s = Q p NL (Q (D1 a) l' m' r' s') NR s
dcons p a NL (Q (D1 b) l' m' r' s'    ) NR  s = Q p NL (Q (D2 a b) l' m' r' s') NR s
dcons _ _ NL _                          R{} _ = error "impossible"
dcons _ _ NL (Q D2{} _ _ _ _)           _   _ = error "non-regular"
dcons p a (L b l) m (R r c) s = Q p NL (Q (D2 a b) l m r (D1 c)) NR s
dcons _ _ L{}     _ NR      _ = error "impossible"

instance Uncons Q where
  uncons Q0 = Empty
  uncons (Q1 a)                         = a :| Q0
  uncons (Q (D1 a)   NL Q0 NR (D1 b))   = a :| Q1 b
  uncons (Q (D1 a)   NL Q0 NR (D2 b c)) = a :| Q (D1 b) NL Q0 NR (D1 c)
  uncons (Q (D2 a b) l  m  r  s)        = a :| Q (D1 b) l  m  r  s
  uncons (Q D0 l m r s) = case nuncons (dip l m r) of
    Empty -> error "non-regular"
    P b c :| m'' -> b :| deep (D1 c) m'' s
  uncons (Q (D1 a) l (Q D0 l' m' r' D0) r s) = case nuncons (dip l' m' r') of
    Empty -> a :| Q D0 l Q0 r s
    P b c :| m'' -> a :| Q D0 l (deep (D2 b c) m'' D0) r s -- D1 under D1 but only at bottom
  uncons (Q (D1 a) l m r s) = a :| Q D0 l m r s

-- extract from a non-0-exposed queue
nuncons :: Q r a c -> View r (Q r) a c
nuncons Q0                             = Empty
nuncons (Q1 a)                         = a :| Q0
nuncons (Q (D1 a)   NL Q0 NR (D1 b))   = a :| Q1 b
nuncons (Q (D1 a)   NL Q0 NR (D2 b c)) = a :| Q (D1 b) NL Q0 NR (D1 c)
nuncons (Q (D1 a)   l  m  r  s)        = a :| Q D0     l  m  r  s
nuncons (Q (D2 a b) l  m  r  s)        = a :| Q (D1 b) l  m  r  s
nuncons (Q D0 _ _ _ _) = error "non-regular"

deep :: D r c d -> Q (P r) b c -> D r a b -> Q r a d
deep p (Q (D1 a) l m r (D1 b)) s = Q p (L a l) m (R r b) s
deep (D1 a) Q0 D0                = Q1 a
deep D0 Q0 (D1 a)                = Q1 a
deep D0 Q0 (D2 a b)              = Q (D1 a) NL Q0 NR (D1 b)
deep (D2 a b) Q0 D0              = Q (D1 a) NL Q0 NR (D1 b)
deep p m s                       = Q p      NL m  NR s

dip :: L r m c d -> Q m b c -> R m r a b -> Q r a d
dip NL      m NR      = m
dip (L a l) m (R r b) = Q (D1 a) l m r (D1 b)
dip NL      _ R{}     = error "impossible"
dip L{}     _ NR      = error "impossible"

{-
-- q :: D r e f -> L (P r) m d e -> Q m c d -> R m (P r) b c -> D r a b -> Q r a f
-- q p l (Q (D1 a) NL Q0 NR (D1 b)) r s = `
-- q p l m r s = Q p l m r s

fix0 :: Q r a c -> Q r a c
fix0 (Q D0 l m r D0) = case nuncons (dip l m r) of
  Empty -> Q0
  P b c :| m'' -> deep (D2 b c) m'' D0
-- fix0 (Q D0 l m r (D1 b)) = undefined
fix0 (Q (D1 a) l (Q D0 l' m' r' D0) r s) = case nuncons (dip l' m' r') of
  Empty -> Q (D1 a) l Q0 r s
  P b c :| m'' -> Q (D1 a) l (deep (D2 b c) m'' D0) r s -- can wind up with D1 under D1 but only at bottom
fix0 xs = xs

-}
