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

double :: r b c -> r a b -> Q r a c
double a b = Q (D1 a) NL Q0 NR (D1 b)

triple :: r c d -> r b c -> r a b -> Q r a d
triple a b c = Q (D1 a) NL Q0 NR (D2 b c)

digit :: D r a b -> Q r a b
digit D0       = Q0
digit (D1 a)   = Q1 a
digit (D2 a b) = double a b

instance Uncons Q where
  uncons Q0 = Empty
  uncons (Q1 a) = a :| Q0
  uncons (Q D0 (L a l) m (R r b) s) = case nuncons (Q (D1 a) l m r (D1 b)) of
    Empty -> error "impossible"
    P c d :| m'' -> c :| deep (D1 d) m'' s
  uncons (Q D0 NL m NR s) = case nuncons m of
    Empty -> error "non-regular"
    P b c :| m'' -> b :| deep (D1 c) m'' s
  uncons (Q (D1 a) l (Q D0 l' m' r' s') r s) = case nuncons (dip l' m' r') of
    Empty -> a :| Q D0 l (digit s') r s
    P b c :| m'' -> a :| Q D0 l (deep (D2 b c) m'' s') r s -- D1 under D1 at bottom
  uncons (Q (D1 a) NL Q0 NR s)   = a :| digit s
  uncons (Q (D1 a) l m r s) = a :| Q D0 l m r s
  uncons (Q (D2 a b) l  m  r  s) = a :| Q (D1 b) l m r s
  uncons (Q _ L{} _ NR _) = error "impossible"
  uncons (Q _ NL _ R{} _) = error "impossible"

  -- uncons (Q D0 NL Q0 NR _s) = error "non-regular"
  -- uncons (Q D0 NL (Q1 (P a b)) NR s)                                 = a :| deep (D1 b) Q0 s
  -- uncons (Q D0 NL (Q (D1 (P a b)) NL Q0 NR (D1 (P c d))) NR D0)      = a :| triple b c d
  -- uncons (Q D0 NL (Q (D1 (P a b)) NL Q0 NR (D1 (P c d))) NR (D1 e))  = a :| Q (D2 b c) NL Q0 NR (D2 d e)

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
