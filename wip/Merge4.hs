{-# LANGUAGE GADTs, PolyKinds, RankNTypes #-}

module RS where

import Control.Category.Free.View
import Control.Category.Free.Catenated

data Pair r a b where
 Pair :: r b c -> r a b -> Pair r a c

-- bottom stack non-empty list of ones down
data D1s l m a b where
 D1 :: l b c -> D1s (Pair l) m a b -> D1s l m a c
 LD :: l a b -> D1s l (Pair l) a b

data D l r a b where
 D0  :: D (Pair l) r a b                   -> D l r a b -- invariant D0 z -- z isn't 0-exposed
 (:<):: D1s l m b c -> D m r a b    -> D l r a c -- invariant _ :< x -- x isn't (:<)
 D2  :: l c d -> l b c -> D (Pair l) r a b -> D l r a d -- invariant D2 x y z -- z isn't 2-exposed
 D   :: D r r a a

-- non-empty list of ones up
data U1s m r a b where
 U1 :: U1s m (Pair r) b c -> r a b -> U1s m r a c
 LU :: r a b -> U1s (Pair r) r a b

data U m r a b where
 U0  :: U l (Pair m) a b -> U l r a b
 (:>):: U l m b c -> U1s m r a b -> U l r a c
 U2  :: U l (Pair r) c d -> r b c -> r a b -> U l r a d
 U   :: U r r a a

data B m a b where
 B0 :: B r a a
 B1 :: r a b -> B r a b

data Q r a b where
 Q  :: D r m c d -> B m b c -> U m r a b -> Q r a d

null :: Q r a b -> Bool
null (Q D B0 U) = True
null _ = False

empty :: Q r a a
empty = Q D B0 U

singleton :: r a b -> Q r a b
singleton a = Q D (B1 a) U

instance Cons Q where
  a <| Q D B0 U = Q D (B1 a) U
  a <| Q D (B1 b) U = Q (LD a :< D) B0 (U :> LU b)

-- cons 1
d1 :: l b c -> D (Pair l) m a b -> D l m a c
d1 l (ls :< ms) = D1 l ls :< ms
d1 l ms         = LD l :< ms

-- snoc 1
u1 :: U m (Pair r) b c -> r a b -> U m r a c
u1 (ms :> rs) r = ms :> U1 rs r
u1 ms r         = ms :> LU r

-- works for non-2 exposed deque
ncons :: r b c -> Q r a b -> Q r a c
ncons a q = case q of
  Q D B0 r     -> Q D (B1 a) r
  Q D (B1 b) U -> Q (LD a :< D) B0 (U :> LU b)
  Q (D0 p) m r -> Q (d1 a p) m r
  Q (D1 b p :< q) m r        -> Q (D2 a b (p :< q)) m r
  Q (D1 b p :< D2 c d q) m r -> Q (D2 a b (p :< D0 (ncons (Pair c d) q))) m r

-- ncons'
{-
  Q (D0 x y) (
  Q
  Q (D1s ND) (B1 b) (U1s NU) -> Q (D1s (D1 a ND)) B0 (U1s (U1 NU b))
  Q (D0 ones ND)
  Q (D1s (D1 b ND)
ncons a (Q (D1 b p4) p q s s4) = Q (D2 a b)
ncons a (Q p4 p q s s4)
-}

-- for a non-2 exposed deque
