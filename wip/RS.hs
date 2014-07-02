{-# LANGUAGE GADTs, PolyKinds, RankNTypes #-}
-- | Kaplan and Tarjan Deque w/ explicit Recursive Slowdown
module RS where

import Control.Category.Free.View
import Control.Category.Free.Catenated

data Digit r a b where
  D0 :: Digit r a a
  D1 :: r a b -> Digit r a b
  D2 :: r b c -> r a b -> Digit r a c
  D3 :: r c d -> r b c -> r a b -> Digit r a d
  D4 :: r d e -> r c d -> r b c -> r a b -> Digit r a d
  D5 :: r e f -> r d e -> r c d -> r b c -> r a b -> Digit r a d

data Color = Red | Yellow | Green
  deriving (Eq,Ord,Show,Read)

color :: Digit -> Color
color D0 = Red
color D1{} = Yellow
color D2{} = Green
color D3{} = Green
color D4{} = Yellow
color D5{} = Red

type PST r = Pair (Digit (Tree r))

data Pair r a b where
  Pair :: r b c -> r a b -> Pair r a c

data Tree r a b where
  Leaf :: r a b -> Tree r a b
  Bin  :: Tree r b c -> Tree r a b -> Tree r a c

data List r a b where
  Nil :: List r a a
  Cons :: r b c -> List r a b -> List r a c

data C r a b
  = PS (PST r a b)
  | Y (List (PST r) a b) -- non-empty list

newtype Deque r a b = Deque (List (C r) a b)

null :: Deque r a b -> Bool
null (Deque Nil) = True
null _ = False

empty :: Deque r a a
empty = Deque Nil

instance Cons Deque where
  a <| Deque q = case popPS q of
    Empty -> Deque (Cons (PS (Pair (Cons (Leaf a) Nil) Nil)) Nil)
    Pair px sx:| cs1 ->

normD :: List (C r) a b -> List (C r) a b
normD l@(Cons c cs) = case firstColor c cs of

firstColor :: C r b c -> List (C r) a b -> Color
firstColor (Y _) _ = Yellow
firstColor (Ps ([],sx

popPS :: List (C r) a b -> View (PST r) (List (C r)) a b
popPS Nil = Empty
popPS (Cons (PS ps) cs)           = ps :| cs
popPS (Cons (Y (Cons ps Nil)) cs) = ps :| cs
popPS (Cons (Y (Cons ps pss)) cs  = ps :| Cons (Y pss) cs


