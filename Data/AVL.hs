{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE UnboxedTuples        #-}

module Data.AVL where

import Prelude hiding (lookup, null)
import Control.Exception (assert)

-- | Balance factor.
-- N : -1
-- Z :  0
-- P : +1
data BFactor = N | Z | P
  deriving Show

data Map k a = Nil
             | NodeN !k a !(Map k a) !(Map k a)
             | NodeZ !k a !(Map k a) !(Map k a)
             | NodeP !k a !(Map k a) !(Map k a)
  deriving Show

{-# INLINE view #-}
view :: Map k a -> Maybe (k, a, BFactor, Map k a, Map k a)
view Nil = Nothing
view (NodeN k x l r) = Just (k, x, N, l, r)
view (NodeZ k x l r) = Just (k, x, Z, l, r)
view (NodeP k x l r) = Just (k, x, P, l, r)

{-# COMPLETE Nil, Node #-}
pattern Node :: k -> a -> BFactor -> Map k a -> Map k a -> Map k a
pattern Node k x f l r <- (view -> Just (k, x, f, l, r))
  where
    Node k x N l r = NodeN k x l r
    Node k x Z l r = NodeZ k x l r
    Node k x P l r = NodeP k x l r

empty :: Map k a
empty = Nil

{-# INLINE singleton #-}
singleton :: k -> a -> Map k a
singleton k x = Node k x Z Nil Nil

insert :: forall k a. Ord k => k -> a -> Map k a -> Map k a
insert k' x' = \n -> case n of
  Nil -> singleton k' x'
  Node k x f l r -> case compare k' k of
    LT -> case f of
      N -> longerLeft'  k x l r
      Z -> neitherLeft' k x l r
      P -> shorterLeft' k x l r
    EQ -> Node k' x' f l r
    GT -> case f of
      N -> shorterRight' k x l r
      Z -> neitherRight' k x l r
      P -> longerRight'  k x l r
  where
    insert' :: Map k a -> (# Bool, Map k a #)
    insert' = \n -> case n of
      Nil -> (# True, #) $! singleton k' x'
      Node k x f l r -> case compare k' k of
        LT -> case f of
          N -> longerLeft  k x l r
          Z -> neitherLeft k x l r
          P -> shorterLeft k x l r
        EQ -> (# False, #) $! Node k' x' f l r 
        GT -> case f of
          N -> shorterRight k x l r
          Z -> neitherRight k x l r
          P -> longerRight  k x l r

    {-# INLINE shorterLeft #-}
    shorterLeft :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    shorterLeft k x l r = (# False, #) $! shorterLeft' k x l r

    {-# INLINE shorterRight #-}
    shorterRight :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    shorterRight k x l r = (# False, #) $! shorterRight' k x l r

    {-# INLINE neitherLeft #-}
    neitherLeft :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    neitherLeft k x l r = let (# p, l' #) = insert' l in case p of
      True  -> (# True,  #) $! Node k x N l' r
      False -> (# False, #) $! Node k x Z l' r

    {-# INLINE neitherRight #-}
    neitherRight :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    neitherRight k x l r = let (# p, r' #) = insert' r in case p of
      True  -> (# True,  #) $! Node k x P l r'
      False -> (# False, #) $! Node k x Z l r'

    {-# INLINE longerLeft #-}
    longerLeft :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    longerLeft k x l r = (# False, #) $! longerLeft' k x l r

    {-# INLINE longerRight #-}
    longerRight :: k -> a -> Map k a -> Map k a -> (# Bool, Map k a #)
    longerRight k x l r = (# False, #) $! longerRight' k x l r

    {-# INLINE shorterLeft' #-}
    shorterLeft' :: k -> a -> Map k a -> Map k a -> Map k a
    shorterLeft' k x l r = let (# p, l' #) = insert' l in case p of
      True  -> Node k x Z l' r
      False -> Node k x P l' r

    {-# INLINE shorterRight' #-}
    shorterRight' :: k -> a -> Map k a -> Map k a -> Map k a
    shorterRight' k x l r = let (# p, r' #) = insert' r in case p of
      True  -> Node k x Z l r'
      False -> Node k x N l r'

    {-# INLINE neitherLeft' #-}
    neitherLeft' :: k -> a -> Map k a -> Map k a -> Map k a
    neitherLeft' k x l r = let (# p, l' #) = insert' l in case p of
      True  -> Node k x N l' r
      False -> Node k x Z l' r

    {-# INLINE neitherRight' #-}
    neitherRight' :: k -> a -> Map k a -> Map k a -> Map k a
    neitherRight' k x l r = let (# p, r' #) = insert' r in case p of
      True  -> Node k x P l r'
      False -> Node k x Z l r'

    longerLeft' :: k -> a -> Map k a -> Map k a -> Map k a
    longerLeft' k x l r = case l of
      Nil -> error "AVL.insert: f == N && l == Nil"
      Node lk lx lf ll lr -> case compare k' lk of
        LT -> case lf of
          -- longer left - longer left
          N -> n' where
            n' = Node k x N l' r
            l' = longerLeft' lk lx ll lr
          -- longer left - neither left (rotate right)
          Z -> let (# p, ll' #) = insert' ll in case p of
              True  -> l' where
                l' = Node lk lx Z ll' n'
                n' = Node  k  x Z lr  r
              False -> n' where
                n' = Node  k  x N  l'  r
                l' = Node lk lx Z ll' lr
          -- longer left - shorter left
          P -> n' where
            n' = Node k x N l' r
            l' = shorterLeft' lk lx ll lr
        EQ -> n' where
          n' = Node k  x   N  l'  r
          l' = Node k' x' lf ll  lr
        GT -> case lf of
          -- longer left - shorter right
          N -> n' where
            n' = Node k x N l' r
            l' = shorterRight' lk lx ll lr
          -- longer left - neither right
          Z -> case lr of
            --  longer left - neither right @ Nil (rotate left-right)
            Nil -> lr' where
              lr' = Node  k'  x' Z   l'   n'
              l'  = assert (null ll) $ Node lk  lx  Z  ll  Nil  -- ll is Nil
              n'  = assert (null  r) $ Node  k   x  Z Nil    r  -- r  is Nil
            Node lrk lrx lrf lrl lrr -> case compare k' lrk of
              LT -> case lrf of
                -- longer left - neither right - longer left
                N -> n' where
                  n'  = Node  k  x N  l' r
                  l'  = Node lk lx Z ll lr'
                  lr' = longerLeft' lrk lrx lrl lrr
                -- longer left - neither right - neither left (rotate left-right)
                Z -> let (# p, lrl' #) = insert' lrl in case p of
                    True  -> lr' where
                      lr' = Node lrk lrx Z   l'   n'
                      l'  = Node  lk  lx Z  ll  lrl'
                      n'  = Node   k   x P lrr    r
                    False -> n' where
                      n'  = Node   k   x N   l'   r
                      l'  = Node  lk  lx Z  ll   lr'
                      lr' = Node lrk lrx Z lrl' lrr
                -- longer left - neither right - shorter left
                P -> n' where
                  n'  = Node  k  x N  l'  r
                  l'  = Node lk lx Z ll  lr'
                  lr' = shorterLeft' lrk lrx lrl lrr
              EQ -> n' where
                n'  = Node  k   x    N   l'  r
                l'  = Node lk  lx    Z  ll  lr'
                lr' = Node  k'  x' lrf lrl lrr
              GT -> case lrf of
                -- longer left - neither right - shorter right
                N -> n' where
                  n'  = Node  k  x N  l' r
                  l'  = Node lk lx Z ll lr'
                  lr' = shorterRight' lrk lrx lrl lrr
                -- longer left - neither right - neither right (rotate left-right)
                Z -> let (# p, lrr' #) = insert' lrr in case p of
                    True  -> lr' where
                      lr' = Node lrk lrx Z   l'   n'
                      l'  = Node  lk  lx N  ll  lrl
                      n'  = Node   k   x Z lrr'   r
                    False -> n' where
                      n'  = Node   k   x N   l'   r
                      l'  = Node  lk  lx Z  ll   lr'
                      lr' = Node lrk lrx Z lrl  lrr'
                -- longer left - neither right - longer right
                P -> n' where
                  n'  = Node  k  x N  l'  r
                  l'  = Node lk lx Z ll  lr'
                  lr' = longerRight' lrk lrx lrl lrr
          -- longer left - longer right
          P -> n' where
            n' = Node k x N l' r
            l' = longerRight' lk lx ll lr

    longerRight' :: k -> a -> Map k a -> Map k a -> Map k a
    longerRight' k x l r = case r of
      Nil -> error "AVL.insert: f == P && r == Nil"
      Node rk rx rf rl rr -> case compare k' rk of
        LT -> case rf of
          -- longer right - longer left
          N -> n' where
            n' = Node k x P l r'
            r' = longerLeft' rk rx rl rr
          -- longer right - neither left
          Z -> case rl of
            -- longer right - neither left @ Nil (rotate right-left)
            Nil -> rl' where
              rl' = Node  k'  x' Z   n'   r'
              n'  = assert (null  l) $ Node  k   x  Z   l  Nil  -- l is Nil
              r'  = assert (null rr) $ Node rk  rx  Z Nil   rr  -- rr is Nil
            Node rlk rlx rlf rll rlr -> case compare k' rlk of
              LT -> case rlf of
                -- longer right - neither left - longer left
                N -> n' where
                  n'  = Node  k  x P  l   r'
                  r'  = Node rk rx Z rl' rr
                  rl' = longerLeft' rlk rlx rll rlr
                -- longer right - neither left - neither left (rotate right-left)
                Z -> let (# p, rll' #) = insert' rll in case p of
                    True  -> rl' where
                      rl' = Node rlk rlx Z   n'   r'
                      n'  = Node   k   x Z   l  rll'
                      r'  = Node  rk  rx P rlr   rr
                    False -> n' where
                      n'  = Node   k   x P   l    r'
                      r'  = Node  rk  rx Z  rl'  rr
                      rl' = Node rlk rlx Z rll' rlr
                -- longer right - neither left - shorter left
                P -> n' where
                  n'  = Node  k  x P  l   r'
                  r'  = Node rk rx Z rl' rr
                  rl' = shorterLeft' rlk rlx rll rlr
              EQ -> n' where
                n'  = Node  k  x    P   l    r'
                r'  = Node rk rx    Z  rl'  rr
                rl' = Node  k' x' rlf rll  rlr
              GT -> case rlf of
                -- longer right - neither left - shorter right
                N -> n' where
                  n'  = Node  k  x P  l   r'
                  r'  = Node rk rx Z rl' rr
                  rl' = shorterRight' rlk rlx rll rlr
                -- longer right - neither left - neither right (rotate right-left)
                Z -> let (# p, rlr' #) = insert' rlr in case p of
                    True  -> rl' where
                      rl' = Node rlk rlx Z   n'   r'
                      n'  = Node   k   x N   l  rll
                      r'  = Node  rk  rx Z rlr'  rr
                    False -> n' where
                      n'  = Node   k   x P   l    r'
                      r'  = Node  rk  rx Z  rl'  rr
                      rl' = Node rlk rlx Z rll  rlr'
                -- longer right - neither left - longer right
                P -> n' where
                  n'  = Node  k  x P  l   r'
                  r'  = Node rk rx Z rl' rr
                  rl' = longerRight' rlk rlx rll rlr
          -- longer right - shorter left
          P -> n' where
            n' = Node k x P l r'
            r' = shorterLeft' rk rx rl rr
        EQ -> n' where
          n' = Node k  x   P  l  r'
          r' = Node k' x' rf rl rr
        GT -> case rf of
          -- longer right - shorter right
          N -> n' where
            n' = Node k x P l r'
            r' = shorterRight' rk rx rl rr
          -- longer right - neither right (rotate left)
          Z -> let (# p, rr' #) = insert' rr in case p of
              True  -> r' where
                r' = Node rk rx Z n' rr'
                n' = Node  k  x Z l  rl
              False -> n' where
                n' = Node  k  x P  l  r'
                r' = Node rk rx Z rl rr'
          -- longer right - longer right
          P -> n' where
            n' = Node k x P l r'
            r' = longerRight' rk rx rl rr

delete :: forall k a. Ord k => k -> Map k a -> Map k a
delete k' = \n -> snd $ delete' n
  where
    delete' :: Map k a -> (Bool, Map k a)
    delete' = \n -> case n of
      Nil -> (False, Nil)
      Node k x f l r -> case compare k' k of
        LT -> case f of
          N -> longerLeft'  k x l r
          Z -> neitherLeft' k x l r
          P -> shorterLeft' k x l r
        EQ -> case f of
          N -> case popFirst r of
            Nothing -> (True, l)
            Just (p, fk, fx, r_) -> rotateAfterShorterRight (,) p fk fx l r_
          Z -> case popFirst r of
            Nothing -> assert (null l) $ (False, l) -- l is Nil
            Just (p, fk, fx, r_) -> case p of
              True  -> (False, Node fk fx N l r_)
              False -> (False, Node fk fx Z l r_)
          P -> case popFirst r of
            Nothing -> error "AVL.delete: f == P && popFirst r == Nothing"
            Just (p, fk, fx, r_) -> case p of
              True  -> (True,  Node fk fx Z l r_)
              False -> (False, Node fk fx P l r_)
        GT -> case f of
          N -> shorterRight' k x l r
          Z -> neitherRight' k x l r
          P -> longerRight'  k x l r

    popFirst :: Map k a -> Maybe (Bool, k, a, Map k a)
    popFirst = \n -> case n of
      Nil -> Nothing
      Node k x f l r -> case f of
        -- longer left
        N -> case popFirst l of
          Nothing -> error "AVL.delete: f == N && popFirst l == Nothing"
          Just (p, fk, fx, l') -> case p of
            True  -> Just (True, fk, fx, n') where
              n' = Node k x Z l' r
            False -> Just (False, fk, fx, n') where
              n' = Node k x N l' r
        -- neither left
        Z -> case popFirst l of
          Nothing -> assert (null r) $ Just (True, k, x, r)  -- r is Nil
          Just (p, fk, fx, l') -> case p of
            True  -> Just (False, fk, fx, n') where
              n' = Node k x P l' r
            False -> Just (False, fk, fx, n') where
              n' = Node k x Z l' r
        -- shorter left
        P -> case popFirst l of
          Nothing -> Just (True, k, x, r)
          Just (p, fk, fx, l_) -> Just $
            rotateAfterShorterLeft (\x y -> (x, fk, fx, y)) p k x l_ r

    rotateAfterShorterLeft :: forall r. (Bool -> Map k a -> r) ->
                              Bool -> k -> a -> Map k a -> Map k a -> r
    rotateAfterShorterLeft cont p k x l_ r = case p of
      True  -> case r of
        Nil -> error "AVL.delete: f == P && r == Nil"
        Node rk rx rf rl rr -> case rf of
          -- rotate right-left
          N -> case rl of
            Nil -> error "AVL.delete: rf == N && rl == Nil"
            Node rlk rlx rlf rll rlr -> case rlf of
              N -> cont True n' where
                n' = Node rlk rlx Z   l'   r'
                l' = Node   k   x Z   l_ rll
                r' = Node  rk  rx P rlr   rr
              Z -> cont True n' where
                n' = Node rlk rlx Z   l'   r'
                l' = Node   k   x Z   l_ rll
                r' = Node  rk  rx Z rlr   rr
              P -> cont True n' where
                n' = Node rlk rlx Z   l'   r'
                l' = Node   k   x N   l_ rll
                r' = Node  rk  rx Z rlr   rr
          -- rotate left
          Z -> cont False n' where
            n' = Node rk rx N l' rr
            l' = Node  k  x P l_  rl
          -- rotate left
          P -> cont True n' where
            n' = Node rk rx Z l' rr
            l' = Node  k  x Z l_  rl
      False -> cont False n' where
        n' = Node k x P l_ r

    rotateAfterShorterRight :: forall r. (Bool -> Map k a -> r) ->
                               Bool -> k -> a -> Map k a -> Map k a -> r
    rotateAfterShorterRight cont p k x l r_ = case p of
      True  -> case l of
        Nil -> error "AVL.delete: f == N && l == Nil"
        Node lk lx lf ll lr -> case lf of
          -- rotate right
          N -> cont True n' where
            n' = Node lk lx N ll r'
            r' = Node  k  x N lr r_
          -- rotate right
          Z -> cont False n' where
            n' = Node lk lx P ll r'
            r' = Node  k  x N ll r_
          -- rotate left-right
          P -> case lr of
            Nil -> error "AVL.delete: lf == P && lr == Nil"
            Node lrk lrx lrf lrl lrr -> case lrf of
              N -> cont True n' where
                n' = Node lrk lrx Z   l'  r'
                l' = Node  lk  lx Z  ll lrl
                r' = Node   k   x P lrr   r_
              Z -> cont True n' where
                n' = Node lrk lrx Z   l'  r'
                l' = Node  lk  lx Z  ll lrl
                r' = Node   k   x Z lrr   r_
              P -> cont True n' where
                n' = Node lrk lrx Z   l'  r'
                l' = Node  lk  lx N  ll lrl
                r' = Node   k   x Z lrr   r_
      False -> cont False n' where
        n' = Node k x N l r_

    shorterLeft' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    shorterLeft' k x l r = let (p, l_) = delete' l in
      rotateAfterShorterLeft (,) p k x l_ r

    shorterRight' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    shorterRight' k x l r = let (p, r_) = delete' r in
      rotateAfterShorterRight (,) p k x l r_

    neitherLeft' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    neitherLeft' k x l r = let (p, l_) = delete' l in case p of
      True  -> (False, Node k x P l_ r)
      False -> (False, Node k x Z l_ r)

    neitherRight' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    neitherRight' k x l r = let (p, r_) = delete' r in case p of
      True  -> (False, Node k x N l r_)
      False -> (False, Node k x Z l r_)

    longerLeft' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    longerLeft' k x l r = let (p, l_) = delete' l in case p of
      True  -> (True,  Node k x Z l_ r)
      False -> (False, Node k x N l_ r)

    longerRight' :: k -> a -> Map k a -> Map k a -> (Bool, Map k a)
    longerRight' k x l r = let (p, r_) = delete' r in case p of
      True  -> (True,  Node k x Z l r_)
      False -> (False, Node k x P l r_)

{-# INLINE null #-}
null :: Map k a -> Bool
null Nil = True
null _   = False

size :: Map k a -> Int
size Nil = 0
size (Node _ _ _ l r) = size l + size r + 1

lookup :: Ord k => k -> Map k a -> Maybe a
lookup _ Nil = Nothing
lookup k' (Node k x _ l r) = case compare k' k of
  LT -> lookup k' l
  EQ -> Just x
  GT -> lookup k' r

member :: Ord k => k -> Map k a -> Bool
member k' Nil = False
member k' (Node k x _ l r) = case compare k' k of
  LT -> member k' l
  EQ -> True
  GT -> member k' r
