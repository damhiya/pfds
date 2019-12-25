{-# LANGUAGE ScopedTypeVariables #-}

module Data.AVL where

-- | Balance factor.
-- L : left-heavy
-- B : balanced
-- R : right-heavy
data BFactor = N | Z | P
  deriving Show

data Map k a = Nil | Node !k a {-# UNPACK #-} !BFactor (Map k a) (Map k a)
  deriving Show

empty :: Map k a
empty = Nil

singleton :: k -> a -> Map k a
singleton k x = Node k x Z Nil Nil

type Cont k a = Bool -> Map k a -> Map k a

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
    insert' :: Map k a -> Cont k a -> Map k a
    insert' n cont = case n of
      Nil -> cont True (singleton k' x')
      Node k x f l r -> case compare k' k of
        LT -> case f of
          N -> longerLeft  k x l r cont
          Z -> neitherLeft k x l r cont
          P -> shorterLeft k x l r cont
        EQ -> cont False (Node k' x' f l r)
        GT -> case f of
          N -> shorterRight k x l r cont
          Z -> neitherRight k x l r cont
          P -> longerRight  k x l r cont
    
    {-# INLINE shorterLeft #-}
    shorterLeft :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    shorterLeft k x l r cont = cont False $ shorterLeft' k x l r
    
    {-# INLINE shorterRight #-}
    shorterRight :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    shorterRight k x l r cont = cont False $ shorterRight' k x l r
    
    {-# INLINE neitherLeft #-}
    neitherLeft :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    neitherLeft k x l r cont = insert' l $ \p l' -> cont p $ case p of
      True  -> Node k x N l' r
      False -> Node k x Z l' r
    
    {-# INLINE neitherRight #-}
    neitherRight :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    neitherRight k x l r cont = insert' r $ \p r' -> cont p $ case p of
      True  -> Node k x P l r'
      False -> Node k x Z l r'
    
    {-# INLINE longerLeft #-}
    longerLeft  :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    longerLeft k x l r cont = cont False $ longerLeft' k x l r
    
    {-# INLINE longerRight #-}
    longerRight :: k -> a -> Map k a -> Map k a -> Cont k a -> Map k a
    longerRight k x l r cont = cont False $ longerRight' k x l r
    
    {-# INLINE shorterLeft' #-}
    shorterLeft' :: k -> a -> Map k a -> Map k a -> Map k a
    shorterLeft' k x l r = insert' l $ \p l' -> case p of
      True  -> Node k x Z l' r
      False -> Node k x P l' r
    
    {-# INLINE shorterRight' #-}
    shorterRight' :: k -> a -> Map k a -> Map k a -> Map k a
    shorterRight' k x l r = insert' r $ \p r' -> case p of
      True  -> Node k x Z l r'
      False -> Node k x N l r'
    
    {-# INLINE neitherLeft' #-}
    neitherLeft' :: k -> a -> Map k a -> Map k a -> Map k a
    neitherLeft' k x l r = insert' l $ \p l' -> case p of
      True  -> Node k x N l' r
      False -> Node k x Z l' r

    {-# INLINE neitherRight' #-}
    neitherRight' :: k -> a -> Map k a -> Map k a -> Map k a
    neitherRight' k x l r = insert' r $ \p r' -> case p of
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
          Z -> insert' ll cont' where
            cont' p ll' = case p of
              True  -> l' where
                l' = Node lk lx Z ll' n'
                n' = Node  k  x Z lr  r
              False -> n' where
                n' = Node  k  x N  l' r
                l' = Node lk lx Z ll' r
          -- longer left - shorter left
          P -> n' where
            n' = Node k x N l' r
            l' = shorterLeft' lk lx ll lr
        EQ -> n' where
          n' = Node k  x   N  l'  r
          l' = Node k' x' lf ll  lr
        GT -> case lf of
          -- longer left - shorter right
          N -> shorterRight lk lx ll lr cont' where
            cont' False l' = Node k x N l' r
          -- longer left - neither right
          Z -> case lr of
            --  longer left - neither right @ Nil (rotate left-right)
            Nil -> lr' where
              lr' = Node  k'  x' Z   l'   n'
              l'  = Node lk  lx  Z  ll  Nil  -- ll is Nil
              n'  = Node  k   x  Z Nil    r  -- r  is Nil
            Node lrk lrx lrf lrl lrr -> case compare k' lrk of
              LT -> case lrf of
                -- longer left - neither right - longer left
                N -> n' where
                  n'  = Node  k  x N  l' r
                  l'  = Node lk lx Z ll lr'
                  lr' = longerLeft' lrk lrx lrl lrr
                -- longer left - neither right - neither left (rotate left-right)
                Z -> insert' lrl cont' where
                  cont' p lrl' = case p of
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
                N -> shorterRight lrk lrx lrl lrr cont' where
                  cont' False lr' = n' where
                    n' = Node  k  x N  l' r
                    l' = Node lk lx Z ll lr'
                -- longer left - neither right - neither right (rotate left-right)
                Z -> insert' lrr cont' where
                  cont' p lrr' = case p of
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
              n'  = Node  k   x  Z   l  Nil  -- l is Nil
              r'  = Node rk  rx  Z Nil   rr  -- rr is Nil
            Node rlk rlx rlf rll rlr -> case compare k' rlk of
              LT -> case rlf of
                -- longer right - neither left - longer left
                N -> n' where
                  n'  = Node  k  x P  l   r'
                  r'  = Node rk rx Z rl' rr
                  rl' = longerLeft' rlk rlx rll rlr
                -- longer right - neither left - neither left (rotate right-left)
                Z -> insert' rll cont' where
                  cont' p rll' = case p of
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
                Z -> insert' rlr cont' where
                  cont' p rlr' = case p of
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
          Z -> insert' rr cont' where
            cont' p rr' = case p of
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