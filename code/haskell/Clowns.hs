{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-- Clowns to the Left of Me, Jokers to the Right.
-- Zippers, derivatives and dissections. Every recursive function is tail recursive.

module Main (main) where

import Data.Bifunctor (Bifunctor (..))
import Data.List      (foldl')
import Data.Void      (Void, absurd)

-- List zipper ---------------------------------------------------------

data ListZipper a =
  ListZipper [a] a [a]
  deriving (Eq, Show)

moveRight :: ListZipper a -> Maybe (ListZipper a)
moveRight = \case
  ListZipper bs x (a : as) -> Just (ListZipper (x : bs) a as)
  _                    -> Nothing

moveLeft :: ListZipper a -> Maybe (ListZipper a)
moveLeft = \case
  ListZipper (b : bs) x as -> Just (ListZipper bs b (x : as))
  _                    -> Nothing

plugList :: ListZipper a -> [a]
plugList (ListZipper bs x as) = foldl' (flip (:)) (x : as) bs

-- Tree zipper ---------------------------------------------------------

data Tree a =
    Leaf
  | Node (Tree a) a (Tree a)
  deriving (Eq, Show)

data Step a =
    WentLeft a (Tree a)
  | WentRight (Tree a) a
  deriving (Eq, Show)

data Loc a =
  Loc (Tree a) [Step a]
  deriving (Eq, Show)

downLeft :: Loc a -> Maybe (Loc a)
downLeft = \case
  Loc (Node l x r) p -> Just (Loc l (WentLeft x r : p))
  _                  -> Nothing

downRight :: Loc a -> Maybe (Loc a)
downRight = \case
  Loc (Node l x r) p -> Just (Loc r (WentRight l x : p))
  _                  -> Nothing

up :: Loc a -> Maybe (Loc a)
up = \case
  Loc t (WentLeft  x r : p) -> Just (Loc (Node t x r) p)
  Loc t (WentRight l x : p) -> Just (Loc (Node l x t) p)
  Loc _ []                  -> Nothing

rebuild :: Loc a -> Tree a
rebuild loc@(Loc t _) = case up loc of
  Just loc' -> rebuild loc'
  Nothing   -> t

-- Polynomial functors: one layer of a datatype ------------------------

newtype K a x =
  K a
  deriving Functor

newtype I x =
  I x
  deriving Functor

data (p :+: q) x =
    L (p x)
  | R (q x)
  deriving Functor

data (p :*: q) x =
  p x :*: q x
  deriving Functor

infixr 6 :+:
infixr 7 :*:

-- Polynomial bifunctors: clowns c, jokers j ---------------------------

newtype K2 a c j =
  K2 a

newtype Clowns p c j =
  Clowns (p c)

newtype Jokers p c j =
  Jokers (p j)

data (p :++: q) c j =
    L2 (p c j)
  | R2 (q c j)

data (p :**: q) c j =
  p c j :**: q c j

infixr 6 :++:
infixr 7 :**:

instance Functor (K2 a c) where
  fmap _ (K2 a) = K2 a

instance Bifunctor (K2 a) where
  bimap _ _ (K2 a) = K2 a

instance Functor (Clowns p c) where
  fmap _ (Clowns pc) = Clowns pc

instance Functor p => Bifunctor (Clowns p) where
  bimap f _ (Clowns pc) = Clowns (fmap f pc)

instance Functor p => Functor (Jokers p c) where
  fmap g (Jokers pj) = Jokers (fmap g pj)

instance Functor p => Bifunctor (Jokers p) where
  bimap _ g (Jokers pj) = Jokers (fmap g pj)

instance (Bifunctor p, Bifunctor q) => Functor ((p :++: q) c) where
  fmap g = \case
    L2 pd -> L2 (second g pd)
    R2 qd -> R2 (second g qd)

instance (Bifunctor p, Bifunctor q) => Bifunctor (p :++: q) where
  bimap f g = \case
    L2 pd -> L2 (bimap f g pd)
    R2 qd -> R2 (bimap f g qd)

instance (Bifunctor p, Bifunctor q) => Functor ((p :**: q) c) where
  fmap g (pd :**: qd) = second g pd :**: second g qd

instance (Bifunctor p, Bifunctor q) => Bifunctor (p :**: q) where
  bimap f g (pd :**: qd) = bimap f g pd :**: bimap f g qd

-- Dissection ----------------------------------------------------------

class (Functor p, Bifunctor d) => Dissect p d | p -> d where
  right :: Either (p j) (d c j, c) -> Either (j, d c j) (p c)
  plug  :: x -> d x x -> p x

instance Dissect (K a) (K2 Void) where
  right = \case
    Left  (K a)      -> Right (K a)
    Right (K2 v, _)  -> absurd v
  plug _ (K2 v) = absurd v

instance Dissect I (K2 ()) where
  right = \case
    Left  (I j)       -> Left (j, K2 ())
    Right (K2 (), c)  -> Right (I c)
  plug x (K2 ()) = I x

instance (Dissect p dp, Dissect q dq) => Dissect (p :+: q) (dp :++: dq) where
  right = \case
    Left  (L pj)      -> inL (right (Left pj))
    Left  (R qj)      -> inR (right (Left qj))
    Right (L2 pd, c)  -> inL (right (Right (pd, c)))
    Right (R2 qd, c)  -> inR (right (Right (qd, c)))
    where
      inL = either (\(j, pd) -> Left (j, L2 pd)) (Right . L)
      inR = either (\(j, qd) -> Left (j, R2 qd)) (Right . R)
  plug x = \case
    L2 pd -> L (plug x pd)
    R2 qd -> R (plug x qd)

instance (Dissect p dp, Dissect q dq)
      => Dissect (p :*: q) (dp :**: Jokers q :++: Clowns p :**: dq) where
  right = \case
    Left  (pj :*: qj)                 -> inP (right (Left pj)) qj
    Right (L2 (pd :**: Jokers qj), c) -> inP (right (Right (pd, c))) qj
    Right (R2 (Clowns pc :**: qd), c) -> inQ pc (right (Right (qd, c)))
    where
      inP r qj = case r of
        Left  (j, pd) -> Left (j, L2 (pd :**: Jokers qj))
        Right pc      -> inQ pc (right (Left qj))
      inQ pc = \case
        Left  (j, qd) -> Left (j, R2 (Clowns pc :**: qd))
        Right qc      -> Right (pc :*: qc)
  plug x = \case
    L2 (pd :**: Jokers qx) -> plug x pd :*: qx
    R2 (Clowns px :**: qd) -> px :*: plug x qd

-- Generic traversals --------------------------------------------------

tmap :: Dissect p d => (s -> t) -> p s -> p t
tmap f = go . right . Left
  where
    go (Left (s, d)) = go (right (Right (d, f s)))
    go (Right pt)    = pt

newtype Mu p =
  In (p (Mu p))

tfold :: forall p d v. Dissect p d => (p v -> v) -> Mu p -> v
tfold phi t0 = load t0 []
  where
    load :: Mu p -> [d v (Mu p)] -> v
    load (In pt) stack = next (right (Left pt)) stack

    next :: Either (Mu p, d v (Mu p)) (p v) -> [d v (Mu p)] -> v
    next (Left (t, d)) stack = load t (d : stack)
    next (Right pv)    stack = unload (phi pv) stack

    unload :: v -> [d v (Mu p)] -> v
    unload !v (d : stack) = next (right (Right (d, v))) stack
    unload !v []          = v

divide :: Dissect p d => p x -> Either (x, d Void x) (p Void)
divide = right . Left

unite :: Dissect p d => Either (x, d Void x) (p Void) -> p x
unite = either (\(x, d) -> plug x (first absurd d)) (fmap absurd)

-- Generic zipper ------------------------------------------------------

type Zip p d = (Mu p, [d (Mu p) (Mu p)])

zUp :: Dissect p d => Zip p d -> Maybe (Zip p d)
zUp = \case
  (t, d : ds) -> Just (In (plug t d), ds)
  (_, [])     -> Nothing

zDown :: Dissect p d => Zip p d -> Maybe (Zip p d)
zDown (In pt, ds) = case right (Left pt) of
  Left  (t, d) -> Just (t, d : ds)
  Right _      -> Nothing

zRight :: forall p d. Dissect p d => Zip p d -> Maybe (Zip p d)
zRight = \case
  (t, d : ds) -> case right @p (Right (d, t)) of
    Left  (t', d') -> Just (t', d' : ds)
    Right _        -> Nothing
  (_, [])     -> Nothing

-- Expressions ---------------------------------------------------------

type ExprF = K Int :+: I :*: I
type Expr  = Mu ExprF

val :: Int -> Expr
val = In . L . K

add :: Expr -> Expr -> Expr
add a b = In (R (I a :*: I b))

evalAlg :: ExprF Int -> Int
evalAlg = \case
  L (K n)         -> n
  R (I a :*: I b) -> a + b

eval :: Expr -> Int
eval = tfold evalAlg

data Tm =
    Val Int
  | Add Tm Tm

data Frame =
    AddL Tm
  | AddR Int

evalByHand :: Tm -> Int
evalByHand e0 = load e0 []
  where
    load (Val n)   stack = unload n stack
    load (Add l r) stack = load l (AddL r : stack)

    unload !v []               = v
    unload !v (AddL r : stack) = load r (AddR v : stack)
    unload !v (AddR u : stack) = unload (u + v) stack

-- Checks --------------------------------------------------------------

leftSpine :: Int -> Expr
leftSpine n = foldl' (\t k -> add t (val k)) (val 0) [1 .. n]

pairOf :: ExprF Int -> Maybe (Int, Int)
pairOf = \case
  R (I a :*: I b) -> Just (a, b)
  L _             -> Nothing

checks :: [(String, Bool)]
checks =
  [ ("list zipper",   fmap plugList (moveRight z) == Just [1, 2, 3, 4])
  , ("move back",     (moveRight z >>= moveLeft) == Just z)
  , ("tree zipper",   fmap rebuild (downLeft (Loc tree [])) == Just tree)
  , ("down then up",  (downRight (Loc tree []) >>= up) == Just (Loc tree []))
  , ("tmap",          pairOf (tmap (* 10) layer) == Just (30, 40))
  , ("divide/unite",  pairOf (unite (divide layer)) == Just (3, 4))
  , ("eval",          eval small == 10)
  , ("by hand",       evalByHand (Add (Add (Val 1) (Val 2)) (Val 3)) == 6)
  , ("deep spine",    eval (leftSpine n) == n * (n + 1) `div` 2)
  , ("generic zip",   fmap (eval . fst) (zDown (small, []) >>= zRight) == Just 7)
  , ("zip up",        fmap (eval . fst) (zDown (small, []) >>= zUp) == Just 10)
  ]
  where
    z     = ListZipper [2, 1] 3 [4 :: Int]
    tree  = Node (Node Leaf 1 Leaf) 2 (Node Leaf (3 :: Int) Leaf)
    layer = R (I 3 :*: I 4) :: ExprF Int
    small = add (add (val 1) (val 2)) (add (val 3) (val 4))
    n     = 200000

main :: IO ()
main = mapM_ report checks
  where
    report (name, ok) = putStrLn ((if ok then "ok    " else "FAIL  ") ++ name)
