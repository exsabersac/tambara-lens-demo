{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

-- Step 2: Profunctor + Strong encoding of Lens (base only)
module Main where

------------------------------------------------------------
-- 1. Profunctor / Strong
------------------------------------------------------------

class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

-- Strong = Tambara module for cartesian product (⊗ = (,))
class Profunctor p => Strong p where
  first'  :: p a b -> p (a, c) (b, c)
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'
    where
      swap (x, y) = (y, x)

instance Profunctor (->) where
  dimap f g h = g . h . f

instance Strong (->) where
  first'  f (a, c) = (f a, c)
  second' f (c, a) = (c, f a)

-- Forget: read-only "profunctor" for view
newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  dimap f _ (Forget k) = Forget (k . f)

instance Strong (Forget r) where
  first'  (Forget k) = Forget (\(a, _) -> k a)
  second' (Forget k) = Forget (\(_, a) -> k a)

------------------------------------------------------------
-- 2. Optic encoding
------------------------------------------------------------

-- Classic get/set
data LensGS s t a b = LensGS
  { gsView :: s -> a
  , gsSet  :: s -> b -> t
  }

-- Profunctor optic (van Laarhoven–style via Strong)
type Lens s t a b = forall p. Strong p => p a b -> p s t
type Lens' s a = Lens s s a a

-- Core assembly: get/set → Strong optic
--   dimap (\s -> (view s, s)) (\(b, s) -> set s b) . first'
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'

------------------------------------------------------------
-- 3. Operations from the optic
------------------------------------------------------------

over :: Lens s t a b -> (a -> b) -> s -> t
over l f = l f  -- (->) is Strong

set :: Lens s t a b -> b -> s -> t
set l b = over l (const b)

view :: Lens s t a b -> s -> a
view l = runForget (l (Forget id))

------------------------------------------------------------
-- 4. Examples
------------------------------------------------------------

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))
-- Note: for (->), first' itself is already _1

_2 :: Lens (c, a) (c, b) a b
_2 = lens snd (\(c, _) b -> (c, b))

data Address = Address { city :: String, zipCode :: String }
  deriving (Show, Eq)

data Person = Person { name :: String, address :: Address }
  deriving (Show, Eq)

_city :: Lens' Address String
_city = lens city (\addr c -> addr { city = c })

_address :: Lens' Person Address
_address = lens address (\p a -> p { address = a })

-- Optic composition = function composition
_cityOf :: Lens' Person String
_cityOf = _address . _city

alice :: Person
alice = Person "Alice" (Address "Shanghai" "200000")

main :: IO ()
main = do
  putStrLn "== (->) via over / set / view =="
  print $ view _1 (True, 42 :: Int)
  print $ set  _1 False (True, 42 :: Int)
  print $ over _2 (*10) (True, 42 :: Int)

  putStrLn "== nested (compose = (.)) =="
  print $ view _cityOf alice
  print $ set  _cityOf "Beijing" alice
  print $ over _cityOf (++ "!") alice

  putStrLn "== first' is _1 on (->) =="
  print $ (first' not :: (Bool, Int) -> (Bool, Int)) (True, 1)

  putStrLn "== round-trip: optic from get/set still views =="
  -- 注意：Lens 是 rank-2，不要先 let 绑成单态再传给 view
  print $ view (lens fst (\(_, c) b -> (b, c))) ("hi", 9 :: Int)
