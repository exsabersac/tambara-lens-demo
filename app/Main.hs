{-# LANGUAGE NamedFieldPuns #-}

-- Step 1: classic get/set Lens (base only, stack lts-21.25 / GHC 9.4.8)
module Main where

data Lens s t a b = Lens
  { view :: s -> a
  , set  :: s -> b -> t
  }

type Lens' s a = Lens s s a a

_1 :: Lens (a, c) (b, c) a b
_1 = Lens fst (\(_, c) b -> (b, c))

_2 :: Lens (c, a) (c, b) a b
_2 = Lens snd (\(c, _) b -> (c, b))

data Address = Address { city :: String, zipCode :: String }
  deriving (Show, Eq)

data Person = Person { name :: String, address :: Address }
  deriving (Show, Eq)

_city :: Lens' Address String
_city = Lens city (\addr c -> addr { city = c })

_addr :: Lens' Person Address
_addr = Lens address (\p a -> p { address = a })

compose :: Lens' s a -> Lens' a b -> Lens' s b
compose (Lens v1 s1) (Lens v2 s2) = Lens
  { view = v2 . v1
  , set  = \s b -> s1 s (s2 (v1 s) b)
  }

_cityOf :: Lens' Person String
_cityOf = compose _addr _city

-- three laws as Boolean checks on examples
law1 :: (Eq a) => Lens' s a -> s -> a -> Bool
law1 l s a = view l (set l s a) == a

law2 :: (Eq s) => Lens' s a -> s -> Bool
law2 l s = set l s (view l s) == s

law3 :: (Eq s) => Lens' s a -> s -> a -> a -> Bool
law3 l s b b' = set l (set l s b) b' == set l s b'

alice :: Person
alice = Person "Alice" (Address "Shanghai" "200000")

main :: IO ()
main = do
  putStrLn "== product lenses =="
  print $ view _1 (True, 42 :: Int)
  print $ set  _1 (True, 42 :: Int) False
  print $ view _2 (True, 42 :: Int)

  putStrLn "== nested =="
  print $ view _cityOf alice
  print $ set  _cityOf alice "Beijing"

  putStrLn "== laws on _cityOf / alice =="
  print $ law1 _cityOf alice "Hangzhou"
  print $ law2 _cityOf alice
  print $ law3 _cityOf alice "A" "B"
