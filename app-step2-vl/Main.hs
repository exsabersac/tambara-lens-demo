{-# LANGUAGE RankNTypes #-}

-- | van Laarhoven（Functor）形态：原理 + 组合 + 丰富示例
--
-- 详细教程：docs/van-Laarhoven教程.md（含 §2 原理、§3 组合）
-- 注意：这里的 Functor f 是「效果容器」，不是 Functor strength / Tambara。
module Main where

import Data.Functor.Identity (Identity (..))
import Data.Monoid (Sum (..))

------------------------------------------------------------------------
-- 1. 类型与核心拼法
------------------------------------------------------------------------

type Lens s t a b =
  forall f. Functor f => (a -> f b) -> s -> f t

type Lens' s a = Lens s s a a

newtype Const r a = Const { getConst :: r }

instance Functor (Const r) where
  fmap _ (Const r) = Const r

-- | get/set → VL（整条故事的「生成器」）
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP afb s =
  fmap (setP s) (afb (get s))

view :: Lens s t a b -> s -> a
view l s = getConst (l Const s)

over :: Lens s t a b -> (a -> b) -> s -> t
over l f s = runIdentity (l (Identity . f) s)

set :: Lens s t a b -> b -> s -> t
set l b = over l (const b)

------------------------------------------------------------------------
-- 2. 元组焦点（与 Step 1/2 对齐）
------------------------------------------------------------------------

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))

_2 :: Lens (c, a) (c, b) a b
_2 = lens snd (\(c, _) b -> (c, b))

------------------------------------------------------------------------
-- 3. 记录字段：命名 Lens
------------------------------------------------------------------------

data Address = Address
  { _city :: String
  , _zip  :: Int
  }
  deriving (Show, Eq)

data Person = Person
  { _name    :: String
  , _age     :: Int
  , _address :: Address
  }
  deriving (Show, Eq)

nameL :: Lens' Person String
nameL = lens _name (\p n -> p { _name = n })

ageL :: Lens' Person Int
ageL = lens _age (\p a -> p { _age = a })

addressL :: Lens' Person Address
addressL = lens _address (\p a -> p { _address = a })

cityL :: Lens' Address String
cityL = lens _city (\a c -> a { _city = c })

zipL :: Lens' Address Int
zipL = lens _zip (\a z -> a { _zip = z })

-- | 嵌套：人 → 城市（复合仍是 (.)）
personCity :: Lens' Person String
personCity = addressL . cityL

------------------------------------------------------------------------
-- 4. 类型会变的 Lens（s≠t 或 a≠b）
------------------------------------------------------------------------

_1Len :: Lens (String, c) (Int, c) String Int
_1Len = lens fst (\(_, c) n -> (n, c))

------------------------------------------------------------------------
-- 5. 换 f：Const (Sum n)
------------------------------------------------------------------------

viewAsSum :: Lens' s Int -> s -> Int
viewAsSum l s = getSum (getConst (l (\n -> Const (Sum n)) s))

------------------------------------------------------------------------
-- 示例数据
------------------------------------------------------------------------

alice :: Person
alice =
  Person
    { _name = "Alice"
    , _age = 30
    , _address = Address { _city = "Shanghai", _zip = 200000 }
    }

nestedPair :: ((Bool, Int), Char)
nestedPair = ((True, 1), 'x')

deepTriple :: (((Bool, Int), Char), String)
deepTriple = (((True, 1), 'x'), "z")

------------------------------------------------------------------------
-- main
------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "======== 1. 元组：view / set / over ========"
  print $ view _1 (True, 42 :: Int)
  print $ set  _1 False (True, 42 :: Int)
  print $ over _2 (*10) (True, 42 :: Int)

  putStrLn "======== 2. 组合 = (.)（原理见教程 §3） ========"
  -- (l . m) afb = l (m afb)
  print $ view (_1 . _1) nestedPair
  print $ set  (_1 . _2) (99 :: Int) nestedPair
  print $ over (_1 . _2) (+5) nestedPair
  -- 三层
  print $ view (_1 . _1 . _1) deepTriple
  print $ over (_1 . _1 . _2) (*10) deepTriple
  -- 分配律：view (l.m) = view m . view l
  print $ view (_1 . _2) nestedPair == view _2 (view _1 nestedPair)
  print $ over (_1 . _2) (+5) nestedPair
         == over _1 (over _2 (+5)) nestedPair
  -- 单位：id :: Lens' a a
  print $ view (id . _1) (True, 42 :: Int)
  print $ view (_1 . id) (True, 42 :: Int)
  -- rank-2：不要 let l = _1 . _1 再 view l

  putStrLn "======== 3. 记录字段 ========"
  print $ view nameL alice
  print $ view ageL alice
  print $ set  nameL "Alicia" alice
  print $ over ageL (+1) alice

  putStrLn "======== 4. 嵌套：personCity = addressL . cityL ========"
  print $ view personCity alice
  print $ set  personCity "Beijing" alice
  print $ over (addressL . zipL) (+1) alice
  print $ view (addressL . zipL) alice
         == view zipL (view addressL alice)

  putStrLn "======== 5. 类型会变：String 焦点 → Int ========"
  print $ view _1Len ("hi", True)
  print $ over _1Len length ("hi", True)

  putStrLn "======== 6. 换 f：Const (Sum Int) ========"
  print $ viewAsSum ageL alice
  print $ viewAsSum (addressL . zipL) alice

  putStrLn "======== 7. 手写展开一次 view ========"
  print $ getConst (nameL Const alice)
