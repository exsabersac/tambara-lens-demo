{-# LANGUAGE NamedFieldPuns #-}

-- | 第 1 步：经典 get/set Lens（仅 base；Stack lts-21.25 / GHC 9.4.8）
--
-- 目标：先把「从结构里取焦点 / 写回焦点」说清楚，并核对三条定律。
-- 后面第 2 步会把同一语义改写成 Strong 下的 profunctor optic。
module Main where

--------------------------------------------------------------------------------
-- 经典 Lens：一对函数
--------------------------------------------------------------------------------

-- | 异构（polymorphic）Lens：
--
-- * @s@：改之前的整棵结构
-- * @t@：改之后的整棵结构（焦点类型变了时，@s@ 与 @t@ 可以不同）
-- * @a@：改之前的焦点
-- * @b@：改之后的焦点
--
-- 同型情形常用 'Lens''：@Lens s s a a@。
data Lens s t a b = Lens
  { view :: s -> a
    -- ^ 取出焦点。不修改结构。
  , set  :: s -> b -> t
    -- ^ 用新焦点 @b@ 写回，得到整棵新结构 @t@。
    --   注意参数顺序：先整棵 @s@，再新焦点（与 lens 库的 @set l b s@ 不同，
    --   这里是「数据优先」的教学写法）。
  }

-- | 同型 Lens：焦点类型不变时的缩写。
type Lens' s a = Lens s s a a

--------------------------------------------------------------------------------
-- 积上的投影：最标准的 Lens 例子
--------------------------------------------------------------------------------

-- | 对 @(a, c)@ 的第一分量。
--
-- 直观：焦点是左边；右边 @c@ 是「上下文」，改焦点时保持不动。
_1 :: Lens (a, c) (b, c) a b
_1 = Lens
  { view = fst
  , set  = \(_, c) b -> (b, c)
  }

-- | 对 @(c, a)@ 的第二分量。
_2 :: Lens (c, a) (c, b) a b
_2 = Lens
  { view = snd
  , set  = \(c, _) b -> (c, b)
  }

--------------------------------------------------------------------------------
-- 嵌套记录：真实代码里更常见的形状
--------------------------------------------------------------------------------

data Address = Address
  { city    :: String
  , zipCode :: String
  }
  deriving (Show, Eq)

data Person = Person
  { name    :: String
  , address :: Address
  }
  deriving (Show, Eq)

-- | @Address@ 上的 @city@ 字段。
_city :: Lens' Address String
_city = Lens
  { view = city
  , set  = \addr c -> addr { city = c }
  }

-- | @Person@ 上的 @address@ 字段。
_addr :: Lens' Person Address
_addr = Lens
  { view = address
  , set  = \p a -> p { address = a }
  }

--------------------------------------------------------------------------------
-- 复合：先整段，再焦点（手写版；第 2 步会变成函数复合）
--------------------------------------------------------------------------------

-- | 复合两个同型 Lens。
--
-- * 取：@v2 . v1@（先从 @s@ 到中间 @a@，再从 @a@ 到焦点 @b@）
-- * 写：先用内层 @s2@ 改中间结构，再用外层 @s1@ 写回整棵 @s@
--
-- 这就是「路径」：@Person → Address → city@。
compose :: Lens' s a -> Lens' a b -> Lens' s b
compose (Lens v1 s1) (Lens v2 s2) = Lens
  { view = v2 . v1
  , set  = \s b -> s1 s (s2 (v1 s) b)
  }

-- | @Person@ 上城市字段的复合 Lens。
_cityOf :: Lens' Person String
_cityOf = compose _addr _city

--------------------------------------------------------------------------------
-- 三条定律（应在合法 Lens 上成立）
--------------------------------------------------------------------------------

-- | 设进去再取：得到刚设的值。
law1 :: (Eq a) => Lens' s a -> s -> a -> Bool
law1 l s a = view l (set l s a) == a

-- | 取出来再设回去：结构不变。
law2 :: (Eq s) => Lens' s a -> s -> Bool
law2 l s = set l s (view l s) == s

-- | 后设覆盖先设。
law3 :: (Eq s) => Lens' s a -> s -> a -> a -> Bool
law3 l s b b' = set l (set l s b) b' == set l s b'

--------------------------------------------------------------------------------
-- Demo
--------------------------------------------------------------------------------

alice :: Person
alice = Person "Alice" (Address "Shanghai" "200000")

main :: IO ()
main = do
  putStrLn "== product lenses =="
  print $ view _1 (True, 42 :: Int)           -- True
  print $ set  _1 (True, 42 :: Int) False     -- (False,42)
  print $ view _2 (True, 42 :: Int)           -- 42

  putStrLn "== nested =="
  print $ view _cityOf alice
  print $ set  _cityOf alice "Beijing"

  putStrLn "== laws on _cityOf / alice =="
  print $ law1 _cityOf alice "Hangzhou"
  print $ law2 _cityOf alice
  print $ law3 _cityOf alice "A" "B"
