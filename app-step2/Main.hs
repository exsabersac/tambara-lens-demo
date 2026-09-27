{-# LANGUAGE RankNTypes #-}

-- | 第 2 步：Profunctor + Strong 编码的 Lens（仅 base）
--
-- 承接第 1 步的 get/set 语义，把 Lens 写成：
--
-- > type Lens s t a b = forall p. Strong p => p a b -> p s t
--
-- 读法：一个 Lens 是「对任意 Strong 的 profunctor，都能把
-- @p a b@（焦点上的变换）抬成 @p s t@（整棵结构上的变换）」。
--
-- 后面接到 Tambara：Strong 恰是笛卡尔积 @(,)@ 上的 Tambara 模。
-- 组合原理：docs/Strong-Profunctor组合.md
module Main where

--------------------------------------------------------------------------------
-- 1. Profunctor / Strong
--------------------------------------------------------------------------------

-- | Profunctor：对输入反变、对输出协变。
--
-- @dimap pre post@：先用 @pre@ 把外面的输入改成里面要的类型，
-- 跑完 @p@ 后再用 @post@ 改输出。
--
-- 对函数 @(->)@：@dimap f g h = g . h . f@。
class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

-- | Strong：对笛卡尔积 @(,)@ 的「上下文强度」。
--
-- 范畴说法（光学语境）：这是 ⊗ = 积 时的 Tambara 模条件。
-- @first'@ 把焦点上的 @p a b@ 抬到「焦点 × 上下文」上，上下文原样通过。
--
-- 默认 @second'@ 由 @first'@ + 交换积得到。
class Profunctor p => Strong p where
  first'  :: p a b -> p (a, c) (b, c)
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'
    where
      swap (x, y) = (y, x)

-- | 函数本身是 Profunctor / Strong：这是 @over@ / @set@ 的载体。
instance Profunctor (->) where
  dimap f g h = g . h . f

instance Strong (->) where
  first'  f (a, c) = (f a, c)
  second' f (c, a) = (c, f a)

-- | @Forget r@：只关心「从左边读出 @r@」，忽略右边类型参数。
--
-- 用来实现 @view@：把 Lens 作用在 @Forget id :: Forget a a b@ 上，
-- 得到 @Forget a s t@，即 @s -> a@。
newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  -- 只改输入；输出侧的 @b@ 本就不存在于表示里
  dimap f _ (Forget k) = Forget (k . f)

instance Strong (Forget r) where
  -- 积上只读焦点分量
  first'  (Forget k) = Forget (\(a, _) -> k a)
  second' (Forget k) = Forget (\(_, a) -> k a)

--------------------------------------------------------------------------------
-- 2. 两种编码：经典 get/set 与 Strong optic
--------------------------------------------------------------------------------

-- | 第 1 步同款：一对 get / set（此处仅作对照，演示 round-trip 思路）。
data LensGS s t a b = LensGS
  { gsView :: s -> a
  , gsSet  :: s -> b -> t
  }

-- | Profunctor optic 形式的 Lens。
--
-- @forall p. Strong p =>@ 是关键：同一个 optic 必须对 *所有*
-- Strong 实例都成立，不能只对 @(->)@ 成立。
-- 因此它携带的信息恰好相当于「可拆成焦点 + 上下文」的 get/set。
type Lens s t a b = forall p. Strong p => p a b -> p s t

-- | 同型缩写。
type Lens' s a = Lens s s a a

-- | 核心拼法：从 get/set 造出 Strong optic。
--
-- 三步（从右往左读管道）：
--
-- 1. @first'@：@p a b -> p (a, s) (b, s)@
--    把「只改焦点」抬到「焦点 × 把整棵 @s@ 当上下文」。
-- 2. 左边的 @dimap@ 前置：@s ↦ (get s, s)@
--    拆出焦点，并保留整棵结构当上下文（以便 set 时用）。
-- 3. 左边的 @dimap@ 后置：@(b, s) ↦ setP s b@
--    用新焦点和旧整树写出新整树。
--
-- 合在一起：
--
-- > lens get setP = dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'

--------------------------------------------------------------------------------
-- 3. 从 optic 取出运算：换不同的 Strong 实例
--------------------------------------------------------------------------------

-- | 用 @(->)@：焦点上的函数变成结构上的函数。
over :: Lens s t a b -> (a -> b) -> s -> t
over l f = l f

-- | @set = over (const b)@。
set :: Lens s t a b -> b -> s -> t
set l b = over l (const b)

-- | 用 @Forget@：只读焦点。
view :: Lens s t a b -> s -> a
view l = runForget (l (Forget id))

--------------------------------------------------------------------------------
-- 4. 例子：积投影、嵌套、复合
--------------------------------------------------------------------------------

-- | 第一分量。对 @(->)@ 而言，@first'@ 本身就是 @_1@。
_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))

_2 :: Lens (c, a) (c, b) a b
_2 = lens snd (\(c, _) b -> (c, b))

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

_city :: Lens' Address String
_city = lens city (\addr c -> addr { city = c })

_address :: Lens' Person Address
_address = lens address (\p a -> p { address = a })

-- | Optic 复合 = 函数复合（都是 @p _ _ -> p _ _@）。
--
-- 与第 1 步手写 @compose@ 同语义，但这里类型已强制「对任意 Strong p」。
_cityOf :: Lens' Person String
_cityOf = _address . _city

alice :: Person
alice = Person "Alice" (Address "Shanghai" "200000")

nestedPair :: ((Bool, Int), Char)
nestedPair = ((True, 1), 'x')

deepTriple :: (((Bool, Int), Char), String)
deepTriple = (((True, 1), 'x'), "z")

main :: IO ()
main = do
  putStrLn "== (->) via over / set / view =="
  print $ view _1 (True, 42 :: Int)
  print $ set  _1 False (True, 42 :: Int)
  print $ over _2 (*10) (True, 42 :: Int)

  putStrLn "== compose = (.) （详解见 docs/Strong-Profunctor组合.md） =="
  -- (l . m) p = l (m p)
  print $ view (_1 . _1) nestedPair
  print $ set  (_1 . _2) (99 :: Int) nestedPair
  print $ over (_1 . _2) (+5) nestedPair
  print $ view (_1 . _1 . _1) deepTriple
  print $ over (_1 . _1 . _2) (*10) deepTriple
  -- 分配律
  print $ view (_1 . _2) nestedPair == view _2 (view _1 nestedPair)
  print $ over (_1 . _2) (+5) nestedPair
         == over _1 (over _2 (+5)) nestedPair
  print $ view (id . _1) (True, 42 :: Int)
  print $ view (_1 . id) (True, 42 :: Int)

  putStrLn "== nested record: _address . _city =="
  print $ view _cityOf alice
  print $ set  _cityOf "Beijing" alice
  print $ over _cityOf (++ "!") alice
  print $ view _cityOf alice == view _city (view _address alice)

  putStrLn "== first' is _1 on (->) =="
  print $ (first' not :: (Bool, Int) -> (Bool, Int)) (True, 1)

  putStrLn "== round-trip: optic from get/set still views =="
  -- Lens 是 rank-2：不要先 let 绑成单态再传给 view，否则会卡在某个 p0。
  print $ view (lens fst (\(_, c) b -> (b, c))) ("hi", 9 :: Int)
