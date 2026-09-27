{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

-- | 第 4 步：Tambara 模（Tambara module）——把 Strong / Choice 统一起来
--
-- 路线图位置：第 2 步学会了 Strong（积上的强度），第 3 步又加了 Choice
-- （和上的强度）。本步引入「对某个张量 ⊗ 的 Tambara 模」，一句话概括：
--
-- > Strong p  ≅  Tambara_(,) p
-- > Choice p  ≅  Tambara_Either p
--
-- 也就是说：光学里常说的「上下文强度」不是两个无关的 ad-hoc 类，
-- 而是「在选定的 monoidal tensor（张量）上，p 能把上下文平行抬过去」。
--
-- 仅依赖 base；Stack lts-21.25 / GHC 9.4.8。
module Main where

--------------------------------------------------------------------------------
-- 0. Profunctor 基座（与第 2–3 步相同）
--------------------------------------------------------------------------------

-- | Profunctor：输入反变、输出协变。
--
-- @dimap pre post p@：先用 @pre@ 把「外面的输入」改成 @p@ 要的类型，
-- 跑完后再用 @post@ 改输出。函数上就是 @post . p . pre@。
class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

instance Profunctor (->) where
  dimap f g h = g . h . f

-- | @Forget r@：只读左边，用来做 @view@。
newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  dimap f _ (Forget k) = Forget (k . f)

--------------------------------------------------------------------------------
-- 1. 什么是「张量」（monoidal tensor）？
--------------------------------------------------------------------------------

-- | 教学用：我们关心两类张量（都是 Haskell 里现成的）：
--
-- * 笛卡尔积 @(,)@：@c ⊗ a = (c, a)@（上下文总在旁边）
-- * 余积 @Either@：@c ⊗ a = Either c a@（上下文是「另一条分支」）
--
-- 严格的 monoidal category 还要单位对象 @I@、结合子 @α@、左右单位子 @λ/ρ@，
-- 以及它们与 @dimap@ 的相容性。教学里我们只把定律写在注释里，不强制证明。
--
-- 非正式定律（对积）：
--
-- * 单位：@() ⊗ a ≅ a@（左右单位）
-- * 结合：@(c ⊗ d) ⊗ a ≅ c ⊗ (d ⊗ a)@
-- * 与 @dimap@ 相容：抬上下文再 @dimap@ ≡ 在张量上 @dimap@ 再抬上下文
--
-- 对 @Either@ 同理，单位是 @Void@，结合是嵌套 @Either@ 的重结合。
--
-- 「上下文强度」α 的形状统一写成：
--
-- > α :: p a b → p (c ⊗ a) (c ⊗ b)
--
-- 焦点从 a 变到 b，上下文 c 平行带着走。

--------------------------------------------------------------------------------
-- 2. Tambara：对选定张量的上下文强度
--------------------------------------------------------------------------------

-- | Tambara 模（相对某个张量 @ten@）：
--
-- > introduce :: p a b → p (ten c a) (ten c b)
--
-- 读法：给 @p@ 一个「平行的上下文 @c@」。这就是光学里的
-- context strength（上下文强度）。
--
-- 注意：@Tambara@ 是 *相对张量参数化* 的——同一套名字，
-- 配 @(,)@ 就变成 Strong，配 @Either@ 就变成 Choice。
--
-- （范畴原文：Tambara module 是对 monoidal category 的「带强度的
--  profunctor」；光学文献里常说 optic = Tambara 上的自然变换 / coend。）
class Profunctor p => Tambara ten p where
  -- | 上下文强度：在张量 @ten c _@ 的「第二槽」上抬 @p@。
  --
  -- 对积：@introduce ≈ second'@
  -- 对和：@introduce ≈ right'@
  introduce :: p a b -> p (ten c a) (ten c b)

-- | 积张量上的「左」强度（≈ first'）：用 swap 从 introduce 推出。
-- 签名写 Strong（与 Tambara (,) 等价），避免 simplifiable-constraint 警告。
introduceFirst
  :: Strong p
  => p a b -> p (a, c) (b, c)
introduceFirst = dimap swap swap . introduce
  where
    swap (x, y) = (y, x)

-- | 和张量上的「左」强度（≈ left'）。
introduceLeft
  :: Choice p
  => p a b -> p (Either a c) (Either b c)
introduceLeft = dimap mirror mirror . introduce
  where
    mirror (Left x)  = Right x
    mirror (Right y) = Left y

--------------------------------------------------------------------------------
-- 3. Strong ≅ Tambara_(,) ； Choice ≅ Tambara_Either
--------------------------------------------------------------------------------

-- | 经典 Strong——积上的强度（与第 2 步相同）。
class Profunctor p => Strong p where
  first'  :: p a b -> p (a, c) (b, c)
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'
    where
      swap (x, y) = (y, x)

-- | 经典 Choice——和上的强度。
class Profunctor p => Choice p where
  left'  :: p a b -> p (Either a c) (Either b c)
  right' :: p a b -> p (Either c a) (Either c b)
  right' = dimap mirror mirror . left'
    where
      mirror (Left x)  = Right x
      mirror (Right y) = Left y

-- | 方向 Strong ⇒ Tambara_(,)：@second'@ 就是 introduce。
instance Strong p => Tambara (,) p where
  introduce = second'

-- | 方向 Choice ⇒ Tambara_Either：@right'@ 就是 introduce。
instance Choice p => Tambara Either p where
  introduce = right'

-- | 反向直觉（写在注释 + newtype 演示）：
--
-- 若你有 @Tambara (,) p@，则可定义
--
-- > second' = introduce
-- > first'  = dimap swap swap . introduce
--
-- 从而恢复 Strong。Choice 同理（right' = introduce）。
-- 下面用包装类型展示「Strong/Choice 实例可以透传」。

newtype ViaProduct p a b = ViaProduct { getViaProduct :: p a b }

instance Profunctor p => Profunctor (ViaProduct p) where
  dimap f g (ViaProduct p) = ViaProduct (dimap f g p)

instance Strong p => Strong (ViaProduct p) where
  first'  (ViaProduct p) = ViaProduct (first' p)
  second' (ViaProduct p) = ViaProduct (second' p)

newtype ViaSum p a b = ViaSum { getViaSum :: p a b }

instance Profunctor p => Profunctor (ViaSum p) where
  dimap f g (ViaSum p) = ViaSum (dimap f g p)

instance Choice p => Choice (ViaSum p) where
  left'  (ViaSum p) = ViaSum (left' p)
  right' (ViaSum p) = ViaSum (right' p)

--------------------------------------------------------------------------------
-- 4. 具体实例：函数与 Forget
--------------------------------------------------------------------------------

instance Strong (->) where
  first'  f (a, c) = (f a, c)
  second' f (c, a) = (c, f a)

instance Choice (->) where
  left'  f (Left a)  = Left (f a)
  left'  _ (Right c) = Right c
  right' f (Right a) = Right (f a)
  right' _ (Left c)  = Left c

-- Forget 对积是 Strong（只读焦点）；对和需要「失败默认」，见第 3 步 ForgetM。
instance Strong (Forget r) where
  first'  (Forget k) = Forget (\(a, _) -> k a)
  second' (Forget k) = Forget (\(_, a) -> k a)

--------------------------------------------------------------------------------
-- 5. 用 Tambara 语言拼 Lens / Prism（对照第 2–3 步）
--------------------------------------------------------------------------------

type Lens s t a b = forall p. Strong p => p a b -> p s t

-- | get/set → Lens；here @introduceFirst@ ≡ @first'@（Tambara 视角）。
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . introduceFirst

type Prism s t a b = forall p. Choice p => p a b -> p s t

-- | match/build → Prism；here @introduce@ ≡ @right'@（Tambara_Either）。
prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism build match =
  dimap match (either id build) . introduce

view :: Lens s t a b -> s -> a
view l = runForget (l (Forget id))

overL :: Lens s t a b -> (a -> b) -> s -> t
overL l f = l f

overP :: Prism s t a b -> (a -> b) -> s -> t
overP p f = p f

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just match
  where
    match (Just a) = Right a
    match Nothing  = Left Nothing

_Left :: Prism (Either a c) (Either b c) a b
_Left = prism Left match
  where
    match (Left a)  = Right a
    match (Right c) = Left (Right c)

--------------------------------------------------------------------------------
-- Demo
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "== Tambara slogan =="
  putStrLn "Strong p  ≅  Tambara_(,) p     (tensor = product)"
  putStrLn "Choice p  ≅  Tambara_Either p  (tensor = sum)"
  putStrLn "introduce ≈ second' / right'   (context strength α)"

  putStrLn "== product Tambara (= Strong) via Lens _1 =="
  print $ view _1 (True, 42 :: Int)
  print $ overL _1 not (True, 42 :: Int)
  print $ (introduce not :: (Int, Bool) -> (Int, Bool)) (0, True)
  print $ (introduceFirst not :: (Bool, Int) -> (Bool, Int)) (True, 0)

  putStrLn "== sum Tambara (= Choice) via Prism =="
  print $ overP _Just (++ "!") (Just "hi" :: Maybe String)
  print $ overP _Just (++ "!") (Nothing :: Maybe String)
  print $ overP _Left (*10) (Left (3 :: Int) :: Either Int String)
  print $ overP _Left (*10) (Right "x" :: Either Int String)
  print $ (introduce not :: Either Int Bool -> Either Int Bool) (Right True)
  print $ (introduceLeft not :: Either Bool Int -> Either Bool Int) (Left True)

  putStrLn "== ViaProduct / ViaSum wrappers still act =="
  print $ getViaProduct (first' (ViaProduct not)) (True, 1 :: Int)
  print $ getViaSum (left' (ViaSum not)) (Left True :: Either Bool Int)
