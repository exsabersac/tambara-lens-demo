{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

-- | 第 3 步：常见 optics 对照（Strong / Choice / …）
--
-- 路线图位置：在 Lens=Strong 之后，用一张「约束 ↔ optic」表把
-- Prism、Traversal、Iso、Affine 摆齐；为第 4–5 步 Tambara / ∀Tambara 做钩子。
--
-- 对照表（记忆用）：
--
-- @
--   约束组合              optic          直觉
--   --------------------  -------------  --------------------------
--   Strong                Lens           积上的焦点（总有）
--   Choice                Prism          和上的焦点（可能没有）
--   Strong + Choice       Affine         至多一个焦点（可选积）
--   （遍历强度 / Wander）  Traversal      零或多个焦点
--   （无额外强度）        Iso            可逆整树重写
-- @
--
-- 本文件用 base 手写 Strong / Choice，跑通 Lens 与 Prism；
-- Traversal / Iso 只给类型形状与短注释，完整 Wander 留到后续。
module Main where

--------------------------------------------------------------------------------
-- Profunctor 基座
--------------------------------------------------------------------------------

class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

instance Profunctor (->) where
  dimap f g h = g . h . f

-- | 积上的 Tambara（→ Lens）
class Profunctor p => Strong p where
  first'  :: p a b -> p (a, c) (b, c)
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'
    where
      swap (x, y) = (y, x)

instance Strong (->) where
  first'  f (a, c) = (f a, c)
  second' f (c, a) = (c, f a)

-- | 和上的 Tambara（→ Prism）
--
-- @left'@：@p a b → p (Either a c) (Either b c)@
-- 只在 @Left@ 分支改焦点；@Right@ 原样通过（「匹配失败」）。
class Profunctor p => Choice p where
  left'  :: p a b -> p (Either a c) (Either b c)
  right' :: p a b -> p (Either c a) (Either c b)
  right' = dimap mirror mirror . left'
    where
      mirror (Left x)  = Right x
      mirror (Right y) = Left y

instance Choice (->) where
  left'  f (Left a)  = Left (f a)
  left'  _ (Right c) = Right c
  right' f (Right a) = Right (f a)
  right' _ (Left c)  = Left c

--------------------------------------------------------------------------------
-- Forget：只读（view / preview）
--------------------------------------------------------------------------------

newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  dimap f _ (Forget k) = Forget (k . f)

instance Strong (Forget r) where
  first'  (Forget k) = Forget (\(a, _) -> k a)
  second' (Forget k) = Forget (\(_, a) -> k a)

-- Choice 需要「失败时有默认」：用 Monoid 攒 Maybe 风格时常用 First；
-- 这里 preview 改用专门的 ForgetM（见下），避免强行给 Forget 上 Choice。

-- | 只读「可能没有焦点」：@a -> Maybe r@
newtype ForgetM r a b = ForgetM { runForgetM :: a -> Maybe r }

instance Profunctor (ForgetM r) where
  dimap f _ (ForgetM k) = ForgetM (k . f)

instance Choice (ForgetM r) where
  left'  (ForgetM k) = ForgetM $ \case
    Left a  -> k a
    Right _ -> Nothing
  right' (ForgetM k) = ForgetM $ \case
    Right a -> k a
    Left _  -> Nothing

--------------------------------------------------------------------------------
-- Optic 类型（约束决定种类）
--------------------------------------------------------------------------------

-- | Lens：任意 Strong
type Lens s t a b = forall p. Strong p => p a b -> p s t
type Lens' s a = Lens s s a a

-- | Prism：任意 Choice
type Prism s t a b = forall p. Choice p => p a b -> p s t
type Prism' s a = Prism s s a a

-- | Affine（可选一个焦点）：Strong + Choice
-- 亦称 AffineTraversal / Optional
type Affine s t a b = forall p. (Strong p, Choice p) => p a b -> p s t

-- | Iso：只要 Profunctor（可逆的 dimap）
type Iso s t a b = forall p. Profunctor p => p a b -> p s t

-- | Traversal：需要「遍历强度」Wander / Traversing（此处仅占位说明）
-- type Traversal s t a b = forall p. Traversing p => p a b -> p s t
-- 直觉：零或多个焦点；用 @traverse@ 类强度抬变换。

--------------------------------------------------------------------------------
-- 构造：Lens / Prism
--------------------------------------------------------------------------------

-- | 与第 2 步相同：get/set → Lens
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'

-- | Prism：匹配 / 构造
--
-- * @build :: b -> t@：总是能从焦点造出整树（注入）
-- * @match :: s -> Either t a@：要么得到焦点 @a@，要么得到「改不动」的 @t@
--
-- 拼法：@dimap match (either id build) . right'@
-- （把 @s@ 看成 @Either t a@，只在 Right=焦点 上作用）
prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism build match =
  dimap match (either id build) . right'

--------------------------------------------------------------------------------
-- 运算
--------------------------------------------------------------------------------

overL :: Lens s t a b -> (a -> b) -> s -> t
overL l f = l f

view :: Lens s t a b -> s -> a
view l = runForget (l (Forget id))

-- | Prism 上的「预览」：有焦点则 Just
preview :: Prism s t a b -> s -> Maybe a
preview p = runForgetM (p (ForgetM Just))

-- | 用 @(->)@：有焦点则改，无焦点则原样（Prism 的 over）
overP :: Prism s t a b -> (a -> b) -> s -> t
overP p f = p f

-- | review 就是构造端 @build@（不经过 optic 量化）；
-- 例如 @_Just@ 的 build 是 @Just@，@_Left@ 的 build 是 @Left@。

--------------------------------------------------------------------------------
-- 例子
--------------------------------------------------------------------------------

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))

-- | @_Just@：@Maybe a@ 上的 Prism（有值才改）
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just $ \case
  Just a  -> Right a
  Nothing -> Left Nothing

-- | @_Left@：@Either@ 左分支
_Left :: Prism (Either a c) (Either b c) a b
_Left = prism Left $ \case
  Left a  -> Right a
  Right c -> Left (Right c)

-- | @_Right@
_Right :: Prism (Either c a) (Either c b) a b
_Right = prism Right $ \case
  Right a -> Right a
  Left c  -> Left (Left c)

main :: IO ()
main = do
  putStrLn "== table reminder =="
  putStrLn "Strong          -> Lens"
  putStrLn "Choice          -> Prism"
  putStrLn "Strong+Choice   -> Affine"
  putStrLn "Traversing      -> Traversal (later)"
  putStrLn "Profunctor only -> Iso"

  putStrLn "== Lens _1 =="
  print $ view _1 (True, 42 :: Int)
  print $ overL _1 not (True, 42 :: Int)

  putStrLn "== Prism _Just =="
  print $ preview _Just (Just "hi" :: Maybe String)
  print $ preview _Just (Nothing :: Maybe String)
  print $ overP _Just (++ "!") (Just "hi")
  print $ overP _Just (++ "!") (Nothing :: Maybe String)

  putStrLn "== Prism _Left / _Right =="
  print $ preview _Left  (Left  1 :: Either Int String)
  print $ preview _Left  (Right "x" :: Either Int String)
  print $ preview _Right (Right "x" :: Either Int String)
  print $ overP _Right (++ "!") (Right "x" :: Either Int String)
