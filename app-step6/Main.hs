{-# LANGUAGE RankNTypes #-}

-- | 第 6 步：与主流库的类型对照（仍仅 base，不引入 lens / profunctor）
--
-- 目标：看清我们手写的名字，在 lens、profunctor-optics、optics 里分别叫什么；
-- 并给一个「只要 Profunctor」的 Iso 微例。下一步该读什么写在注释末尾，
-- 亦可对照 docs/概念对照表.md、docs/原理详解.md。
module Main where

--------------------------------------------------------------------------------
-- 精简基座（与前几步一致）
--------------------------------------------------------------------------------

class Profunctor p where
  dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

instance Profunctor (->) where
  dimap f g h = g . h . f

class Profunctor p => Strong p where
  first'  :: p a b -> p (a, c) (b, c)
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'
    where
      swap (x, y) = (y, x)

instance Strong (->) where
  first'  f (a, c) = (f a, c)
  second' f (c, a) = (c, f a)

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
-- 我们的类型（教学版）
--------------------------------------------------------------------------------

-- | Iso：只要 Profunctor——整树可逆重写，不需要额外上下文强度。
--
-- 约束越少 ⇒ optic *越难造*、但 *用途越广*：一个 Iso 值的类型是
-- @forall p. Profunctor p => …@，可以实例化到带 Strong 的 @p@，
-- 因此 Iso 能当 Lens 用（真实库里也是如此）。
type Iso s t a b = forall p. Profunctor p => p a b -> p s t

type Lens s t a b = forall p. Strong p => p a b -> p s t
type Prism s t a b = forall p. Choice p => p a b -> p s t
type Affine s t a b = forall p. (Strong p, Choice p) => p a b -> p s t

-- Traversal 需要 Traversing / Wander（遍历强度），此处仅占位：
-- type Traversal s t a b = forall p. Traversing p => p a b -> p s t

-- | 从一对互逆函数造 Iso。
iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso sa bt = dimap sa bt

-- | 交换二元组：经典 Iso。
swapped :: Iso (a, b) (c, d) (b, a) (d, c)
swapped = iso swap swap
  where
    swap (x, y) = (y, x)

-- | @Maybe@ ↔ @Either ()@（另一常见 Iso）。
maybeEither :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
maybeEither = iso f g
  where
    f Nothing  = Left ()
    f (Just x) = Right x
    g (Left ()) = Nothing
    g (Right x) = Just x

overI :: Iso s t a b -> (a -> b) -> s -> t
overI i f = i f

--------------------------------------------------------------------------------
-- 打印对照表
--------------------------------------------------------------------------------

printTable :: IO ()
printTable = do
  putStrLn "========================================================================"
  putStrLn "  constraint (ours)     optic        tensor hint     library names"
  putStrLn "------------------------------------------------------------------------"
  putStrLn "  Profunctor            Iso          (none / ≅)      Iso"
  putStrLn "  Strong / Tambara_(,)  Lens         product (,)     Lens"
  putStrLn "  Choice / Tambara_+    Prism        sum Either      Prism"
  putStrLn "  Strong+Choice         Affine       optional        AffineTraversal /"
  putStrLn "                                                     Optional / Affine"
  putStrLn "  Traversing / Wander   Traversal    traversable     Traversal"
  putStrLn "========================================================================"
  putStrLn ""
  putStrLn "Package map (conceptual; we stay base-only):"
  putStrLn "  * lens              — van Laarhoven + profunctor optics"
  putStrLn "  * profunctors       — Profunctor, Strong, Choice, ..."
  putStrLn "  * profunctor-optics — optics as Tambara morphisms"
  putStrLn "  * optics            — concrete Optic newtype; same hierarchy"
  putStrLn ""
  putStrLn "Our encoding:"
  putStrLn "  type Lens  s t a b = forall p. Strong      p => p a b -> p s t"
  putStrLn "  type Prism s t a b = forall p. Choice      p => p a b -> p s t"
  putStrLn "  type Iso   s t a b = forall p. Profunctor  p => p a b -> p s t"
  putStrLn ""
  putStrLn "What to read next:"
  putStrLn "  1. docs/原理详解.md"
  putStrLn "  2. docs/概念对照表.md"
  putStrLn "  3. Pickering–Gibbons–Wu: Profunctor Optics"
  putStrLn "  4. Milewski: Profunctor Optics / Tambara modules"
  putStrLn "  5. Hackage: lens, optics, profunctors"

-- 阅读顺序建议（给读源码的人）：
-- 1. 本仓库 app/ → app-step6 + docs/原理详解.md
-- 2. lens 文档里的 Optic 层级图
-- 3. "Profunctor Optics: Modular Data Accessors" (Pickering et al.)
-- 4. Bartosz Milewski 关于 Tambara modules 的文章
-- 5. 动手：lens 的 Lens'/Prism'，再对照 optics 包
--
-- 刻意不依赖这些包，是为了强制看清约束本身，而不是 API 糖。

main :: IO ()
main = do
  printTable

  putStrLn "== tiny Iso: swapped =="
  print $ overI swapped id ("L", "R" :: String)
  print $ overI swapped (\(x, y) -> (reverse y, x ++ "!")) ("ab", "cd" :: String)

  putStrLn "== tiny Iso: maybeEither =="
  print $ overI maybeEither id (Just "x" :: Maybe String)
  print $ overI maybeEither id (Nothing :: Maybe String)
  print $ overI maybeEither (either (const (Right "z")) Right) Nothing
