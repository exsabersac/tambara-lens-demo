{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

-- | 第 5 步：Optic 作为 Tambara 态射（existential / coend ↔ ∀ Tambara）
--
-- 核心等式（笛卡尔积张量上的 Lens）：
--
-- @
--   Optic_(,) s t a b
--     ≅  ∃ c.  (s → (c, a)) × ((c, b) → t)     -- existential / coend 形
--     ≅  ∀ p. Tambara_(,) p ⇒ p a b → p s t     -- van Laarhoven / profunctor 形
--     ≅  (s → a) × (s → b → t)                  -- 经典 get/set（c 取成 s）
-- @
--
-- 对和张量 @Either@，把 @(c, –)@ 换成 @Either c –@，就得到 Prism。
--
-- 本文件实现积上 Lens 的双向变换，并对 Prism 给出对称草图 + round-trip。
-- 仅 base；详见 docs/原理详解.md。
module Main where

--------------------------------------------------------------------------------
-- Profunctor / Strong / Choice / Tambara（精简复述）
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

newtype Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
  dimap f _ (Forget k) = Forget (k . f)

instance Strong (Forget r) where
  first'  (Forget k) = Forget (\(a, _) -> k a)
  second' (Forget k) = Forget (\(_, a) -> k a)

--------------------------------------------------------------------------------
-- 1. 三种编码：经典 / existential / ∀ Strong
--------------------------------------------------------------------------------

-- | 经典 get/set（第 1 步）。
data LensGS s t a b = LensGS
  { gsView :: s -> a
  , gsSet  :: s -> b -> t
  }

-- | Existential / coend 形（积张量）：
--
-- @∃ c. (s → (c, a)) × ((c, b) → t)@
--
-- 读法：把整树 @s@ 拆成「上下文 @c@ + 焦点 @a@」；
-- 改完焦点得到 @b@ 后再用上下文装回 @t@。
--
-- （范畴说法：这是 coend ∫^c … 的一个具体代表元；教学里用 ∃ 即可。）
data ExLens s t a b = forall c. ExLens
  { exOut :: s -> (c, a)   -- ^ 拆：s ↦ (context, focus)
  , exIn  :: (c, b) -> t   -- ^ 装： (context, newFocus) ↦ t
  }

-- | Profunctor optic 形（∀ Strong ≅ ∀ Tambara_(,)）。
type Lens s t a b = forall p. Strong p => p a b -> p s t

--------------------------------------------------------------------------------
-- 2. 双向：经典 ↔ existential ↔ ∀ Strong
--------------------------------------------------------------------------------

-- | 经典 → existential：上下文直接取整棵 @s@。
--
-- @out s = (s, get s)@，@in (s, b) = set s b@。
-- 这是「最朴素」的代表元（c := s）。
gsToEx :: LensGS s t a b -> ExLens s t a b
gsToEx (LensGS get setP) = ExLens
  { exOut = \s -> (s, get s)
  , exIn  = \(s, b) -> setP s b
  }

-- | existential → 经典：view = snd ∘ out；set 用 out 取出 c 再 in。
exToGs :: ExLens s t a b -> LensGS s t a b
exToGs (ExLens out inn) = LensGS
  { gsView = snd . out
  , gsSet  = \s b -> inn (fst (out s), b)
  }

-- | existential → ∀ Strong：
--
-- @dimap out inn . second'@
-- （out 拆成 (c,a)：上下文在左、焦点在右；故用 second' 只改 a。）
--
-- 这与第 2 步 @lens get setP@ 同构（那边用 first' 是因为写成了 (a,s)），
-- 只是上下文类型更一般（任意 c，不强制 c = s）。
exToOptic :: ExLens s t a b -> Lens s t a b
exToOptic (ExLens out inn) =
  dimap out inn . second'

-- | ∀ Strong → 经典：分别用 Forget 与 (->) 实例取出 get / set。
--
-- 注意：不能先 @let l0 = l@ 再传给多个运算——rank-2 会被单态化。
-- 正确做法：每次直接把 polymorphic 的 @l@ 传进去（或用本函数一次抽出）。
opticToGs :: Lens s t a b -> LensGS s t a b
opticToGs l = LensGS
  { gsView = runForget (l (Forget id))
  , gsSet  = \s b -> l (const b) s   -- (->) 实例：set = over (const b)
  }

-- | 经典 → ∀ Strong（第 2 步同款，作为对照）。
gsToOptic :: LensGS s t a b -> Lens s t a b
gsToOptic (LensGS get setP) =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'

-- 组合路径（注释里的对拍）：
--   gs  --gsToEx-->  ex  --exToOptic-->  optic
--   gs  <--exToGs--  ex
--   gs  <--opticToGs-- optic
--   gs  --gsToOptic--> optic

--------------------------------------------------------------------------------
-- 3. Prism 草图：existential ↔ ∀ Choice
--------------------------------------------------------------------------------

-- | Existential 形（和张量）：
--
-- @∃ c. (s → Either c a) × (Either c b → t)@
--
-- * @Left c@：匹配失败，上下文是「改不动的那一侧」
-- * @Right a@：匹配成功，得到焦点
data ExPrism s t a b = forall c. ExPrism
  { exMatch :: s -> Either c a
  , exBuild :: Either c b -> t
  }

type Prism s t a b = forall p. Choice p => p a b -> p s t

-- | 经典 match/build → existential（c 取成 t：失败时直接产出最终 t）。
--
-- @match :: s → Either t a@，@build :: b → t@。
mbToEx :: (s -> Either t a) -> (b -> t) -> ExPrism s t a b
mbToEx match build = ExPrism
  { exMatch = match
  , exBuild = either id build
  }

-- | existential → ∀ Choice：@dimap match buildE . right'@
exToPrism :: ExPrism s t a b -> Prism s t a b
exToPrism (ExPrism match buildE) =
  dimap match buildE . right'

-- | ∀ Choice → 用 (->) 做 over；preview 需要 ForgetM，这里只做 over round-trip。
overP :: Prism s t a b -> (a -> b) -> s -> t
overP p f = p f

--------------------------------------------------------------------------------
-- 4. 例子与 round-trip
--------------------------------------------------------------------------------

_1gs :: LensGS (a, c) (b, c) a b
_1gs = LensGS fst (\(_, c) b -> (b, c))

-- 经 existential 再回到 optic
_1 :: Lens (a, c) (b, c) a b
_1 = exToOptic (gsToEx _1gs)

-- 直接经典 → optic
_1' :: Lens (a, c) (b, c) a b
_1' = gsToOptic _1gs

_JustEx :: ExPrism (Maybe a) (Maybe b) a b
_JustEx = mbToEx match Just
  where
    match (Just a) = Right a
    match Nothing  = Left Nothing

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = exToPrism _JustEx

view :: Lens s t a b -> s -> a
view l = runForget (l (Forget id))

overL :: Lens s t a b -> (a -> b) -> s -> t
overL l f = l f

-- | round-trip 检查：经典 → ex → 经典
rtGsEx :: (Eq a, Eq t) => LensGS s t a b -> s -> b -> Bool
rtGsEx gs s b =
  let gs' = exToGs (gsToEx gs)
  in gsView gs' s == gsView gs s
     && gsSet gs' s b == gsSet gs s b

-- | round-trip：经典 → optic → 经典
rtGsOptic :: (Eq a, Eq t) => LensGS s t a b -> s -> b -> Bool
rtGsOptic gs s b =
  let gs' = opticToGs (gsToOptic gs)
  in gsView gs' s == gsView gs s
     && gsSet gs' s b == gsSet gs s b

-- | round-trip：经典 → ex → optic → 经典
rtFull :: (Eq a, Eq t) => LensGS s t a b -> s -> b -> Bool
rtFull gs s b =
  let gs' = opticToGs (exToOptic (gsToEx gs))
  in gsView gs' s == gsView gs s
     && gsSet gs' s b == gsSet gs s b

-- | 展示 existential 代表元的拆装直觉。
-- 因 @c@ 被 ∃ 藏住，不能在外部给 @out@ 的结果写死类型；
-- 这里用「已知 c = 整树」的手写代表元（与 gsToEx 同构）直接打印。
demoExConcrete :: IO ()
demoExConcrete = do
  let out :: (Bool, Int) -> ((Bool, Int), Bool)
      out s = (s, fst s)   -- context = whole pair, focus = first
      inn :: ((Bool, Int), Bool) -> (Bool, Int)
      inn (s, b) = (b, snd s)
  print $ out (True, 42)
  print $ inn ((True, 42), False)

main :: IO ()
main = do
  putStrLn "== three encodings (product / Lens) =="
  putStrLn "LensGS  ↔  ExLens (∃c)  ↔  forall Strong p. p a b -> p s t"

  putStrLn "== _1 via existential path =="
  print $ view _1 (True, 42 :: Int)
  print $ overL _1 not (True, 42 :: Int)
  print $ view _1' ("hi", 9 :: Int)

  putStrLn "== round-trips on _1gs =="
  print $ rtGsEx    _1gs (True, 42 :: Int) False
  print $ rtGsOptic _1gs (True, 42 :: Int) False
  print $ rtFull    _1gs (True, 42 :: Int) False

  putStrLn "== Prism _Just via existential (sum tensor) =="
  print $ overP _Just (++ "!") (Just "hi" :: Maybe String)
  print $ overP _Just (++ "!") (Nothing :: Maybe String)

  putStrLn "== exOut/exIn intuition (concrete c = whole pair) =="
  demoExConcrete
