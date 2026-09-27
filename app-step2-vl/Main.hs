{-# LANGUAGE RankNTypes #-}

-- | 补充：van Laarhoven（Functor）形态的 Lens
--
-- 与 Step 1 get/set、Step 2 Strong profunctor 并列的第三种常见编码。
-- @lens@ 库默认使用本形态。
--
-- 注意：这里的 @Functor f@ 是「效果容器」，不是 Functor strength / Tambara。
module Main where

import Data.Functor.Identity (Identity (..))

-- | van Laarhoven Lens
type Lens s t a b =
  forall f. Functor f => (a -> f b) -> s -> f t

type Lens' s a = Lens s s a a

-- | 只读载体：@Const r a@ 忽略 @a@，只保留 @r@
newtype Const r a = Const { getConst :: r }

instance Functor (Const r) where
  fmap _ (Const r) = Const r

-- | get/set → VL
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP afb s =
  fmap (setP s) (afb (get s))

view :: Lens s t a b -> s -> a
view l s = getConst (l Const s)

over :: Lens s t a b -> (a -> b) -> s -> t
over l f s = runIdentity (l (Identity . f) s)

set :: Lens s t a b -> b -> s -> t
set l b = over l (const b)

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))

-- 复合仍是 (.)
_2 :: Lens (c, a) (c, b) a b
_2 = lens snd (\(c, _) b -> (c, b))

main :: IO ()
main = do
  putStrLn "== van Laarhoven Lens =="
  print $ view _1 (True, 42 :: Int)
  print $ set  _1 False (True, 42 :: Int)
  print $ over _2 (*10) (True, 42 :: Int)
  putStrLn "== compose = (.) =="
  -- rank-2：不要 let 绑成单态；直接写 _1 . _1
  print $ view (_1 . _1) ((True, 1 :: Int), 'x')
