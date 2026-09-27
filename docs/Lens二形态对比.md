# Lens 三种形态对比：get/set / Strong / van Laarhoven

本文对比三种常见 `Lens` 编码。总原理见 [原理详解.md](原理详解.md)。

---

## 一览

| | **(A) 经典 get/set** | **(B) Strong / Profunctor** | **(C) van Laarhoven / Functor** |
|--|----------------------|-----------------------------|----------------------------------|
| **定义** | `data Lens … = Lens { view, set }` | `forall p. Strong p => p a b -> p s t` | `forall f. Functor f => (a -> f b) -> s -> f t` |
| **源码** | [`app/Main.hs`](../app/Main.hs) | [`app-step2/Main.hs`](../app-step2/Main.hs) | [`app-step2-vl/Main.hs`](../app-step2-vl/Main.hs) |
| **复合** | 手写 `compose` | `(.)` | `(.)` |
| **取运算** | 字段直接是函数 | 换 `p`：`Forget` / `(->)` | 换 `f`：`Const` / `Identity` |
| **库现实** | 教学 | `profunctor-optics` 一系 | **`lens` 库默认** |
| **类型难度** | 低 | 高（rank-2 + Profunctor） | 中高（rank-2 + Functor） |
| **统一 Prism** | 另起数据类型 | 改成 `Choice` | Prism 用别的约束；Traversal 用 `Applicative` |

(A)(B)(C) 在合法 Lens 上语义等价（可互相翻译）。

**划界**： (C) 里的 `Functor f` ≠ Functor strength / Tambara 上下文强度。Tambara 线走 (B) / Step 4。

---

## (A) 经典 get/set

```haskell
data Lens s t a b = Lens { view :: s -> a, set :: s -> b -> t }
```

**优点**：直觉好、定律好看、无 rank-2。  
**缺点**：复合啰嗦；难和 Prism/Traversal 统一。  
**适合**：第一小时建立「焦点×上下文」直觉。详见 Step 1。

---

## (B) `forall p. Strong p => …`

```haskell
type Lens s t a b = forall p. Strong p => p a b -> p s t
lens get setP = dimap (\s -> (get s, s)) (\(b,s) -> setP s b) . first'
```

**优点**：复合即 `(.)`；换 `p` 得多种运算；与 Choice/Tambara 同一故事。  
**缺点**：要先懂 Profunctor；rank-2 `let` 易踩坑。  
**适合**：接 Prism / Tambara / 广义 optic。详见 Step 2、4、5。

---

## (C) van Laarhoven（Functor）

```haskell
type Lens s t a b =
  forall f. Functor f => (a -> f b) -> s -> f t

lens get setP afb s = fmap (setP s) (afb (get s))

view l s = getConst (l Const s)           -- f = Const a
over l f s = runIdentity (l (Identity . f) s)  -- f = Identity
```

**优点**
1. 复合即 `(.)`（与 B 同）。
2. Haskell 日常生态默认（`lens` 包）。
3. 只需 `Functor`，很多人比 Profunctor 更熟。

**缺点**
1. 仍是 rank-2。
2. 和 Tambara「换张量」叙述不如 (B) 直接；Prism/Traversal 要换成别的类约束（如 `Applicative`），统一故事要多绕一步。
3. 易与「Functor strength」术语混淆——名字里都有 Functor，机制不同。

**小例子**（`stack exec step2b-van-laarhoven`；更细见 [van-Laarhoven教程.md](van-Laarhoven教程.md)）：

```text
view _1 (True,42)              → True
set  _1 False …                → (False,42)
over _2 (*10) …                → (True,420)
view (addressL . cityL) alice  → "Shanghai"
over _1Len length ("hi",True)  → (2,True)
```

**适合**：读/写 `lens` 库代码；与 (B) 对照「同语义、不同量化」。

---

## 怎么选？

| 场景 | 更合适 |
|------|--------|
| 讲课第一小时、写定律 | **(A)** |
| 对接 Tambara / profunctor optics 论文与叙述 | **(B)** |
| 对接 Hackage 上的 `lens`、日常工程 | **(C)** |
| 弄清等价 | 三者都写，Step 5 做 round-trip（A↔B）；C 与 A 用上面 `lens`/`view`/`over` 互译 |

本仓库路线：**先 (A) 后 (B)**，用 (C) 作与库对齐的补充；Tambara 主线仍以 (B) 为准。

---

## 相关入口

- Step 1：`stack exec step1-classic-lens`
- Step 2：`stack exec step2-strong-lens`
- Step 2b：`stack exec step2b-van-laarhoven`
- Step 5：`stack exec step5-optic-tambara`
- 原理：[原理详解.md](原理详解.md)

- VL 详细教程：[van-Laarhoven教程.md](van-Laarhoven教程.md)
