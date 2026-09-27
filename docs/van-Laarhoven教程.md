# van Laarhoven（Functor）形态详细教程

面向：已看过 Step 1（get/set）和 Step 2（Strong），想对齐 `lens` 库默认编码、并与另两种形态对照的读者。

可运行代码：[`app-step2-vl/Main.hs`](../app-step2-vl/Main.hs)（`stack exec step2b-van-laarhoven`）。  
三种形态总表：[Lens二形态对比.md](Lens二形态对比.md)。  
Tambara / Strong 线：[原理详解.md](原理详解.md)。

---

## 1. 定义：在说什么？

```haskell
type Lens s t a b =
  forall f. Functor f => (a -> f b) -> s -> f t

type Lens' s a = Lens s s a a
```

**读法（从右往左）**：

1. 你给我一个「焦点上的」函数 `a -> f b`（`f` 是某个 Functor）。
2. 我还给你一个「整树上的」函数 `s -> f t`。
3. 而且这对 **任意** `Functor f` 都要成立（`forall f`）。

直觉：Lens 不是一对 get/set 数据，而是一段 **「把焦点上的效果抬到整树上」** 的通用程序。不同的 `f` 抽出不同运算。

---

## 2. 从 get/set 拼出来（核心公式）

```haskell
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP afb s =
  fmap (setP s) (afb (get s))
```

逐步：

| 步骤 | 表达式 | 类型 | 含义 |
|------|--------|------|------|
| 取焦点 | `get s` | `a` | 从整树取出焦点 |
| 焦点上跑效果 | `afb (get s)` | `f b` | 用户给的 `a -> f b` |
| 写回 | `fmap (setP s) …` | `f t` | 在 `f` 里把新焦点装回整树 |

这与 get/set 语义相同：先看再改再装；`fmap` 负责「在效果 `f` 里」完成装回。

---

## 3. 换不同的 `f` → 不同运算

### 3.1 `view`：用 `Const`

```haskell
newtype Const r a = Const { getConst :: r }
-- fmap 忽略函数，只留 r

view :: Lens s t a b -> s -> a
view l s = getConst (l Const s)
```

这里 `afb = Const`，类型是 `a -> Const a b`（右边 `b` 被丢掉）。  
Lens 被迫只「读」出 `a`，装回用 `fmap` 也不改变那个 `a`。

### 3.2 `over` / `set`：用 `Identity`

```haskell
over l f s = runIdentity (l (Identity . f) s)
set  l b   = over l (const b)
```

`f = Identity` 表示「没有额外效果，就是普通改值」。

### 对照表

| 选用的 `f` | 得到 | 类比 Strong 形态里的 |
|-----------|------|----------------------|
| `Const r` | `view` | `Forget r` |
| `Identity` | `over` / `set` | `(->)` |
| （更多）`Const (Sum …)` 等 | fold 类 | 其它 `p` |

---

## 4. 例子（与 Step 1 / 2 同一场景）

```haskell
_1 = lens fst (\(_, c) b -> (b, c))
_2 = lens snd (\(c, _) b -> (c, b))

view _1 (True, 42)           -- True
set  _1 False (True, 42)     -- (False, 42)
over _2 (*10) (True, 42)     -- (True, 420)

-- 复合 = (.)
view (_1 . _1) ((True, 1), 'x')  -- True
```

运行：`stack exec step2b-van-laarhoven`。

**rank-2 坑**（与 Strong 形态相同）：不要 `let l = _1 . _1` 再 `view l`，会卡在某个具体 `f0`；保持多态，直接 `view (_1 . _1) …`。

---

## 5. 与 (A) get/set、(B) Strong 对照

| | (A) get/set | (B) Strong | **(C) VL / Functor** |
|--|-------------|------------|----------------------|
| 量化 | 无 | `forall p. Strong p` | `forall f. Functor f` |
| 复合 | 手写 | `(.)` | `(.)` |
| 读 | 字段 `view` | `Forget` | `Const` |
| 写 | 字段 `set` | `(->)` | `Identity` |
| 库 | 教学 | profunctor-optics | **`lens` 默认** |
| 接 Tambara | 间接 | **直接**（Strong=积上 Tambara） | 间接（先译到 B 或 get/set） |

**互译直觉**：

- (A) → (C)：就是上面的 `lens get setP`。
- (C) → (A)：`view` + `set`（用 `Const` / `Identity`）收回一对函数。
- (B) ↔ (C)：在合适条件下等价；本仓库 Tambara 叙述以 (B) 为主，(C) 负责对齐日常 `lens`。

---

## 6. 和 Traversal / Prism 的关系（预告）

van Laarhoven 家族靠 **加强 `f` 上的约束** 区分 optic：

| optic | 对 `f` 的要求（常见说法） |
|-------|---------------------------|
| Lens | `Functor f` |
| Traversal | `Applicative f` |
| （部分表述里）Prism 等 | 另有编码；profunctor 侧用 Choice 更整齐 |

因此：若你的主线是 **Tambara / 约束表（Strong、Choice）**，跟 Step 3–5 的 (B)；若你的主线是 **读 `lens` 源码、写 `traverseOf`**，跟 (C) 并把 `Functor` 换成 `Applicative`。

---

## 7. 常见误区

1. **「Functor」混为一谈**  
   VL 的 `Functor f` = 效果容器；**不是** Functor strength，也不是 Tambara 的上下文强度 α。后者见 Step 4。

2. **单态 `let`**  
   `Lens` 是 rank-2；绑定后丢失 `forall f`。

3. **以为只有两种形态**  
   工程上至少三种：数据对、(B) profunctor、(C) VL。见对比文。

---

## 8. 建议阅读顺序

1. Step 1 弄清 get/set 与定律。  
2. 读本文 §2–§4，跑 `step2b-van-laarhoven`。  
3. Step 2 看同一语义的 Strong 拼法，对照 §5 表。  
4. 需要 Tambara / ∀p ↔ ∃m 时走 Step 4–5；需要库 API 时看 Step 6。

---

## 相关入口

- 代码：`app-step2-vl/Main.hs`
- 对比：[Lens二形态对比.md](Lens二形态对比.md)
- 原理：[原理详解.md](原理详解.md)
- Strong 步：`stack exec step2-strong-lens`
