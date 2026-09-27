# van Laarhoven（Functor）形态详细教程

面向：已看过 Step 1（get/set）和 Step 2（Strong），想对齐 `lens` 库默认编码、并与另两种形态对照的读者。

可运行代码：[`app-step2-vl/Main.hs`](../app-step2-vl/Main.hs)（`stack exec step2b-van-laarhoven`）。  
三种形态总表：[Lens二形态对比.md](Lens二形态对比.md)。  
Tambara / Strong 线：[原理详解.md](原理详解.md)。

本文比初版更细：逐步类型推导、记录嵌套、类型会变的 Lens、换 `f` 的多种用法，以及和 Strong/`Forget` 的一一对照。

---

## 1. 定义：在说什么？

```haskell
type Lens s t a b =
  forall f. Functor f => (a -> f b) -> s -> f t

type Lens' s a = Lens s s a a
```

四个类型参数（与 get/set、Strong 同惯例）：

| 参数 | 角色 |
|------|------|
| `s` | 改之前的整树 |
| `t` | 改之后的整树（类型可变） |
| `a` | 改之前的焦点 |
| `b` | 改之后的焦点（类型可变） |

**读法（从右往左）**：

1. 你给我一个「焦点上的」函数 `a -> f b`（`f` 是某个 Functor）。
2. 我还给你一个「整树上的」函数 `s -> f t`。
3. 而且这对 **任意** `Functor f` 都要成立（`forall f`）。

直觉：Lens 不是一对 get/set 数据，而是一段 **「把焦点上的效果抬到整树上」** 的通用程序。不同的 `f` 抽出不同运算。

与 (B) Strong 的对照一句：Strong 是「换 profunctor `p`」；VL 是「换 Functor `f`」。语义都能覆盖 view/over，量化对象不同。

---

## 2. 从 get/set 拼出来（核心公式）

```haskell
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP afb s =
  fmap (setP s) (afb (get s))
```

### 2.1 逐步类型表

固定一次调用：`afb :: a -> f b`，`s :: s`。

| 步骤 | 表达式 | 类型 | 含义 |
|------|--------|------|------|
| 取焦点 | `get s` | `a` | 从整树取出焦点 |
| 焦点上跑效果 | `afb (get s)` | `f b` | 用户给的 `a -> f b` |
| 写回函数 | `setP s` | `b -> t` | 「给定新焦点，造出新整树」 |
| 在 `f` 里写回 | `fmap (setP s) (afb (get s))` | `f t` | 效果里带着新整树 |

这与 get/set 语义相同：先看再改再装；`fmap` 负责「在效果 `f` 里」完成装回。

### 2.2 用具体数字走一遍（`over`）

设 `s = (True, 42)`，`_2 = lens snd (\(c,_) b -> (c,b))`，要做 `over _2 (*10)`。

此时 `f = Identity`，`afb = Identity . (*10)`：

1. `get s = 42`
2. `afb 42 = Identity 420`
3. `setP s = \b -> (True, b)`
4. `fmap (setP s) (Identity 420) = Identity (True, 420)`
5. `runIdentity` → `(True, 420)`

### 2.3 用同一 Lens 走一遍（`view`）

`view _2 (True, 42)` 时 `afb = Const`（见下一节）：

1. `get s = 42`
2. `Const 42` 的类型是 `Const Int b`（`b` 幽灵参数）
3. `fmap (setP s) (Const 42) = Const 42`（`Const` 的 `fmap` 丢掉函数）
4. `getConst` → `42`

读操作根本不执行「写回」；`fmap` 被 `Const` 吃掉了。这就是 VL 的巧妙之处：同一段 `lens` 程序，靠 `f` 的选择变成读或写。

---

## 3. 换不同的 `f` → 不同运算

### 3.1 `view`：用 `Const`

```haskell
newtype Const r a = Const { getConst :: r }

instance Functor (Const r) where
  fmap _ (Const r) = Const r   -- 忽略映射，只留 r

view :: Lens s t a b -> s -> a
view l s = getConst (l Const s)
```

这里 `afb = Const`，类型是 `a -> Const a b`。  
Lens 被迫只「读」出 `a`；装回用 `fmap` 也不改变那个 `a`。

### 3.2 `over` / `set`：用 `Identity`

```haskell
over l f s = runIdentity (l (Identity . f) s)
set  l b   = over l (const b)
```

`f = Identity` 表示「没有额外效果，就是普通改值」。

### 3.3 再换一次：`Const (Sum Int)`（演示「换 f」）

不必只用于「原样取出焦点」。例如把焦点 `Int` 先包进 `Sum`，再解开：

```haskell
viewAsSum :: Lens' s Int -> s -> Int
viewAsSum l s =
  getSum (getConst (l (\n -> Const (Sum n)) s))
```

语义仍是「读那个 Int」，但路径是：`a -> Const (Sum Int) b`。  
教程里用它只为强调：**运算 = 选一个 Functor 实例**，不是 Lens 里另写一套 API。

（真正的 `foldMapOf` / 多焦点累加属于 Traversal + `Applicative`，见 §8。）

### 对照表

| 选用的 `f` | 得到 | 类比 Strong 形态里的 |
|-----------|------|----------------------|
| `Const r`（`r ~ a`） | `view` | `Forget r` |
| `Identity` | `over` / `set` | `(->)` |
| `Const (Sum n)` 等 | 带 monoid 包装的读 | 其它 `Forget` 变体 |
| （库里）`Const m` + Traversal | `foldMapOf` | 多焦点 + monoid |

---

## 4. 例子 A：元组（与 Step 1 / 2 同一场景）

```haskell
_1 = lens fst (\(_, c) b -> (b, c))
_2 = lens snd (\(c, _) b -> (c, b))

view _1 (True, 42)           -- True
set  _1 False (True, 42)     -- (False, 42)
over _2 (*10) (True, 42)     -- (True, 420)
```

### 复合 = `(.)`

VL 的 `Lens` 本身是函数类型，复合就是普通函数复合：

```haskell
view (_1 . _1) ((True, 1), 'x')   -- True
set  (_1 . _2) 99 ((True, 1), 'x') -- ((True, 99), 'x')
over (_1 . _2) (+5) …              -- ((True, 6), 'x')
```

类型上：`(_1 . _1)` 先对「外层左分量」用 `_1`，再对「内层左分量」用 `_1`。

**rank-2 坑**（与 Strong 形态相同）：

```haskell
-- 容易挂：
let l = _1 . _1
in view l ((True, 1), 'x')
-- GHC 可能把 l 单态成某个具体 f0，再 view 时 Const 对不上。

-- 稳妥：保持内联
view (_1 . _1) …

-- 或给显式多态签名（进阶）
l :: Lens' ((a, b), c) a
l = _1 . _1
```

---

## 5. 例子 B：记录字段与嵌套

```haskell
data Address = Address { _city :: String, _zip :: Int }
data Person  = Person  { _name :: String, _age :: Int, _address :: Address }

nameL    = lens _name    (\p n -> p { _name = n })
ageL     = lens _age     (\p a -> p { _age = a })
addressL = lens _address (\p a -> p { _address = a })
cityL    = lens _city    (\a c -> a { _city = c })
zipL     = lens _zip     (\a z -> a { _zip = z })

personCity = addressL . cityL
```

对示例值：

```haskell
alice = Person "Alice" 30 (Address "Shanghai" 200000)

view nameL alice              -- "Alice"
view ageL alice               -- 30
set  nameL "Alicia" alice     -- 名字改掉，其余不变
over ageL (+1) alice          -- 年龄 31

view personCity alice         -- "Shanghai"
set  personCity "Beijing" alice
over (addressL . zipL) (+1) alice
```

**读法**：`addressL . cityL` = 先进入 `Person` 的 address 焦点，再进入 `Address` 的 city 焦点。  
中间类型：`Person → Address → String`，复合后 `Person → String`。

这比手写

```haskell
\p -> _city (_address p)
\p c -> p { _address = (_address p) { _city = c } }
```

短得多，且复合可继续叠（`foo . bar . baz`）。

---

## 6. 例子 C：类型会变的 Lens

`Lens s t a b` 允许焦点类型从 `a` 变成 `b`，整树从 `s` 变成 `t`。

```haskell
-- 焦点：String → Int（例如改成 length）
_1Len :: Lens (String, c) (Int, c) String Int
_1Len = lens fst (\(_, c) n -> (n, c))

view _1Len ("hi", True)           -- "hi" :: String
over _1Len length ("hi", True)    -- (2, True) :: (Int, Bool)
```

`view` 仍返回改之前的焦点类型 `a`；`over` 之后整树类型已是 `t`。  
这与 Step 1 里「类型会变的 get/set」是同一现象，只是编码换成了 VL。

---

## 7. 手写展开：`view nameL alice`

把 `lens` 公式和 `Const` 代进去（与 demo 第 7 段一致）：

```text
view nameL alice
  = getConst (nameL Const alice)
  = getConst ( fmap (\n -> alice{ _name = n })
                     (Const (_name alice)) )
  = getConst (Const "Alice")          -- fmap 对 Const 是空操作
  = "Alice"
```

再对比 `over ageL (+1) alice`：

```text
over ageL (+1) alice
  = runIdentity (nameL 的同类展开，但 afb = Identity . (+1))
  = runIdentity (fmap (\a -> alice{_age=a}) (Identity 31))
  = alice { _age = 31 }
```

同一条 `lens get setP` 程序；差别只在 `afb` 选的是 `Const` 还是 `Identity . f`。

---

## 8. 与 (A) get/set、(B) Strong 对照

| | (A) get/set | (B) Strong | **(C) VL / Functor** |
|--|-------------|------------|----------------------|
| 量化 | 无 | `forall p. Strong p` | `forall f. Functor f` |
| 复合 | 手写 | `(.)` | `(.)` |
| 读 | 字段 `view` | `Forget` | `Const` |
| 写 | 字段 `set` | `(->)` | `Identity` |
| 库 | 教学 | profunctor-optics | **`lens` 默认** |
| 接 Tambara | 间接 | **直接**（Strong=积上 Tambara） | 间接（先译到 B 或 get/set） |

**互译**：

- (A) → (C)：`lens get setP`（§2）。
- (C) → (A)：`view` + `set` 收回一对函数。
- (B) ↔ (C)：合法 Lens 上语义等价；本仓库 Tambara 叙述以 (B) 为主，(C) 对齐日常 `lens`。

**Forget ↔ Const 对照**（读操作）：

| Strong | VL |
|--------|-----|
| `view l s = l (Forget id) s` 再 `getForget` | `view l s = getConst (l Const s)` |
| `Forget r` 丢掉右边、留下 `r` | `Const r` 丢掉「映射目标」、留下 `r` |

两者都是「只保留一个只读摘要」的载体；一个挂在 profunctor 上，一个挂在 Functor 上。

---

## 9. Traversal / Prism 预告（VL 家族）

van Laarhoven 家族靠 **加强 `f` 上的约束** 区分 optic：

| optic | 对 `f` 的要求（常见说法） |
|-------|---------------------------|
| Lens | `Functor f` |
| Traversal | `Applicative f` |
| （部分表述） | Prism 等另有编码；profunctor 侧用 Choice 更整齐 |

把 `Functor` 换成 `Applicative` 后，你可以「走访多个焦点」（例如列表每个元素），并用 `pure` / `<*>` 把多处修改拼回去。那是下一步；本 demo 仍停在单焦点 Lens。

因此：

- 主线是 **Tambara / Strong、Choice** → Step 3–5 的 (B)。
- 主线是 **读 `lens` 源码、`traverseOf`** → (C)，并把约束从 `Functor` 升到 `Applicative`。

---

## 10. 常见误区

1. **「Functor」混为一谈**  
   VL 的 `Functor f` = 效果容器；**不是** Functor strength，也不是 Tambara 的上下文强度 α。后者见 Step 4。

2. **单态 `let`**  
   `Lens` 是 rank-2；绑定后丢失 `forall f`。保持内联或写显式多态签名。

3. **以为只有两种形态**  
   工程上至少三种：数据对、(B) profunctor、(C) VL。见对比文。

4. **把 `fmap` 理解成「改焦点」**  
   焦点上的修改在 `afb`；`fmap` 只负责把「新焦点 → 新整树」抬进效果 `f`。

5. **`Lens'` 与 `Lens` 混淆**  
   `Lens' s a = Lens s s a a` 是「整树与焦点类型都不变」的特例；类型会变的场景要用完整四参数（§6）。

---

## 11. 建议阅读顺序

1. Step 1：get/set 与定律。  
2. 本文 §1–§4，跑 demo 段 1–2。  
3. 本文 §5–§7，跑 demo 段 3–7（记录、嵌套、类型变化、展开）。  
4. Step 2：同一语义的 Strong 拼法，对照 §8。  
5. Tambara / ∀p ↔ ∃m：Step 4–5；库 API：Step 6。

---

## 12. 运行与输出对照

```bash
stack exec step2b-van-laarhoven
```

预期分段大致为：

1. 元组 view/set/over  
2. `(_1 . _1)` / `(_1 . _2)` 复合  
3. `nameL` / `ageL`  
4. `personCity` 与 zip  
5. `_1Len` + `length`  
6. `viewAsSum`  
7. 手写 `getConst (nameL Const alice)`

源码里每段有注释；打不通时先看类型是否因 `let` 单态化。

---

## 相关入口

- 代码：`app-step2-vl/Main.hs`
- 对比：[Lens二形态对比.md](Lens二形态对比.md)
- 原理：[原理详解.md](原理详解.md)
- Strong 步：`stack exec step2-strong-lens`
