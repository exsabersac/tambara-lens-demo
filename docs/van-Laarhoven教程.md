# van Laarhoven（Functor）形态详细教程

面向：已看过 Step 1（get/set）和 Step 2（Strong），想对齐 `lens` 库默认编码、并与另两种形态对照的读者。

可运行代码：[`app-step2-vl/Main.hs`](../app-step2-vl/Main.hs)（`stack exec step2b-van-laarhoven`）。  
三种形态总表：[Lens二形态对比.md](Lens二形态对比.md)。  
Tambara / Strong 线：[原理详解.md](原理详解.md)。

本文比初版更细：原理（为何 `forall f` 够用）、**Lens 组合**（为何是 `(.)`、类型怎么拼）、逐步类型推导、记录嵌套、类型会变、换 `f`，以及和 Strong/`Forget` 对照。

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

## 2. 原理：为什么这样定义就够了？

### 2.1 它在范畴上在说什么

把「焦点上的修改」看成一个映射族：

\[
\alpha_f : (a \to f\, b) \to (s \to f\, t)
\]

并对 **每一个** Functor \(f\) 都给出一个 \(\alpha_f\)，且与 `fmap` 相容（自然语言变换条件：\(\alpha\) 对 `fmap` 自然）。van Laarhoven 观察是：

> 这样一套自然的 \(\alpha\) **恰好**对应一对「取焦点 / 装回」——也就是经典 get/set。

Haskell 里不写自然性条件，而是写成单个多态函数：

```haskell
forall f. Functor f => (a -> f b) -> s -> f t
```

`Functor` 约束保证你只能用 `fmap` 把「新焦点 → 新整树」抬进效果；你不能对 `f` 做额外拆包（那会破坏「任意 f」）。于是程序形态被逼成：

```text
取焦点 → 在焦点上跑 afb → fmap 装回
```

这正是 `lens get setP` 那一行。

### 2.2 为何「任意 Functor」而不是某一个？

若只对某一个 `f` 成立，你只能做那一种运算。  
对 **所有** Functor 成立，意味着同一段代码在代入 `Const` / `Identity` / … 时都能类型检查——于是 **一种编码、多种运算**。

直觉对照：

| 你固定住的东西 | 你得到的能力 |
|----------------|--------------|
| 只固定 `Identity` | 只能 `over`/`set` |
| 只固定 `Const` | 只能 `view` |
| 对所有 `f` 都给出同一段程序 | 上面两种（以及更多）都能抽出 |

这与 Strong 形态「对所有 Strong `p` 给出同一段程序」是平行设计：量化范围 = 可抽取运算的菜单。

### 2.3 和 get/set 的信息量

从 (A) 到 (C)：`lens get setP` 把两个函数打包进一个多态函数。  
从 (C) 回到 (A)：用 `Const` / `Identity` 特化，收回 `view` 与 `set`。

因此在「合法 Lens」上，**(A) 与 (C) 携带的信息相同**；差别在复合方式与和 Prism/Traversal 的统一路径。定律（get-set / set-get / set-set）仍对收回的 get/set 陈述；VL 侧常写成对 `view`/`set`/`over` 的同款等式。

### 2.4 单焦点 ↔ `Functor`（为 Traversal 埋伏笔）

装回一步只需要 `fmap :: (b -> t) -> f b -> f t`——这是 **一个** 新焦点对应 **一棵** 新整树。  
若有多个焦点，要把多处 `f b` 拼成一个 `f t`，就需要 `pure` 与 `<*>`，即把约束升到 `Applicative`（Traversal）。  
所以：`Functor` 不是随便选的，它精确对应「单焦点、上下文唯一」的 Lens。

---

## 3. 原理：Lens 之间如何组合？

### 3.1 为什么组合就是 `(.)`？

把 `Lens s t a b` 的类型括号写清楚：

```haskell
Lens s t a b
  ≅ forall f. Functor f => (a -> f b) -> (s -> f t)
```

对固定的 `f`，这就是普通函数类型 `X -> Y`。  
两个这种函数按中间类型对接，就是 Haskell 的函数复合 `(.)`。

设

```haskell
l :: Lens s t a b   -- (a -> f b) -> (s -> f t)
m :: Lens a b c d   -- (c -> f d) -> (a -> f b)
```

则

```haskell
l . m :: Lens s t c d
-- 因为 (l . m) afb = l (m afb)
```

展开一句：

```text
(l . m) afb s
  = l (m afb) s
  = 「先用 m 把『焦点 c 上的效果』抬成『中层 a 上的效果』，
      再用 l 抬成『整树 s 上的效果』」
```

**没有**单独的 `composeLens`；编码本身已是函数，复合运算被「偷」成了 `(.)`。

### 3.2 类型参数怎么拼？（必看表）

| 透镜 | `s` | `t` | `a` | `b` | 口语 |
|------|-----|-----|-----|-----|------|
| 外层 `l` | 大树前 | 大树后 | **中层前** | **中层后** | 「从大树看到中层」 |
| 内层 `m` | **中层前** | **中层后** | 焦点前 | 焦点后 | 「从中层看到焦点」 |
| 复合 `l . m` | 大树前 | 大树后 | 焦点前 | 焦点后 | 「从大树直接看到焦点」 |

中层的 `a`/`b` 被消掉：外层的焦点类型 = 内层的整树类型。

`Lens'` 特例更简单：

```haskell
l :: Lens' S A
m :: Lens' A C
l . m :: Lens' S C
```

### 3.3 书写顺序：路径从左到右

Haskell 里 `(l . m)` 表示「先应用 `m`，再应用 `l`」（函数复合惯例）。  
读路径时人们常说「先 `addressL` 再 `cityL`」——那是 **进入数据结构的顺序**，对应代码里也写作 `addressL . cityL`（外层在左、内层在右）：

```haskell
personCity = addressL . cityL
-- 外层 addressL :: Lens' Person Address
-- 内层 cityL    :: Lens' Address String
-- 复合           :: Lens' Person String
```

与 get/set 手写复合对照：

```haskell
-- (A) 必须自己写：
compose l m = Lens
  { view = view m . view l
  , set  = \s b -> set l s (set m (view l s) b)
  }

-- (C) 直接：
l . m
```

Strong 形态同样是 `(.)`。**(A) 复合啰嗦，(B)(C) 复合免费**——这是换编码的主要工程收益之一。

### 3.4 结合律与单位

因为 `(.)` 本身满足：

```text
(l . m) . n  =  l . (m . n)
id . l       =  l  =  l . id
```

其中「单位透镜」在 VL 里就是普通的 `id`（在合适类型下）：

```haskell
id :: Lens' a a   -- 焦点 = 整树
```

三层嵌套只需连写：

```haskell
-- 例如：((a,b),c) 的最内左焦点
_1 . _1          -- 两层
-- 记录：若还有 Country 包着 Address，可写成
-- countryL . addressL . cityL
```

结合律保证括号怎么加语义不变（类型能对上的前提下）。

### 3.5 组合后运算如何作用？

`view` / `over` 不关心透镜是「原子」还是「复合」——它们只代入某个 `f`：

```haskell
view (l . m) s     = view m (view l s)          -- 读：先外后内
over (l . m) f s   = over l (over m f) s        -- 改：在外层里改「内层整树」
```

第二式用 Identity 展开即：`l` 的 `afb` 被设成 `m (Identity . f)`，于是内层先改焦点，外层再把改过的中层装回大树。

定律在复合下保持：若 `l`、`m` 各自满足 Lens 定律，则 `l . m` 也满足（对收回的 get/set 而言）。

### 3.6 与 Strong 组合的对照

| | Strong (B) | VL (C) |
|--|------------|--------|
| 编码 | `p a b -> p s t` | `(a -> f b) -> s -> f t` |
| 复合 | `(.)` | `(.)` |
| 展开 | `(l . m) pab = l (m pab)` | `(l . m) afb = l (m afb)` |
| 读路径 | 外 `.` 内 | 同左 |

差别不在组合机制，而在「中间被传递的东西」是 `p a b` 还是 `a -> f b`。Strong 侧展开见 [Strong-Profunctor组合.md](Strong-Profunctor组合.md)。

### 3.7 rank-2 与组合

组合结果仍是 rank-2。`let` 绑死某个具体 `f` 后，就不能再拿去 `view`（要 `Const`）又 `over`（要 `Identity`）。  
组合本身不引入新坑；**绑定多态透镜**才是坑。写法：内联 `view (l . m) s`，或给 `l . m` 显式 `Lens`/`Lens'` 签名。

---

## 4. 从 get/set 拼出来（核心公式）

```haskell
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP afb s =
  fmap (setP s) (afb (get s))
```

### 4.1 逐步类型表

固定一次调用：`afb :: a -> f b`，`s :: s`。

| 步骤 | 表达式 | 类型 | 含义 |
|------|--------|------|------|
| 取焦点 | `get s` | `a` | 从整树取出焦点 |
| 焦点上跑效果 | `afb (get s)` | `f b` | 用户给的 `a -> f b` |
| 写回函数 | `setP s` | `b -> t` | 「给定新焦点，造出新整树」 |
| 在 `f` 里写回 | `fmap (setP s) (afb (get s))` | `f t` | 效果里带着新整树 |

这与 get/set 语义相同：先看再改再装；`fmap` 负责「在效果 `f` 里」完成装回。

### 4.2 用具体数字走一遍（`over`）

设 `s = (True, 42)`，`_2 = lens snd (\(c,_) b -> (c,b))`，要做 `over _2 (*10)`。

此时 `f = Identity`，`afb = Identity . (*10)`：

1. `get s = 42`
2. `afb 42 = Identity 420`
3. `setP s = \b -> (True, b)`
4. `fmap (setP s) (Identity 420) = Identity (True, 420)`
5. `runIdentity` → `(True, 420)`

### 4.3 用同一 Lens 走一遍（`view`）

`view _2 (True, 42)` 时 `afb = Const`（见下一节）：

1. `get s = 42`
2. `Const 42` 的类型是 `Const Int b`（`b` 幽灵参数）
3. `fmap (setP s) (Const 42) = Const 42`（`Const` 的 `fmap` 丢掉函数）
4. `getConst` → `42`

读操作根本不执行「写回」；`fmap` 被 `Const` 吃掉了。这就是 VL 的巧妙之处：同一段 `lens` 程序，靠 `f` 的选择变成读或写。

---

## 5. 换不同的 `f` → 不同运算

### 5.1 `view`：用 `Const`

```haskell
newtype Const r a = Const { getConst :: r }

instance Functor (Const r) where
  fmap _ (Const r) = Const r   -- 忽略映射，只留 r

view :: Lens s t a b -> s -> a
view l s = getConst (l Const s)
```

这里 `afb = Const`，类型是 `a -> Const a b`。  
Lens 被迫只「读」出 `a`；装回用 `fmap` 也不改变那个 `a`。

### 5.2 `over` / `set`：用 `Identity`

```haskell
over l f s = runIdentity (l (Identity . f) s)
set  l b   = over l (const b)
```

`f = Identity` 表示「没有额外效果，就是普通改值」。

### 5.3 再换一次：`Const (Sum Int)`（演示「换 f」）

不必只用于「原样取出焦点」。例如把焦点 `Int` 先包进 `Sum`，再解开：

```haskell
viewAsSum :: Lens' s Int -> s -> Int
viewAsSum l s =
  getSum (getConst (l (\n -> Const (Sum n)) s))
```

语义仍是「读那个 Int」，但路径是：`a -> Const (Sum Int) b`。  
教程里用它只为强调：**运算 = 选一个 Functor 实例**，不是 Lens 里另写一套 API。

（真正的 `foldMapOf` / 多焦点累加属于 Traversal + `Applicative`，见 §11。）

### 对照表

| 选用的 `f` | 得到 | 类比 Strong 形态里的 |
|-----------|------|----------------------|
| `Const r`（`r ~ a`） | `view` | `Forget r` |
| `Identity` | `over` / `set` | `(->)` |
| `Const (Sum n)` 等 | 带 monoid 包装的读 | 其它 `Forget` 变体 |
| （库里）`Const m` + Traversal | `foldMapOf` | 多焦点 + monoid |

---

## 6. 例子 A：元组（与 Step 1 / 2 同一场景）

```haskell
_1 = lens fst (\(_, c) b -> (b, c))
_2 = lens snd (\(c, _) b -> (c, b))

view _1 (True, 42)           -- True
set  _1 False (True, 42)     -- (False, 42)
over _2 (*10) (True, 42)     -- (True, 420)
```

### 复合示例（原理见 §3）

```haskell
view (_1 . _1) ((True, 1), 'x')    -- True
set  (_1 . _2) 99 ((True, 1), 'x') -- ((True, 99), 'x')
over (_1 . _2) (+5) …               -- ((True, 6), 'x')

-- 三层：(((Bool, Int), Char), String) 的最内左
view (_1 . _1 . _1) (((True, 1), 'x'), "z")  -- True
```

`view (l . m) = view m . view l`；`over (l . m) f = over l (over m f)`。rank-2：不要对 `l . m` 做单态 `let`（§3.7）。

---

## 7. 例子 B：记录字段与嵌套

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

## 8. 例子 C：类型会变的 Lens

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

## 9. 手写展开：`view nameL alice`

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

## 10. 与 (A) get/set、(B) Strong 对照

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

## 11. Traversal / Prism 预告（VL 家族）

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

## 12. 常见误区

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

## 13. 建议阅读顺序

1. Step 1：get/set 与定律。  
2. 本文 §1–§3（定义 + 原理 + **组合**），跑 demo 组合段。  
3. 本文 §4–§5，弄清 `lens` / `Const` / `Identity`。  
4. 本文 §6–§9，跑 demo 全段（记录、嵌套、类型变化、展开）。  
5. Step 2：Strong 拼法，对照 §10。  
6. Tambara：Step 4–5；库 API：Step 6。

---

## 14. 运行与输出对照

```bash
stack exec step2b-van-laarhoven
```

预期分段大致为：

1. 元组 view/set/over  
2. 复合：`(_1 . _1)` / `(_1 . _2)` / 三层 / `view`/`over` 分配律  
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
