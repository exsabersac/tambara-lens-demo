# Strong / Profunctor 形态：原理与 Lens 组合

面向：已跑通 Step 2，想把 **(B) `forall p. Strong p`** 下的组合机制讲透，并与 van Laarhoven 的 `(.)` 对照。

可运行代码：[`app-step2/Main.hs`](../app-step2/Main.hs)（`stack exec step2-strong-lens`）。  
VL 侧组合专章：[van-Laarhoven教程.md](van-Laarhoven教程.md) §3。  
总原理：[原理详解.md](原理详解.md)。

---

## 1. 定义回顾

```haskell
type Lens s t a b = forall p. Strong p => p a b -> p s t
type Lens' s a    = Lens s s a a

lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'
```

读法：对任意 Strong profunctor `p`，把「焦点上的」`p a b` 抬成「整树上的」`p s t`。

| `p` | 抽出 |
|-----|------|
| `(->)` | `over` / `set` |
| `Forget r` | `view` |

---

## 2. 原理：为何组合就是 `(.)`？

### 2.1 类型就是函数

括号写清：

```haskell
Lens s t a b
  ≅ forall p. Strong p => p a b -> p s t
```

对固定的 `p`，这是普通函数 `X -> Y`。两个 Lens 在中间类型对接，就是 Haskell 的 `(.)`。

设

```haskell
l :: Lens s t a b   -- p a b -> p s t
m :: Lens a b c d   -- p c d -> p a b
```

则

```haskell
l . m :: Lens s t c d
-- (l . m) pcd = l (m pcd)
```

展开：

```text
(l . m) pcd
  = l (m pcd)
  = 「先用内层 m 把『最内焦点上的 p』抬到中层，
      再用外层 l 抬到整树」
```

**没有**单独的 `composeLens`；与 VL 一样，编码本身已是函数。

### 2.2 类型参数怎么拼？

| 透镜 | `s` | `t` | `a` | `b` | 口语 |
|------|-----|-----|-----|-----|------|
| 外层 `l` | 大树前 | 大树后 | **中层前** | **中层后** | 大树 ↔ 中层 |
| 内层 `m` | **中层前** | **中层后** | 焦点前 | 焦点后 | 中层 ↔ 焦点 |
| 复合 `l . m` | 大树前 | 大树后 | 焦点前 | 焦点后 | 大树 ↔ 焦点 |

中层被消掉。`Lens'` 更简单：`Lens' S A` 与 `Lens' A C` 合成 `Lens' S C`。

书写顺序：**外 `.` 内**（进入数据结构的路径从左到右）：

```haskell
_cityOf = _address . _city
-- _address :: Lens' Person Address
-- _city    :: Lens' Address String
-- 复合      :: Lens' Person String
```

### 2.3 与 get/set 手写复合对照

```haskell
-- (A) 必须自己写：
compose l m = Lens
  { view = view m . view l
  , set  = \s b -> set l s (set m (view l s) b)
  }

-- (B) Strong：直接
l . m
```

语义相同；`(B)` 还保证复合结果对 **所有** Strong `p` 成立（不只对某一实例）。

### 2.4 结合律与单位

```text
(l . m) . n  =  l . (m . n)
id . l       =  l  =  l . id
```

单位在合适类型下就是 `id`：

```haskell
id :: Lens' a a   -- 焦点 = 整树
```

三层：`_1 . _1 . _1` 等，括号怎么加语义不变。

---

## 3. 组合后运算如何作用？

`view` / `over` 只是代入某个 Strong 实例；它们不区分「原子」与「复合」：

```haskell
view (l . m) s   = view m (view l s)
over (l . m) f s = over l (over m f) s
```

### 3.1 `over` 侧（`p = (->)`）

```haskell
over (l . m) f
  = (l . m) f
  = l (m f)
```

`m f` 已是「中层上的」`a -> b`；再经 `l` 抬成「大树上的」`s -> t`。  
这与 `over l (over m f)` 相同。

### 3.2 `view` 侧（`p = Forget`）

```haskell
view (l . m) s
  = runForget ( (l . m) (Forget id) ) s
  = runForget ( l (m (Forget id)) ) s
```

内层 `m (Forget id)` 得到 `Forget c a b`（只读中层焦点）；外层 `l` 再把它抬成对大树的只读。  
结果等于 `view m (view l s)`。

### 3.3 与 VL 展开对照

| | Strong (B) | VL (C) |
|--|------------|--------|
| 展开 | `(l . m) pab = l (m pab)` | `(l . m) afb = l (m afb)` |
| 中间传递 | `p a b` | `a -> f b` |
| `view` 分配 | `view m . view l` | 同左 |
| `over` 分配 | `over l (over m f)` | 同左 |

组合机制相同；差别在「中间被传递的东西」。

---

## 4. 管道视角：两个 `lens` 公式叠在一起

单个：

```haskell
lens get setP = dimap (\s -> (get s, s)) (\(b,s) -> setP s b) . first'
```

复合 `l . m` 在 `p` 上等于：先跑内层整条管道，再跑外层。不必手工展开成一个巨大的 `dimap`；类型系统保证中间 `p a b` 对接。

直觉：

```text
最内焦点上的 p
  --m--> 中层上的 p
  --l--> 大树上的 p
```

这与 Tambara 叙述一致：每次 `first'`/`dimap` 都在「带上下文抬一层」；组合就是连续抬多层。

---

## 5. 例子

### 5.1 元组

```haskell
view (_1 . _1) ((True, 1), 'x')     -- True
set  (_1 . _2) 99 ((True, 1), 'x')  -- ((True, 99), 'x')
over (_1 . _2) (+5) …               -- ((True, 6), 'x')

view (_1 . _1 . _1) (((True,1),'x'),"z")  -- True
```

### 5.2 记录

```haskell
_cityOf = _address . _city
view _cityOf alice          -- "Shanghai"
set  _cityOf "Beijing" alice
```

### 5.3 分配律（demo 会打印 `True`）

```haskell
view (_1 . _2) s     == view _2 (view _1 s)
over (_1 . _2) f s   == over _1 (over _2 f) s
view (id . _1) s     == view _1 s
view (_1 . id) s     == view _1 s
```

---

## 6. rank-2 坑（与 VL 相同）

```haskell
-- 容易挂：
let o = _address . _city
in view o alice
-- 可能把 o 单态成某个具体 p0，再 view（要 Forget）对不上。

-- 稳妥：内联，或显式多态签名
view (_address . _city) alice

o :: Lens' Person String
o = _address . _city
```

组合不引入新坑；**绑定多态 optic** 才是坑。

---

## 7. 和 Choice / Prism 组合的边界（预告）

- Lens 要求 `Strong`；Prism 要求 `Choice`。
- `Lens . Lens = Lens`（都是 Strong）。
- Prism 与 Lens 复合得到的约束是两者交集（更强），对应更「窄」的 optic（如部分字段上的仿射等）——细节见 Step 3 / 约束表。
- 本页只保证：**两个 Strong optic 用 `(.)` 仍是 Strong optic**。

---

## 8. 建议阅读

1. Step 2 源码注释 + 本文 §2–§3。  
2. 跑 `stack exec step2-strong-lens` 看组合段。  
3. VL 对照：[van-Laarhoven教程.md](van-Laarhoven教程.md) §3。  
4. Tambara：Step 4；existential：Step 5。

---

## 相关入口

- 代码：`app-step2/Main.hs`
- 对比：[Lens二形态对比.md](Lens二形态对比.md)
- 原理：[原理详解.md](原理详解.md)
- VL 组合：`docs/van-Laarhoven教程.md` §3
