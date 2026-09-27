# Lens 两种形态对比：(A) get/set vs (B) forall Strong

本文专门对比本仓库 Step 1 与 Step 2 的两种 `Lens` 写法。  
总原理见 [原理详解.md](原理详解.md)；速查见 [概念对照表.md](概念对照表.md)。

---

## 一览

| | **(A) 经典 get/set** | **(B) Profunctor optic（Strong）** |
|--|----------------------|-------------------------------------|
| **定义** | `data Lens s t a b = Lens { view :: s -> a, set :: s -> b -> t }` | `type Lens s t a b = forall p. Strong p => p a b -> p s t` |
| **源码** | [`app/Main.hs`](../app/Main.hs)（`step1-classic-lens`） | [`app-step2/Main.hs`](../app-step2/Main.hs)（`step2-strong-lens`） |
| **「透镜」是什么** | 一对具体函数 | 一段「对任意 Strong p 都成立」的抬变换 |
| **复合** | 手写 `compose`（分别拼 view / set） | 普通函数复合 `(.)` |
| **取运算** | 字段就在那儿：`view l` / `set l` | 换不同的 `p`：`Forget`→view，`(->)`→over/set |
| **通向 Prism 等** | 要另起一套 match/build 数据类型 | 改约束即可：`Choice`→Prism，`Profunctor`→Iso |
| **类型难度** | 低（rank-1） | 高（rank-2 `forall`） |

二者在**合法 Lens**上语义等价；双向转换见 Step 5（[`app-step5/Main.hs`](../app-step5/Main.hs)）。

---

## (A) 经典 get/set —— 优点与代价

### 定义（Step 1）

```haskell
data Lens s t a b = Lens
  { view :: s -> a
  , set  :: s -> b -> t
  }

_1 :: Lens (a, c) (b, c) a b
_1 = Lens { view = fst, set = \(_, c) b -> (b, c) }
```

### 优点

1. **直觉直接**：就是「取」和「放」，和面向对象里的 getter/setter 心理模型接近。
2. **定律好看**：三条定律直接写在 `view`/`set` 上（见 Step 1 的 `law1`–`law3`）。
3. **调试友好**：在 GHCi 里对某个 `Lens` 值看字段、写 QuickCheck，都很自然。
4. **无 rank-2**：初学者不会撞上「单态 `let` 卡死」的坑。

### 缺点

1. **复合啰嗦**：必须手写

   ```haskell
   compose (Lens v1 s1) (Lens v2 s2) = Lens
     { view = v2 . v1
     , set  = \s b -> s1 s (s2 (v1 s) b)
     }
   ```

   每多一种 optic（Prism、Traversal），就要再发明一套「如何复合」的公式。

2. **运算不开放**：想加 `over`、`traverseOf`、`foldMapOf`……每个都要新写，且与数据类型绑定。
3. **难统一层级**：Lens / Prism / Iso 看起来像三种无关的 data，看不出「约束在减弱/增强」。

### 小例子

```haskell
-- Step 1 demo 风格
view _1 (True, 42 :: Int)            -- True
set  _1 (True, 42) False             -- (False, 42)
view _cityOf alice                   -- "Shanghai"
```

适合：**第一次建立「焦点 / 上下文」直觉、验证定律**。

---

## (B) `forall p. Strong p => p a b -> p s t` —— 优点与代价

### 定义（Step 2）

```haskell
type Lens s t a b = forall p. Strong p => p a b -> p s t

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens get setP =
  dimap (\s -> (get s, s)) (\(b, s) -> setP s b) . first'

_1 :: Lens (a, c) (b, c) a b
_1 = lens fst (\(_, c) b -> (b, c))
```

读法：一个 Lens 是「**对任意** Strong 的 profunctor，都能把焦点上的 `p a b` 抬成整树上的 `p s t`」。

### 优点

1. **复合即 `(.)`**：`_cityOf = _address . _city`，因为两边都是 `p _ _ -> p _ _`。
2. **一种定义，多种运算**：不改 Lens 值，只换 `p` 的实例：

   | 选用的 `p` | 得到的运算 |
   |------------|------------|
   | `(->)` | `over` / `set` |
   | `Forget a` | `view` |

3. **层级统一**：把 `Strong` 换成 `Choice` 就是 Prism；只要 `Profunctor` 就是 Iso（Step 3 / 6）。这与 Tambara「换张量」是同一故事（Step 4）。
4. **与库一致**：`lens` / `optics` / `profunctor-optics` 的主编码就是这条路（Step 6 对照表）。

### 缺点

1. **概念负担**：要先懂 Profunctor、`dimap`、`first'`、`Forget`。
2. **rank-2 坑**：

   ```haskell
   -- 坏：let 绑成单态
   let l = lens fst (\(_,c) b -> (b,c))
   in view l (True, 1)     -- 常类型错误 / 推不出

   -- 好：保持多态，直接传
   view (lens fst (\(_,c) b -> (b,c))) (True, 1)
   ```

3. **「值」不透明**：GHCi 里看不到一对 get/set，要对着类型想「它能对哪些 p 工作」。

### 小例子

```haskell
-- Step 2 demo 风格
view _1 (True, 42 :: Int)            -- True
set  _1 False (True, 42)             -- (False, 42)  注意参数顺序与 (A) 不同！
over _2 (*10) (True, 42)             -- (True, 420)
view _cityOf alice                   -- "Shanghai"
```

注意：教学版 (A) 的 `set` 是 `s → b → t`（数据优先）；(B) 经 `over` 得到的库风格常是 `b → s → t`。本仓库 Step 2 的 `set l b s` 采用后者。

适合：**理解复合、准备接 Prism/Traversal、对接真实库**。

---

## 对照同一条语义

对 `_1`：

| 动作 | (A) Step 1 | (B) Step 2 |
|------|------------|------------|
| 读第一分量 | `view _1 (True,42)` | `view _1 (True,42)`（内部是 `Forget`） |
| 写第一分量 | `set _1 (True,42) False` | `set _1 False (True,42)` |
| 复合 | `compose _addr _city` | `_address . _city` |

从 (A) 造 (B)：`gsToOptic` / `lens get setP`（Step 2、5）。  
从 (B) 抽 (A)：`opticToGs`（Step 5）。  
经 existential 中转：`gsToEx` / `exToOptic`（Step 5）——看清「上下文类型 `c`」。

---

## 怎么选？

| 场景 | 更合适 |
|------|--------|
| 讲课第一小时、写定律、小脚本 | **(A)** |
| 要复合、要和 Prism/Iso 同一套语言、要对齐 Hackage | **(B)** |
| 弄清「为什么等价」 | 两者都写，再用 Step 5 round-trip |

本仓库的路线是 **先 (A) 后 (B)**，再在 Step 4–5 把 (B) 收进 Tambara / existential 图景。

---

## 相关入口

- 原理总文：[原理详解.md](原理详解.md) §2
- Step 1：`stack exec step1-classic-lens`
- Step 2：`stack exec step2-strong-lens`
- Step 5 round-trip：`stack exec step5-optic-tambara`
