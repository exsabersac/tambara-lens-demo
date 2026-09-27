# DaoFP 第 19 章：Tambara 推导（通俗重排）

本文定位：对照 Milewski *DaoFP* 第 19 章（Tambara Modules），把原文的动机 → Tannakian → Tambara → ∀↔∃ → 换张量这条线重排成更易跟的推导。  
与本仓库交叉链接：[原理详解.md](原理详解.md) §4–5、[学习路线.md](学习路线.md) Step 4–5、[Strong-Profunctor组合.md](Strong-Profunctor组合.md) §7；代码 [`app-step4/Main.hs`](../app-step4/Main.hs)、[`app-step5/Main.hs`](../app-step5/Main.hs)。

读者假定已读过 DaoFP / CTFP 或本仓库 Steps 1–3：本文澄清定义与边界，并把公式接到 Haskell，而不是从零讲范畴。读完应能说清一句话：

> `forall p. Strong p => p a b -> p s t` 恰好等于 existential lens `∃c. (s → c×a) × (c×b → t)`；`Strong` 就是积张量上的 **Tambara module**。

---

## 0. 这一章在解决什么

**直接陈述：** get/set（尤其 setter）复合别扭；把 lens 改写成「对一类 profunctor 多态的函数」后，复合就是普通的 `(.)`。本章要找出那一类 profunctor——**Tambara module**——并证明

```text
∫_{P : Tambara} Set(P⟨a,b⟩, P⟨s,t⟩)  ≅  ∫^c C(s, c×a) × C(c×b, t)
```

Haskell 侧即 `forall p. Strong p => p a b -> p s t ≅` existential / get-set lens。

**证据 / 动机。** 经典 `Lens` 的 getter 用函数复合即可；setter 要嵌套手写，existential 形 `∃c.…` 也没有变成「函数」。几何里旋转若用轴角公式复合很丑，换成矩阵/四元数就变成乘法——同样地，profunctor 表示让 optic 变成 `p a b → p s t` 形的函数，复合回到 `(.)`。Iso 只要裸 `Profunctor`；要得到真正的 Lens，必须给 `P` 加上「能把上下文 `c` 平行带进两边」的结构 α，那就是 Tambara。

目标一句话（后文主公式）：找出一类 profunctor（Tambara / Strong），使得 `forall p. Tambara p => p a b -> p s t` 恰好等于 existential lens。

---

## 1. 热身：用「全部表示」重建箭头（Tannakian）

**直接陈述（主公式）：**

```text
∫_{F : [C,Set]} Set(F a, F b)  ≅  C(a,b)
```

单看某一个 functors 的底层集合不够重建箭头；必须同时看全体 co-presheaf 范畴 `[C,Set]`，以及它们之间的自然变换（equivariant maps）。左端是「对所有结构相容的表示，凡 `a` 在则 `b` 在」的证明集合；这恰好当且仅当存在箭头 `a → b`。

### 1.1 为何单表示不够

Monoid 可看成单对象范畴 `M`（唯一对象 `*`，hom-set 即 monoid 元素）。表示是 functor `F : M → Set`：把 `*` 映到集合 `S`，把乘法映成 `S → S` 的复合。单个 `S` 几乎总在「作弊」——可能把整个 monoid 压成 `id_S`——所以从底层集合重建不出 `M`。要重建，必须看全体表示形成的 functor 范畴 `[M,Set]`，以及 fiber functor `fib F = F*`；自然变换分量正是 equivariant maps：`α ∘ F m = G m ∘ α`。

### 1.2 证明相关直觉（子集语言）

`Set`-值 functor 可看成与范畴结构相容的 **proof-relevant subset**：`a` 属于该子集当且仅当 `Fa` 非空；箭头 `f : a → b` 给出 `Ff : Fa → Fb`，把「`a` 在」的证明送到「`b` 在」的证明。于是主公式左端的一个元素是：对每一个这样的子集，若 `a` 在则 `b` 在。这只可能当存在 `a → b`。

形式证明走两次 Yoneda：先把 `Fa ≅ [C,Set](C(a,-), F)`，再对 functor 范畴用 Yoneda 推论，得到 `C(a,b)`。wedge 条件通过自然变换进入 end——这正是「全体表示一起约束」的地方。

### 1.3 Haskell：Getter 的前身

```haskell
toTannaka :: (a -> b) -> (forall f. Functor f => f a -> f b)
toTannaka g = fmap g

fromTannaka :: (forall f. Functor f => f a -> f b) -> (a -> b)
fromTannaka g a = runIdentity (g (Identity a))

type Getter a b = forall f. Functor f => f a -> f b
```

`forall f. Functor f => f a → f b ≅ a → b`。唯一（参数多态下）的实现是偷偷抓住一个 `a→b` 再 `fmap`；用 `Identity` 取回。这就是 **Getter**：说明 `a` 里有足够信息构造 `b`。复合仍是 `(.)`：

```haskell
boolToStrGetter = toTannaka show . toTannaka (bool (-1) 1)
```

Getter 是最简 optic；其它 optic 的 get/set 复合别扭，但它们的 functor / profunctor 表示同样用 `(.)` 复合——这正是第 0 节动机的预演。

### 1.4 带 free/forgetful 时的总引擎（optics 的骨架）

若 `T` 是带额外结构的 functor 范畴，且有 free/forgetful 伴随 `F ⊣ U`（`T ⇄ [C,Set]`），同一套路给出

```text
∫_{P : T} Set((U P) a, (U P) s)  ≅  (Φ Y^a) s
```

其中 `Φ = U ∘ F` 是 monad，`Y^a = C(a,-)`。optics 推导里把对象换成对 `⟨a,b⟩`、`⟨s,t⟩`，functors 换成 profunctors，`T` 换成 Tambara 范畴——右端就会变成 existential lens。**这是整章的总引擎**；后文 §4 只是把它实例化。

<details>
<summary>附录直觉：Cayley / DList（压成旁支，不占主线）</summary>

Cayley：每个 monoid 同构于某组自函数（post-composition 表示）。Haskell 里 list monoid 的 Cayley 形是 difference list `DList a = [a] → [a]`，`rep as = (as ++)`，把 `O(N²)` 的 `reverse` 变成线性。这与「用全体表示重建」同属表示论家族，但 **不是** optics 主公式的必要步骤；读原文时可扫过，不必在推导链上停留。

</details>

---

## 2. 为何 Lens 要看 Profunctor

**直接陈述：** 类型变化 lens 的 hom-set 是 coend

```text
L⟨s,t⟩⟨a,b⟩  =  ∫^c C(s, c×a) × C(c×b, t)
```

可写成积范畴 `C^op × C` 上的「带作用」hom：

```text
c • ⟨a,b⟩  =  ⟨c×a, c×b⟩
L⟨s,t⟩⟨a,b⟩  =  ∫^c (C^op × C)(c • ⟨a,b⟩, ⟨s,t⟩)
```

因此表示应在 **profunctors**（`C^op × C → Set` 的 co-presheaves）上做 Tannakian，而不是普通 functors。

### 2.1 Iso 热身（无额外结构）

对 `T = [C^op × C, Set]`（裸 Profunctor，无 Tambara），主引擎退化成普通 Tannakian：

```text
∫_P Set(P⟨a,b⟩, P⟨s,t⟩)  ≅  C(s,a) × C(b,t)
```

Haskell：

```haskell
type Iso  s t a b = (s -> a, b -> t)
type IsoP s t a b = forall p. Profunctor p => p a b -> p s t

toIsoP (f, g) = dimap f g
```

「对每个 profunctor 都能把 `P⟨a,b⟩` 抬到 `P⟨s,t⟩`」的唯一办法，是手里握着一对 `(s→a, b→t)`。Iso **没有留下的上下文 `c`**，所以不需要 Strong/Choice（对照本仓库 Step 6、原理详解 §6.3）。

### 2.2 从 existential 出发缺什么

手上有 `⟨f,g⟩ : C(s, c×a) × C(c×b, t)`。想对任意合适的 `P` 造出 `P⟨a,b⟩ → P⟨s,t⟩`：

1. 若已有 `P⟨c×a, c×b⟩`，则 `P⟨f,g⟩`（即 `dimap`）给出 `P⟨s,t⟩`；
2. **缺口**是 `P⟨a,b⟩ → P⟨c×a, c×b⟩`。

下一节把这个缺口立成定义。

---

## 3. 缺口与 Tambara module

**直接陈述：** Tambara module（相对笛卡尔积）是带有一族变换

```text
α_{⟨a,b⟩,c} : P⟨a,b⟩ → P⟨c×a, c×b⟩
```

的 profunctor，满足 dinaturality 与幺半相干；态射是与 α 交换的自然变换。Haskell 里这就是 `Strong` / `Cartesian`。

### 3.1 定义与 dinaturality

`c` 同时出现在反变与协变位置，故对 `h : c → c'` 的自然性必须改成 **dinatural**（对角自然）：α 给出的是更一般对象 `P⟨c'×a, c×b⟩` 的对角分量。教学上够用的图是：从 `P⟨a,b⟩` 经 `α_c` 与 `α_{c'}` 两条路走到 `P⟨c×a, c'×b⟩`，用 `P` 作用在 `h×id` 上使两路相等。不必抄满原文所有交换图；记住「α 对上下文参数是 dinatural」即可。

### 3.2 幺半相干

- 单位：`α_{⟨a,b⟩, 1} = id`（`1` 为终端对象 / 积单位）；
- 结合：`α_{⟨a,b⟩, c'×c} ≅ α_{⟨c×a,c×b⟩, c'} ∘ α_{⟨a,b⟩, c}`（隐含结合子）。

### 3.3 态射

Tambara 之间的态射 `ρ : (P,α) → (Q,β)` 是自然变换，且与 α 交换：先 α 再 ρ 等于先 ρ 再 β。**Tambara 范畴的箭头结构**正是后文 end 的 wedge 条件来源——这决定了「对所有 Tambara 量化」长什么样。

### 3.4 Haskell

```haskell
class Profunctor p => Strong p where   -- 文献亦称 Cartesian
  first'  :: p a b -> p (c, a) (c, b)  -- ≈ α（左积）
  -- second' 可由 swap 推出；本仓库 Step 4 的 introduce ≈ second'

-- DaoFP 原文记号：
-- class Profunctor p => Cartesian p where
--   alpha :: p a b -> p (c, a) (c, b)
```

本仓库统一写法（Step 4）：

```haskell
class Profunctor p => Tambara ten p where
  introduce :: p a b -> p (ten c a) (ten c b)

-- Strong p  ≅  Tambara (,) p      （introduce = second'）
-- Choice p  ≅  Tambara Either p   （introduce = right'）
```

参数多态已保证相关自然性；相干律在实例里由积/和的单位与结合保证。

### 3.5 划界表：Tambara/Strong vs Functor strength

（对齐 [原理详解.md](原理详解.md) §4.2）

| | **Profunctor / Tambara 强度**（本章与本仓库） | **Functor / Applicative strength** |
|--|-----------------------------------------------|-------------------------------------|
| 典型类型 | `p a b → p (c,a) (c,b)` | `f a → f (c,a)` 或 `(c, f a) → f (c,a)` |
| 作用对象 | **Profunctor**（两参数，左反右正） | **Functor**（一参数） |
| 光学角色 | 定义 Lens/Prism 的「能带上下文」 | 单子/应用函子、另一套遍历故事 |
| Haskell 名 | `Strong` / `Choice` / `Tambara ten` | 常称 strength，与 `Data.Functor` 相关 |

名字都有 strength，**不是同一个东西**。见 `Strong` 就想 Tambara_(,)，不要想成 `f a → f (c,a)`。

---

## 4. 主公式：∀ Tambara ↔ existential Lens

**直接陈述：**

```text
∫_{P : Tambara} Set(P⟨a,b⟩, P⟨s,t⟩)
  ≅  ∫^c C(s, c×a) × C(c×b, t)
```

左边是「Tambara 态射」侧（Haskell：`forall p. Strong p => …`）；右边是 existential / coend 侧。二者同构——这就是 profunctor lens 的正当性。

### 4.1 三步路线图（读者不必跟完所有 end 演算）

1. **Comonad Θ。** 在 profunctor 范畴上定义  
   `(Θ P)⟨a,b⟩ = ∫_c P⟨c×a, c×b⟩`。  
   其 **coalgebras** `P → Θ P` 恰好是一族 α——即 Tambara modules。更强地，它们是 Θ 的 Eilenberg–Moore coalgebras，故 Tambara 范畴 = EM(Θ)。

2. **伴随 monad Φ。** Θ 的左伴随是 monad  
   `(Φ P)⟨s,t⟩ = ∫^{u,v,c} (C^op×C)(c•⟨u,v⟩, ⟨s,t⟩) × P⟨u,v⟩`。  
   EM(Φ) 与 EM(Θ) 相同，于是得到 free/forgetful `F ⊣ U`，且 `Φ = U∘F`——正是 §1.4 总引擎需要的伴随。

3. **作用在 representable 上。** 把 `Φ` 作用在 `(C^op×C)(⟨a,b⟩, -)` 上，再在 `⟨s,t⟩` 求值；co-Yoneda 消掉多余变量后得到  
   `∫^c C(s, c×a) × C(c×b, t)`——existential lens。

把这三步代入 §1.4 的骨架公式，即得本节开头的同构。细节 end 演算可回原文；教学上抓住「Θ 的 coalgebra = Tambara；Φ(representable) = existential」即可。

### 4.2 Haskell：构造、取回、复合

```haskell
type LensP s t a b = forall p. Strong p => p a b -> p s t

-- existential → profunctor（DaoFP：toLensP；本仓库：exToOptic）
toLensP (from, to) = dimap from to . first'   -- 或 . alpha / introduceFirst

-- 取回 get/set：把 get/set 自己做成 Strong profunctor（FlipLens）
data FlipLens a b s t = FlipLens (s -> a) (s -> b -> t)

instance Profunctor (FlipLens a b) where
  dimap f g (FlipLens get set) =
    FlipLens (get . f) (fmap g . set . f)

instance Strong (FlipLens a b) where
  first' (FlipLens get set) = FlipLens get' set'
    where
      get' (c, s) = get s          -- 或 get . snd，视 first'/second' 约定
      set' (c, s) b = (c, set s b)

fromLensP pp =
  let FlipLens get' set' = pp (FlipLens id (\_ b -> b))
  in (get', set')
```

复合：两个 `LensP` 都是函数，中间类型对接即 `(.)`——第 0 节承诺兑现。

### 4.3 对照本仓库 Step 5

| 方向 | 本仓库函数 | 含义 |
|------|------------|------|
| get/set → ∃ | `gsToEx` | 取 `c := s` |
| ∃ → get/set | `exToGs` | `view = snd∘out` 等 |
| ∃ → ∀ Strong | `exToOptic` | `dimap out inn . first'`（= DaoFP `toLensP`） |
| get/set → ∀ | `gsToOptic` | Step 2 的 `lens` |
| ∀ → get/set | `opticToGs` | 用 `Forget` 与 `(->)`（或 FlipLens）取出 |

三条编码 round-trip：`rtGsEx` / `rtGsOptic` / `rtFull`。详见 [原理详解.md](原理详解.md) §5。

---

## 5. 换张量 → 整族 optic

**直接陈述：** Tambara 原先对任意 monoidal 张量 `⊗` 定义：`α : P⟨a,b⟩ → P⟨c⊗a, c⊗b⟩`。推导一字不改；换张量就换 optic。

| 张量 / 作用 | Tambara ≈ | Optic | existential 要点 |
|-------------|-----------|-------|------------------|
| product `(,)` | `Strong` / `Cartesian` | **Lens** | `∫^c C(s,c×a)×C(c×b,t)`；焦点总在 |
| coproduct `Either` | `Choice` / `Cocartesian` | **Prism** | `∫^c C(s,c+a)×C(c+b,t) ≅ C(s,t+a)×C(b,t)`；`match`/`build` |
| 仅 Profunctor（无 α） | — | **Iso** | `C(s,a)×C(b,t)`；无上下文 |
| 序列 / 幂级数作用 `c•a = Σ_m c_m × a^m` | Traversing（推广 Tambara） | **Traversal** | 多焦点；`n` 与残差 `c_n` 一起藏在 coend；DaoFP 用 `[N,C]` 上 Day 卷积给幺半结构 |
| 两范畴上的作用 | mixed Tambara | **mixed optics** | `∫^m C(s,m•a)×D(m•b,t)`；`P : C^op×D→Set` |

### 5.1 Prism 要点（和张量）

```haskell
match :: s -> Either t a
build :: b -> t

class Profunctor p => Choice p where
  right' :: p a b -> p (Either c a) (Either c b)

type PrismP s t a b = forall p. Choice p => p a b -> p s t
toPrismP (Prism from to) = dimap from to . right'
```

existential：`s` 要么给出焦点 `a`，要么给出残差 `c`；`t` 可由新焦点 `b` 或同一残差装回。本仓库 `ForgetM` 做 `preview`（Step 3）；`_Just` round-trip 见 Step 5。

### 5.2 Traversal 与 mixed（略写）

Traversal 要同时处理「`n` 个焦点」，类型安全需要依赖类型或把长度写进 existential。范畴侧对每个 `n` 有残差 `c_n`，作用 `c • a = Σ_m c_m × a^m`，在 `[N,C]` 上用 Day 卷积得到幺半结构；推广 Tambara 后 ∀ 侧仍成立。Mixed optics 允许左右两边活在不同范畴、共享同一个 monoidal 作用者 `M`（actegory）。本仓库 Step 3 对 Traversal 仅占位；细节回原文或专文。

---

## 6. 与本仓库对照 + 易混边界

### 6.1 步骤指针

| 论题 | 文档 | 代码 |
|------|------|------|
| get/set、定律 | 原理详解 §1；学习路线 Step 1 | `app/Main.hs` |
| `forall Strong`、Forget | 原理详解 §3；Strong-Profunctor组合 | `app-step2/Main.hs` |
| 约束表 Lens/Prism/Iso | 概念对照表；学习路线 Step 3 | `app-step3/Main.hs` |
| Tambara ≅ Strong/Choice | 原理详解 §4；**本文 §3** | `app-step4/Main.hs` |
| ∃ ↔ ∀ round-trip | 原理详解 §5；**本文 §4** | `app-step5/Main.hs` |
| 库名 / Iso | 原理详解 §6.3 | `app-step6/Main.hs` |

### 6.2 易混边界表

| 易混对 | 界限 |
|--------|------|
| **get/set vs Strong vs VL** | (A) 数据构造器；(B) `forall Strong`；(C) `forall Functor f => (a→f b)→s→f t`。语义等价（合法 lens 上）；复合在 (B)(C) 都是 `(.)`。见 [Lens二形态对比.md](Lens二形态对比.md) |
| **Strong ≠ Functor strength** | 见 §3.5；原理详解 §4.2 |
| **Forget vs ForgetM** | `Forget r`（`a→r`）+ Strong → `view`；`ForgetM r`（`a→Maybe r`）+ Choice → `preview`。不要给裸 Forget 硬上 Choice |
| **Iso vs Lens** | Iso 无上下文、只要 Profunctor；Lens 需要积上 Tambara（Strong） |
| **existential `c` vs 类型参数 `s`** | `gsToEx` 常取 `c:=s` 作代表元；一般 `c` 是「真正的残差」，同构不唯一到代表元选取 |
| **本文 vs 原理详解** | 原理详解走仓库代码链；本文走 DaoFP 范畴推导链。交汇点是 Strong≅Tambara 与 ∃↔∀ |

---

## 7. 读原文章节地图

| DaoFP Ch.19 原文 | 本文 |
|------------------|------|
| 章首动机（get/set 复合 vs profunctor `(.)`） | §0 |
| § Tannakian Reconstruction（monoid 表示、Cayley/DList、重建公式、Yoneda 证明、Haskell Getter、带伴随的 Φ 公式） | §1（Cayley/DList → 附录） |
| § Profunctor Lenses · Iso | §2 |
| 缺口；Tambara module（α、dinatural、相干、态射） | §3 |
| Profunctor lenses 公式；Θ / Φ；Haskell Cartesian + FlipLens | §4 |
| § General Optics（⊗、Prism、Traversal） | §5 |
| § Mixed Optics | §5 表末行 |
| （无专节）与手写 demo 对照 | §6 |
| （无专节）章节地图 | §7（本表） |

---

## 延伸阅读

1. Bartosz Milewski — *DaoFP* Chapter 19（Tambara Modules）；博客 Profunctor Optics / Tambara 系列  
2. Pickering, Gibbons, Wu — *Profunctor Optics: Modular Data Accessors*  
3. 本仓库：[原理详解.md](原理详解.md) §4–5；[Strong-Profunctor组合.md](Strong-Profunctor组合.md) §7；[学习路线.md](学习路线.md) Step 4–5；[`app-step4`](../app-step4/Main.hs) / [`app-step5`](../app-step5/Main.hs)  
4. Hackage：`lens`、`optics`、`profunctors`（读 `Strong`/`Choice` 类型，对照手写版）
