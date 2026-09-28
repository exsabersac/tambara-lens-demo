# DaoFP 第 19 章：Tambara 推导（通俗重排）

本文定位：对照 Milewski *DaoFP* 第 19 章（Tambara Modules），把原文的动机 → Tannakian → Tambara → ∀↔∃ → 换张量这条线重排成更易跟的推导。  
与本仓库交叉链接：[原理详解.md](原理详解.md) §4–5、[学习路线.md](学习路线.md) Step 4–5、[Strong-Profunctor组合.md](Strong-Profunctor组合.md) §7；代码 [`app-step4/Main.hs`](../app-step4/Main.hs)、[`app-step5/Main.hs`](../app-step5/Main.hs)。

读者假定已读过 DaoFP / CTFP 或本仓库 Steps 1–3：本文澄清定义与边界，并把公式接到 Haskell，而不是从零讲范畴。读完应能说清一句话：

> `forall p. Strong p => p a b -> p s t` 恰好等于 existential lens \(\exists c.\; \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)\)；`Strong` 就是积张量上的 **Tambara module**。

---

## 0. 这一章在解决什么

**直接陈述：** get/set（尤其 setter）复合别扭；把 lens 改写成「对一类 profunctor 多态的函数」后，复合就是普通的 `(.)`。本章要找出那一类 profunctor——**Tambara module**——并证明

$$
\int_{P : \mathrm{Tambara}} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
  \;\cong\;
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
$$

Haskell 侧即 `forall p. Strong p => p a b -> p s t` ≅ existential / get-set lens。

**证据 / 动机。** 经典 `Lens` 的 getter 用函数复合即可；setter 要嵌套手写，existential 形 \(\exists c.\ldots\) 也没有变成「函数」。几何里旋转若用轴角公式复合很丑，换成矩阵/四元数就变成乘法——同样地，profunctor 表示让 optic 变成 \(p\,a\,b \to p\,s\,t\) 形的函数，复合回到 `(.)`。Iso 只要裸 `Profunctor`；要得到真正的 Lens，必须给 \(P\) 加上「能把上下文 \(c\) 平行带进两边」的结构 \(\alpha\)，那就是 Tambara。

目标一句话（后文主公式）：找出一类 profunctor（Tambara / Strong），使得 `forall p. Tambara p => p a b -> p s t` 恰好等于 existential lens。

---

## 1. 热身：用「全部表示」重建箭头（Tannakian）

<a id="sec-copresheaf"></a>

### 1.0 co-presheaf 范畴（[C, Set]）

**直接陈述：** **co-presheaf 范畴**（co-presheaf category）就是函子范畴 \([\mathcal{C},\mathrm{Set}]\)：对象是协变函子 \(F : \mathcal{C} \to \mathrm{Set}\)，态射是自然变换。相对 **presheaf** 范畴 \([\mathcal{C}^{\mathrm{op}},\mathrm{Set}]\) 而言，定义域不取 opposite，故称 “co”。Tannakian 重建、Iso / Lens 的 ∀ 侧，都是在这类函子范畴（或其带结构的子范畴）上取 end。

#### 对照表：presheaf vs co-presheaf

| | **presheaf** | **co-presheaf** |
|--|--------------|-----------------|
| 函子 | \(F : \mathcal{C}^{\mathrm{op}} \to \mathrm{Set}\)（反变） | \(F : \mathcal{C} \to \mathrm{Set}\)（协变） |
| 函子范畴 | \([\mathcal{C}^{\mathrm{op}},\mathrm{Set}]\) | \([\mathcal{C},\mathrm{Set}]\) |
| 代表元（Yoneda） | \(Y_a = \mathcal{C}(-,a)\) | \(Y^{a} = \mathcal{C}(a,-)\) |
| 在本仓库 / DaoFP 中的角色 | 常作背景对照 | Tannakian 表示侧；profunctor 是 \(\mathcal{C}^{\mathrm{op}}\times\mathcal{C}\) 上的 co-presheaf |

后文凡写 \([\mathcal{C},\mathrm{Set}]\) 或「表示范畴」，默认指 co-presheaf 侧。

#### Yoneda embedding、Yoneda lemma、为何是 Tannakian 的舞台

Yoneda embedding 把对象 \(a\) 映到 representable co-presheaf

$$
Y^{a} \;=\; \mathcal{C}(a,-) \;:\; \mathcal{C} \to \mathrm{Set}
$$

Yoneda lemma：对任意 \(F : \mathcal{C} \to \mathrm{Set}\)，

$$
F a \;\cong\; [\mathcal{C},\mathrm{Set}]\big(Y^{a},\, F\big)
$$

即「在 \(a\) 处取值」同构于「从 representable \(Y^{a}\) 出发的自然变换」。Tannakian 主公式正是在 \([\mathcal{C},\mathrm{Set}]\) 上对所有 \(F\) 取 end：

$$
\int_{F : [\mathcal{C},\mathrm{Set}]} \mathrm{Set}(F a, F b) \;\cong\; \mathcal{C}(a,b)
$$

证明走两次 Yoneda（见 §1.2）：先用 lemma 把 \(Fa\) 换成 \([\mathcal{C},\mathrm{Set}](Y^{a}, F)\)，再对函子范畴用 Yoneda 推论得到 \(\mathcal{C}(a,b)\)。因此 **co-presheaf 范畴是重建箭头的舞台**：对象提供表示，态射（自然变换）提供 equivariant 约束，end 把「全体表示一起」收成 hom-set。

#### Fiber functor

固定对象 \(a\)，**fiber functor**（纤维函子）是求值

$$
\mathrm{fib}_{a} : [\mathcal{C},\mathrm{Set}] \to \mathrm{Set},\qquad F \mapsto F a
$$

Monoid 特例（单对象 \(\mathcal{M}\)）里常写 \(\mathrm{fib}\, F = F*\)。主公式左端可看作：对所有 \(F\)，从 \(\mathrm{fib}_{a} F\) 到 \(\mathrm{fib}_{b} F\) 的、与自然变换相容的一族映射——即 fiber 之间的 equivariant maps。单看某一个 \(Fa\) 不够重建；必须连同全体 \(F\) 与它们之间的自然变换一起看。

#### 为何在 optics / Tambara 中反复出现

同一舞台换底范畴 / 换子范畴，就是整章的升级路径：

1. **普通 Tannaka：** \(T = [\mathcal{C},\mathrm{Set}]\)（裸 co-presheaves）。End 重建 \(\mathcal{C}(a,b)\)；Haskell 侧即 `forall f. Functor f => f a -> f b`（Getter，§1.3）。
2. **Profunctor 情形：** 把 \(\mathcal{C}\) 换成 \(\mathcal{C}^{\mathrm{op}}\times\mathcal{C}\)。该积范畴上的 co-presheaves 恰是 **profunctors** \(P : \mathcal{C}^{\mathrm{op}}\times\mathcal{C}\to\mathrm{Set}\)。裸 Profunctor 上的 Tannakian 给出 Iso（§2.1）。
3. **Tambara：** 不再对全体 profunctor 取 end，而对带 strength \(\alpha\) 的子范畴（Tambara modules）取 end。Forgetful \(U\) 忘掉 \(\alpha\)；free \(F\)（Pastro 构造）自由添加 strength；monad \(\Phi = U \circ F\)。代入 §1.4 总引擎，右端变成 existential lens（§4）。

链路一句话：co-presheaf →（换底）profunctor →（加 \(\alpha\)、free/forget）Tambara。

#### Haskell 对照（短表）

| 范畴侧 | Haskell 侧 |
|--------|------------|
| \(F : \mathcal{C}\to\mathrm{Set}\)（co-presheaf） | `Functor f`；值 \(F a\) 写作 `f a` |
| \(\int_F \mathrm{Set}(Fa,Fb)\) | `forall f. Functor f => f a -> f b` |
| \(P : \mathcal{C}^{\mathrm{op}}\times\mathcal{C}\to\mathrm{Set}\) | `Profunctor p`；值 \(P\langle a,b\rangle\) 写作 `p a b` |
| 带 \(\alpha\) 的 Tambara | `Strong p`（积）/ `Choice p`（和） |
| \(\int_{P:\mathrm{Tambara}}\mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)\) | `forall p. Strong p => p a b -> p s t` |

范畴在前；Haskell 只是 end / 多态的记法对照。细节实现见 §1.3、§2.1、§4.2。

**直接陈述（主公式）：**

$$
\int_{F : [\mathcal{C},\mathrm{Set}]} \mathrm{Set}(F a, F b)
  \;\cong\;
\mathcal{C}(a,b)
$$

单看某一个 functors 的底层集合不够重建箭头；必须同时看全体 co-presheaf 范畴 \([\mathcal{C},\mathrm{Set}]\)，以及它们之间的自然变换（equivariant maps）。左端是「对所有结构相容的表示，凡 \(a\) 在则 \(b\) 在」的证明集合；这恰好当且仅当存在箭头 \(a \to b\)。

### 1.1 为何单表示不够

Monoid 可看成单对象范畴 \(\mathcal{M}\)（唯一对象 \(*\)，hom-set 即 monoid 元素）。表示是 functor \(F : \mathcal{M} \to \mathrm{Set}\)：把 \(*\) 映到集合 \(S\)，把乘法映成 \(S \to S\) 的复合。单个 \(S\) 几乎总在「作弊」——可能把整个 monoid 压成 \(\mathrm{id}_S\)——所以从底层集合重建不出 \(\mathcal{M}\)。要重建，必须看全体表示形成的 functor 范畴 \([\mathcal{M},\mathrm{Set}]\)，以及 fiber functor \(\mathrm{fib}\, F = F*\)；自然变换分量正是 equivariant maps：\(\alpha \circ F m = G m \circ \alpha\)。

### 1.2 证明相关直觉（子集语言）

\(\mathrm{Set}\)-值 functor 可看成与范畴结构相容的 **proof-relevant subset**：\(a\) 属于该子集当且仅当 \(Fa\) 非空；箭头 \(f : a \to b\) 给出 \(Ff : Fa \to Fb\)，把「\(a\) 在」的证明送到「\(b\) 在」的证明。于是主公式左端的一个元素是：对每一个这样的子集，若 \(a\) 在则 \(b\) 在。这只可能当存在 \(a \to b\)。

形式证明走两次 Yoneda：先把 \(Fa \cong [\mathcal{C},\mathrm{Set}](\mathcal{C}(a,-), F)\)，再对 functor 范畴用 Yoneda 推论，得到 \(\mathcal{C}(a,b)\)。wedge 条件通过自然变换进入 end——这正是「全体表示一起约束」的地方。

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

若 \(T\) 是带额外结构的 functor 范畴，且有 free/forgetful 伴随 \(F \dashv U\)（\(T \rightleftarrows [\mathcal{C},\mathrm{Set}]\)），同一套路给出

$$
\int_{P : T} \mathrm{Set}((U P) a, (U P) s)
  \;\cong\;
(\Phi Y^{a})\, s
$$

其中 \(\Phi = U \circ F\) 是 monad，\(Y^{a} = \mathcal{C}(a, -)\)（Yoneda；\(U P\) 为 forgetful 应用到 \(P\)）。optics 推导里把对象换成对 \(\langle a,b\rangle\)、\(\langle s,t\rangle\)，functors 换成 profunctors，\(T\) 换成 Tambara 范畴——右端就会变成 existential lens。**这是整章的总引擎**；后文 §4 只是把它实例化。

> **附录直觉：Cayley / DList**（压成旁支，不占主线）
>
> Cayley：每个 monoid 同构于某组自函数（post-composition 表示）。Haskell 里 list monoid 的 Cayley 形是 difference list `DList a = [a] → [a]`，`rep as = (as ++)`，把 `O(N²)` 的 `reverse` 变成线性。这与「用全体表示重建」同属表示论家族，但 **不是** optics 主公式的必要步骤；读原文时可扫过，不必在推导链上停留。

---

## 2. 为何 Lens 要看 Profunctor

**直接陈述：** 类型变化 lens 的 hom-set 是 coend

$$
\mathcal{L}\langle s,t\rangle\langle a,b\rangle
  \;=\;
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
$$

可写成积范畴 \(\mathcal{C}^{\mathrm{op}} \times \mathcal{C}\) 上的「带作用」hom：

$$
c \bullet \langle a,b\rangle \;=\; \langle c\times a,\; c\times b\rangle
$$

$$
\mathcal{L}\langle s,t\rangle\langle a,b\rangle
  \;=\;
\int^{c} (\mathcal{C}^{\mathrm{op}} \times \mathcal{C})(c \bullet \langle a,b\rangle, \langle s,t\rangle)
$$

因此表示应在 **profunctors**（\(\mathcal{C}^{\mathrm{op}} \times \mathcal{C} \to \mathrm{Set}\) 的 co-presheaves）上做 Tannakian，而不是普通 functors。

### 2.1 Iso 热身（无额外结构）

对 \(T = [\mathcal{C}^{\mathrm{op}} \times \mathcal{C}, \mathrm{Set}]\)（裸 Profunctor，无 Tambara），主引擎退化成普通 Tannakian：

$$
\int_{P} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
  \;\cong\;
\mathcal{C}(s,a) \times \mathcal{C}(b,t)
$$

Haskell：

```haskell
type Iso  s t a b = (s -> a, b -> t)
type IsoP s t a b = forall p. Profunctor p => p a b -> p s t

toIsoP (f, g) = dimap f g
```

「对每个 profunctor 都能把 \(P\langle a,b\rangle\) 抬到 \(P\langle s,t\rangle\)」的唯一办法，是手里握着一对 \((s\to a,\, b\to t)\)。Iso **没有留下的上下文 \(c\)**，所以不需要 Strong/Choice（对照本仓库 Step 6、原理详解 §6.3）。

### 2.2 从 existential 出发缺什么

手上有 \(\langle f,g\rangle : \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)\)。想对任意合适的 \(P\) 造出 \(P\langle a,b\rangle \to P\langle s,t\rangle\)：

1. 若已有 \(P\langle c\times a, c\times b\rangle\)，则 \(P\langle f,g\rangle\)（即 `dimap`）给出 \(P\langle s,t\rangle\)；
2. **缺口**是 \(P\langle a,b\rangle \to P\langle c\times a, c\times b\rangle\)。

下一节把这个缺口立成定义。

---

## 3. 缺口与 Tambara module

**直接陈述：** Tambara module（相对笛卡尔积）是带有一族变换

$$
\alpha_{\langle a,b\rangle,c} : P\langle a,b\rangle \to P\langle c\times a,\, c\times b\rangle
$$

的 profunctor，满足 dinaturality 与幺半相干；态射是与 \(\alpha\) 交换的自然变换。Haskell 里这就是 `Strong` / `Cartesian`。

### 3.1 定义与 dinaturality

\(c\) 同时出现在反变与协变位置，故对 \(h : c \to c'\) 的自然性必须改成 **dinatural**（对角自然）：\(\alpha\) 给出的是更一般对象 \(P\langle c'\times a, c\times b\rangle\) 的对角分量。教学上够用的图是：从 \(P\langle a,b\rangle\) 经 \(\alpha_c\) 与 \(\alpha_{c'}\) 两条路走到 \(P\langle c\times a, c'\times b\rangle\)，用 \(P\) 作用在 \(h\times\mathrm{id}\) 上使两路相等。不必抄满原文所有交换图；记住「\(\alpha\) 对上下文参数是 dinatural」即可。

### 3.2 幺半相干

- 单位（\(1\) 为终端对象 / 积单位）：

$$
\alpha_{\langle a,b\rangle,\, 1} \;=\; \mathrm{id}
$$

- 结合（隐含结合子）：

$$
\alpha_{\langle a,b\rangle,\, c'\times c}
  \;\cong\;
\alpha_{\langle c\times a,\, c\times b\rangle,\, c'}
  \circ
\alpha_{\langle a,b\rangle,\, c}
$$

### 3.3 态射

Tambara 之间的态射 \(\rho : (P,\alpha) \to (Q,\beta)\) 是自然变换，且与 \(\alpha\) 交换：先 \(\alpha\) 再 \(\rho\) 等于先 \(\rho\) 再 \(\beta\)。**Tambara 范畴的箭头结构**正是后文 end 的 wedge 条件来源——这决定了「对所有 Tambara 量化」长什么样。

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
| 典型类型 | \(p\,a\,b \to p\,(c,a)\,(c,b)\) | \(f\,a \to f\,(c,a)\) 或 \((c, f\,a) \to f\,(c,a)\) |
| 作用对象 | **Profunctor**（两参数，左反右正） | **Functor**（一参数） |
| 光学角色 | 定义 Lens/Prism 的「能带上下文」 | 单子/应用函子、另一套遍历故事 |
| Haskell 名 | `Strong` / `Choice` / `Tambara ten` | 常称 strength，与 `Data.Functor` 相关 |

名字都有 strength，**不是同一个东西**。见 `Strong` 就想 `Tambara (,) p`，不要想成 `f a → f (c,a)`。

---

## 4. 主公式：∀ Tambara ↔ existential Lens

**直接陈述：**

$$
\int_{P : \mathrm{Tambara}} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
  \;\cong\;
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
$$

左边是「Tambara 态射」侧（Haskell：`forall p. Strong p => …`）；右边是 existential / coend 侧。二者同构——这就是 profunctor lens 的正当性。

### 4.1 三步路线图（读者不必跟完所有 end 演算）

1. **Comonad \(\Theta\)。** 在 profunctor 范畴上定义

$$
(\Theta P)\langle a,b\rangle \;=\; \int_{c} P\langle c\times a,\, c\times b\rangle
$$

   其 **coalgebras** \(P \to \Theta P\) 恰好是一族 \(\alpha\)——即 Tambara modules。更强地，它们是 \(\Theta\) 的 Eilenberg–Moore coalgebras，故 Tambara 范畴 = EM(\(\Theta\))。

2. **伴随 monad \(\Phi\)。** \(\Theta\) 的左伴随是 monad

$$
(\Phi P)\langle s,t\rangle
  \;=\;
\int^{u,v,c}
  (\mathcal{C}^{\mathrm{op}}\times\mathcal{C})(c \bullet \langle u,v\rangle, \langle s,t\rangle)
  \times P\langle u,v\rangle
$$

   EM(\(\Phi\)) 与 EM(\(\Theta\)) 相同，于是得到 free/forgetful \(F \dashv U\)，且 \(\Phi = U \circ F\)——正是 §1.4 总引擎需要的伴随。

3. **作用在 representable 上。** 把 \(\Phi\) 作用在 \((\mathcal{C}^{\mathrm{op}} \times \mathcal{C})(\langle a,b\rangle, -)\) 上，再在 \(\langle s,t\rangle\) 求值；co-Yoneda 消掉多余变量后得到

$$
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
$$

   即 existential lens。

把这三步代入 §1.4 的骨架公式，即得本节开头的同构。细节 end 演算可回原文；教学上抓住「\(\Theta\) 的 coalgebra = Tambara；\(\Phi(\mathrm{representable})\) = existential」即可。

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
| get/set → ∃ | `gsToEx` | 取 \(c := s\) |
| ∃ → get/set | `exToGs` | `view = snd∘out` 等 |
| ∃ → ∀ Strong | `exToOptic` | `dimap out inn . first'`（= DaoFP `toLensP`） |
| get/set → ∀ | `gsToOptic` | Step 2 的 `lens` |
| ∀ → get/set | `opticToGs` | 用 `Forget` 与 `(->)`（或 FlipLens）取出 |

三条编码 round-trip：`rtGsEx` / `rtGsOptic` / `rtFull`。详见 [原理详解.md](原理详解.md) §5。

---

## 5. 换张量 → 整族 optic

**直接陈述：** Tambara 原先对任意 monoidal 张量 \(\otimes\) 定义：\(\alpha : P\langle a,b\rangle \to P\langle c\otimes a,\, c\otimes b\rangle\)。推导一字不改；换张量就换 optic。

| 张量 / 作用 | Tambara ≈ | Optic | existential 要点 |
|-------------|-----------|-------|------------------|
| product `(,)` | `Strong` / `Cartesian` | **Lens** | \(\int^{c} \mathcal{C}(s,c\times a)\times\mathcal{C}(c\times b,t)\)；焦点总在 |
| coproduct `Either` | `Choice` / `Cocartesian` | **Prism** | \(\int^{c} \mathcal{C}(s,c+a)\times\mathcal{C}(c+b,t) \cong \mathcal{C}(s,t+a)\times\mathcal{C}(b,t)\)；`match`/`build` |
| 仅 Profunctor（无 α） | — | **Iso** | \(\mathcal{C}(s,a)\times\mathcal{C}(b,t)\)；无上下文 |
| 序列 / 幂级数作用 \(c\bullet a = \sum_m c_m \times a^m\) | Traversing（推广 Tambara） | **Traversal** | 多焦点；\(n\) 与残差 \(c_n\) 一起藏在 coend；DaoFP 用 \([\mathbb{N},\mathcal{C}]\) 上 Day 卷积给幺半结构 |
| 两范畴上的作用 | mixed Tambara | **mixed optics** | \(\int^{m} \mathcal{C}(s,m\bullet a)\times\mathcal{D}(m\bullet b,t)\)；\(P : \mathcal{C}^{\mathrm{op}}\times\mathcal{D}\to\mathrm{Set}\) |

### 5.1 Prism 要点（和张量）

```haskell
match :: s -> Either t a
build :: b -> t

class Profunctor p => Choice p where
  right' :: p a b -> p (Either c a) (Either c b)

type PrismP s t a b = forall p. Choice p => p a b -> p s t
toPrismP (Prism from to) = dimap from to . right'
```

existential：\(s\) 要么给出焦点 \(a\)，要么给出残差 \(c\)；\(t\) 可由新焦点 \(b\) 或同一残差装回。本仓库 `ForgetM` 做 `preview`（Step 3）；`_Just` round-trip 见 Step 5。

### 5.2 Traversal 与 mixed（略写）

Traversal 要同时处理「\(n\) 个焦点」，类型安全需要依赖类型或把长度写进 existential。范畴侧对每个 \(n\) 有残差 \(c_n\)，作用 \(c \bullet a = \sum_m c_m \times a^m\)，在 \([\mathbb{N},\mathcal{C}]\) 上用 Day 卷积得到幺半结构；推广 Tambara 后 ∀ 侧仍成立。Mixed optics 允许左右两边活在不同范畴、共享同一个 monoidal 作用者 \(M\)（actegory）。本仓库 Step 3 对 Traversal 仅占位；细节回原文或专文。

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
| **existential \(c\) vs 类型参数 \(s\)** | `gsToEx` 常取 \(c:=s\) 作代表元；一般 \(c\) 是「真正的残差」，同构不唯一到代表元选取 |
| **本文 vs 原理详解** | 原理详解走仓库代码链；本文走 DaoFP 范畴推导链。交汇点是 Strong≅Tambara 与 ∃↔∀ |

---

## 7. 读原文章节地图（各节目的导读）

对照 *DaoFP* 第 19 章 `19-Tambara.tex`：下面按原文顺序，对**每一个** section / subsection 给出目的、论证角色、关键公式，以及（如适用）可跳读提示与本文 / 仓库对照。先读「本节目的」；细节公式可回原文或本文 §0–§5。

速查表（详解见各小节）：

| 原文 | 本文 |
|------|------|
| 章首动机 | §0 |
| （预备）co-presheaf / Yoneda / fiber | [§1.0](#sec-copresheaf) |
| § Tannakian Reconstruction | §1（含 §1.0–§1.4） |
| § Profunctor Lenses · Iso / 缺口 / Tambara / 主公式 / Haskell | §2–§4 |
| § General Optics（⊗、Prism、Traversal） | §5 |
| § Mixed Optics | §5 表末行 |
| （无专节）与手写 demo | §6 |

---

### 7.0 章首（Chapter opener，§ Tannakian 之前）

1. **原文标题：** *Tambara Modules*（章首动机段落，无独立 `\section`）
2. **本节目的：** 说明为何要把 optics 改写成 profunctor 表示：经典 get/set（尤其 setter）与 existential 的复合别扭；profunctor 形 \(p\,a\,b \to p\,s\,t\) 让复合回到普通函数复合 `(.)`。
3. **在整章论证中的角色：** 提出整章要解决的问题，并预告「Tambara modules = 那一类能正确复合的 profunctor」；后续 Tannakian → Tambara → ∀↔∃ 都是为兑现这一承诺。
4. **关键结论 / 公式：** 无独立公式；目标陈述为：找出一类 \(P\)，使

$$
\int_{P} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
$$

在合适结构下等于 existential lens（后文主公式）。
5. **可跳读提示：** 不可跳——这是动机锚点。
6. **对照本文 / 仓库：** 本文 [§0](#0-这一章在解决什么)；学习路线 Step 2–3 的复合体验。

---

### 7.1 § Tannakian Reconstruction

1. **原文标题：** *Tannakian Reconstruction*
2. **本节目的：** 建立「用全体表示（co-presheaves）重建箭头」的技术，作为后文把 existential optic 写成「对一类 profunctor 多态」的范畴引擎。
3. **在整章论证中的角色：** 整章的证明骨架；先在 functor 上练熟，再换到 profunctor / Tambara。
4. **关键结论 / 公式：** 节标题本身不给公式；核心在子节：

$$
\int_{F : [\mathcal{C},\mathrm{Set}]} \mathrm{Set}(F a, F b) \;\cong\; \mathcal{C}(a,b)
$$

以及带伴随的推广（见 §7.1.6）。
5. **可跳读提示：** 整节不可跳；其中 Cayley/DList 子节可扫过（见下）。
6. **对照本文 / 仓库：** 本文 [§1](#1-热身用全部表示重建箭头tannakian)；预备语言见 [§1.0 co-presheaf](#sec-copresheaf)。

#### 7.1.1 Monoids and their Representations

1. **原文标题：** *Monoids and their Representations*
2. **本节目的：** 把 monoid 看成单对象范畴 \(\mathcal{M}\)，把表示看成 functor \(F : \mathcal{M} \to \mathrm{Set}\)，并说明单个底层集合 \(F*\) 通常不够重建 monoid——必须同时看全体表示与 equivariant maps。
3. **在整章论证中的角色：** 引入「表示范畴 \([\mathcal{M},\mathrm{Set}]\) + 自然变换（equivariant）」这一语言；为 Tannakian 重建准备 fiber functor 与 wedge 直觉。
4. **关键结论 / 公式：** 自然性 / equivariance：

$$
\alpha \circ (F m) = (G m) \circ \alpha
$$

其中 \(\alpha : F* \to G*\) 是自然变换的唯一分量。
5. **可跳读提示：** 若已熟悉 monoid-as-category 与 equivariant maps，可快读；不可整节跳过。
6. **对照本文 / 仓库：** 本文 §1.1。

#### 7.1.2 Cayley's theorem

1. **原文标题：** *Cayley's theorem*
2. **本节目的：** 展示每个 monoid 同构于一组自函数（post-composition 表示），并用 difference list（`DList`）把 \(O(N^2)\) 的 list reverse 变成线性，作为表示论的程序例子。
3. **在整章论证中的角色：** 表示论家族的旁支例证；**不**进入 optics 主公式的推导链。
4. **关键结论 / 公式：** Cayley 表示：取 \(S = \mathcal{M}(*,*)\)，\((F m)\, n = m \circ n\)；Haskell：`type DList a = [a] -> [a]`，`rep as = (as ++)`。
5. **可跳读提示：** **可跳读 / 扫过**——与 ∀↔∃ lens 公式无必要步骤；本文已压成附录。
6. **对照本文 / 仓库：** 本文 §1 附录「Cayley / DList」。

#### 7.1.3 Tannakian reconstruction of a monoid

1. **原文标题：** *Tannakian reconstruction of a monoid*
2. **本节目的：** 陈述 monoid 情形的重建定理：从全体表示上 fiber functor 到自身的自然变换（写成 end）可恢复 \(\mathcal{M}(*,*)\)。
3. **在整章论证中的角色：** 把「全体表示一起约束」写成具体 end；是一般范畴情形（下一小节）的特例预告。
4. **关键结论 / 公式：**

$$
\int_F \mathrm{Set}(F *, F *) \;\cong\; \mathcal{M}(*, *)
$$

fiber functor：\(\mathrm{fib}\, F = F*\)。
5. **可跳读提示：** 若急于看一般证明，可与下一小节合并读；公式本身要记住。
6. **对照本文 / 仓库：** 本文 §1 主公式的 monoid 特例。

#### 7.1.4 Proof of Tannakian reconstruction

1. **原文标题：** *Proof of Tannakian reconstruction*
2. **本节目的：** 对一般范畴 \(\mathcal{C}\) 证明 \(\int_F \mathrm{Set}(Fa, Fb) \cong \mathcal{C}(a,b)\)，并用 proof-relevant subset 给出直觉。
3. **在整章论证中的角色：** 整章第一次完整的 end + Yoneda 证明模板；后文 Iso / Lens 的 ∀ 侧都是同一模板的实例。
4. **关键结论 / 公式：**

$$
\int_{F : [\mathcal{C},\mathrm{Set}]} \mathrm{Set}(F a, F b) \;\cong\; \mathcal{C}(a,b)
$$

证明两步 Yoneda：\(Fa \cong [\mathcal{C},\mathrm{Set}](\mathcal{C}(a,-), F)\)，再对 functor 范畴用 Yoneda 推论。直觉：左端元素 =「对每个与范畴结构相容的子集，若 \(a\) 在则 \(b\) 在」\(\iff\) 存在 \(a \to b\)。
5. **可跳读提示：** 证明细节可略读，但主公式与「wedge 经自然变换进入 end」不可丢。
6. **对照本文 / 仓库：** 本文 §1.2。

#### 7.1.5 Tannakian reconstruction in Haskell

1. **原文标题：** *Tannakian reconstruction in Haskell*
2. **本节目的：** 把主公式翻译成 `forall f. Functor f => f a -> f b ≅ a -> b`，并把它解释为最简 optic——**Getter**；强调 functor 表示同样用 `(.)` 复合。
3. **在整章论证中的角色：** 第一次在代码里兑现「表示侧复合 = 函数复合」；为 Lens/Prism 的 profunctor 表示预演。
4. **关键结论 / 公式：**

```haskell
type Getter a b = forall f. Functor f => f a -> f b
-- toTannaka g = fmap g
-- fromTannaka g a = runIdentity (g (Identity a))
```

5. **可跳读提示：** 不可跳——这是 optics 复合动机的最小可运行模型。
6. **对照本文 / 仓库：** 本文 §1.3。

#### 7.1.6 Tannakian reconstruction with adjunction

1. **原文标题：** *Tannakian reconstruction with adjunction*
2. **本节目的：** 把 end 从裸 \([\mathcal{C},\mathrm{Set}]\) 推广到带 free/forgetful \(F \dashv U\) 的特殊 functor 范畴 \(\mathcal{T}\)，得到 optics 的总引擎公式。
3. **在整章论证中的角色：** **整章总引擎**；后文 Tambara 范畴只是把 \(\mathcal{T}\) 实例化，并把对象换成 \(\langle a,b\rangle\)。
4. **关键结论 / 公式：**

$$
\int_{P : \mathcal{T}} \mathrm{Set}\big((U P)\, a,\, (U P)\, s\big)
  \;\cong\;
\big(\Phi\, \mathcal{C}(a,-)\big)\, s
  \;=\;
(\Phi Y^{a})\, s
$$

其中 \(\Phi = U \circ F\) 是 monad。预告：optics 推导里 \(a,s\) 换成 \(\langle a,b\rangle,\langle s,t\rangle\)，functors 换成 profunctors。
5. **可跳读提示：** 不可跳——后文 Lens 公式直接代入此骨架。
6. **对照本文 / 仓库：** 本文 §1.4。

---

### 7.2 § Profunctor Lenses

1. **原文标题：** *Profunctor Lenses*（节首，Iso 之前的动机段）
2. **本节目的：** 说明 type-changing lens 的 hom-set 是带作用 \(c \bullet \langle a,b\rangle = \langle c\times a,\, c\times b\rangle\) 的 coend，因此表示应在 **profunctors**（\(\mathcal{C}^{\mathrm{op}}\times\mathcal{C}\to\mathrm{Set}\)）上做 Tannakian。
3. **在整章论证中的角色：** 把问题从 functor 表示转到 profunctor 表示；定义后文 Iso / Lens 共用的「作用」记号。
4. **关键结论 / 公式：**

$$
\mathcal{L}\langle s,t\rangle\langle a,b\rangle
  \;=\;
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
  \;=\;
\int^{c} (\mathcal{C}^{\mathrm{op}}\times\mathcal{C})(c \bullet \langle a,b\rangle, \langle s,t\rangle)
$$

$$
c \bullet \langle a,b\rangle \;=\; \langle c\times a,\; c\times b\rangle
$$

5. **可跳读提示：** 不可跳。
6. **对照本文 / 仓库：** 本文 [§2](#2-为何-lens-要看-profunctor)。

#### 7.2.1 Iso

1. **原文标题：** *Iso*
2. **本节目的：** 在裸 Profunctor 范畴（无额外 \(\alpha\)）上跑一遍 Tannakian，得到 Iso：一对 \((s\to a,\, b\to t)\)，对应 `forall p. Profunctor p => p a b -> p s t`。
3. **在整章论证中的角色：** 无上下文残差时的 sanity check；说明「还缺 \(\alpha\)」之前，裸 Profunctor 已经够 Iso。
4. **关键结论 / 公式：**

$$
\int_{P} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
  \;\cong\;
\mathcal{C}(s,a) \times \mathcal{C}(b,t)
$$

Haskell：`type IsoP s t a b = forall p. Profunctor p => p a b -> p s t`，`toIsoP (f,g) = dimap f g`。
5. **可跳读提示：** 短；建议读完再进 Lens 缺口。
6. **对照本文 / 仓库：** 本文 §2.1；Step 6 / 原理详解 §6.3。

#### 7.2.2 Profunctors and lenses

1. **原文标题：** *Profunctors and lenses*
2. **本节目的：** 从 existential \(\langle f,g\rangle\) 出发，指出用 `dimap` 得到 \(P\langle s,t\rangle\) 之前，缺口正是 \(P\langle a,b\rangle \to P\langle c\times a,\, c\times b\rangle\)。
3. **在整章论证中的角色：** 把「需要什么结构」立成下一节的定义动机；不引入新公式，只钉缺口。
4. **关键结论 / 公式：** 缺口（待定义为 Tambara）：

$$
P\langle a,b\rangle \;\to\; P\langle c\times a,\, c\times b\rangle
$$

已有：若持有 \(P\langle c\times a,\, c\times b\rangle\)，则 \(P\langle f,g\rangle\) 给出 \(P\langle s,t\rangle\)。
5. **可跳读提示：** 不可跳——一句缺口，整节 Tambara 由此而来。
6. **对照本文 / 仓库：** 本文 §2.2。

#### 7.2.3 Tambara module

1. **原文标题：** *Tambara module*
2. **本节目的：** 定义相对笛卡尔积的 Tambara module：一族 \(\alpha\)，要求对 \(a,b\) 自然、对上下文 \(c\) **dinatural**，并满足积的单位 / 结合相干；态射是与 \(\alpha\) 交换的自然变换。
3. **在整章论证中的角色：** 正式给出「那一类 \(P\)」；Tambara 范畴的箭头结构经 wedge 进入后文 end，决定 ∀ 侧长什么样。
4. **关键结论 / 公式：**

$$
\alpha_{\langle a,b\rangle,c} : P\langle a,b\rangle \to P\langle c\times a,\, c\times b\rangle
$$

$$
\alpha_{\langle a,b\rangle,\, 1} \;=\; \mathrm{id},\qquad
\alpha_{\langle a,b\rangle,\, c'\times c}
  \;\cong\;
\alpha_{\langle c\times a,\, c\times b\rangle,\, c'}
  \circ
\alpha_{\langle a,b\rangle,\, c}
$$

5. **可跳读提示：** dinaturality 交换图可略读；\(\alpha\) 定义与相干、态射交换方不可丢。
6. **对照本文 / 仓库：** 本文 [§3](#3-缺口与-tambara-module)；`app-step4`（`Tambara ten` ≅ `Strong`/`Choice`）。

#### 7.2.4 Profunctor lenses

1. **原文标题：** *Profunctor lenses*
2. **本节目的：** 用 comonad \(\Theta\) 的 coalgebras刻画 Tambara，取其左伴随 monad \(\Phi\)，把 \(\Phi\) 作用在 representable 上，得到 ∀ Tambara ≅ existential lens。
3. **在整章论证中的角色：** **主公式的证明**；把 §7.1.6 的总引擎实例化为积张量上的 Tambara。
4. **关键结论 / 公式：**

$$
(\Theta P)\langle a,b\rangle \;=\; \int_{c} P\langle c\times a,\, c\times b\rangle
$$

（coalgebras \(P\to\Theta P\) = Tambara；Tambara = EM(\(\Theta\))）

$$
(\Phi P)\langle s,t\rangle
  \;=\;
\int^{u,v,c}
  (\mathcal{C}^{\mathrm{op}}\times\mathcal{C})(c \bullet \langle u,v\rangle, \langle s,t\rangle)
  \times P\langle u,v\rangle
$$

$$
\int_{P : \mathrm{Tambara}} \mathrm{Set}(P\langle a,b\rangle, P\langle s,t\rangle)
  \;\cong\;
\int^{c} \mathcal{C}(s, c\times a) \times \mathcal{C}(c\times b, t)
$$

5. **可跳读提示：** end 演算细节可回原文细读；教学上抓住「\(\Theta\)-coalgebra = Tambara；\(\Phi(\mathrm{representable})\) = ∃ lens」即可。
6. **对照本文 / 仓库：** 本文 [§4](#4-主公式-tambara--existential-lens)；`app-step5` 的 ∃↔∀。

#### 7.2.5 Profunctor lenses in Haskell

1. **原文标题：** *Profunctor lenses in Haskell*
2. **本节目的：** 把积上 Tambara 写成 `Cartesian`/`Strong`，定义 `LensP`，给出 existential → profunctor（`dimap . alpha`）与用 `FlipLens` 取回 get/set；强调复合是 `(.)`。
3. **在整章论证中的角色：** 把主公式落到可运行代码，兑现章首「复合变简单」的承诺。
4. **关键结论 / 公式：**

```haskell
type LensP s t a b = forall p. Cartesian p => p a b -> p s t
-- toLensP (LensE from to) = dimap from to . alpha
-- fromLensP：喂 FlipLens id (\_ b -> b) 取出 get/set
```

5. **可跳读提示：** 不可跳——仓库 Step 4–5 的直接原文对应。
6. **对照本文 / 仓库：** 本文 §4.2–4.3；`app-step4` / `app-step5`（`exToOptic` ≈ `toLensP`，`opticToGs` / FlipLens）。

---

### 7.3 § General Optics

1. **原文标题：** *General Optics*（节首，Prisms 之前）
2. **本节目的：** 指出 Tambara 原本对任意 monoidal 张量 \(\otimes\) 定义；推导一字不改，换张量就换 optic。
3. **在整章论证中的角色：** 把 Lens 特款推广成整族 optic 的统一机制。
4. **关键结论 / 公式：**

$$
\alpha_{\langle a,b\rangle,c} : P\langle a,b\rangle \to P\langle c \otimes a,\, c \otimes b\rangle
$$

（相干律与 ∀↔∃ 推导对一般 \(\otimes\) 原样成立。）
5. **可跳读提示：** 短；读完再进 Prism / Traversal。
6. **对照本文 / 仓库：** 本文 [§5](#5-换张量--整族-optic) 开篇表。

#### 7.3.1 Prisms

1. **原文标题：** *Prisms*
2. **本节目的：** 把积换成 coproduct，得到 Prism：existential / `match`–`build`，以及 `Choice`/`Cocartesian` 上的 profunctor 表示。
3. **在整章论证中的角色：** 「换张量」的第一个完整实例；与 Lens 平行，验证统一框架。
4. **关键结论 / 公式：**

$$
\int^{c} \mathcal{C}(s, c+a)\times\mathcal{C}(c+b, t)
  \;\cong\;
\mathcal{C}(s, t+a)\times\mathcal{C}(b,t)
$$

Haskell：`match :: s -> Either t a`，`build :: b -> t`；`type PrismP s t a b = forall p. Cocartesian p => p a b -> p s t`；`toPrismP = dimap from to . alpha'`。
5. **可跳读提示：** 若已会 Lens 推导，可快读 existential 化简与 `Choice` 对应。
6. **对照本文 / 仓库：** 本文 §5.1；Step 3 `ForgetM` / `_Just`；Step 5 Prism round-trip。

#### 7.3.2 Traversals

1. **原文标题：** *Traversals*
2. **本节目的：** 处理多焦点：用 \(n\) 与残差序列 \(c_n\)（或 \([\mathbb{N},\mathcal{C}]\)）写出 existential；用作用 \(c\bullet a = \sum_m c_m\times a^m\) 与 Day 卷积给出幺半结构，再推广 Tambara 得到 ∀ 侧。
3. **在整章论证中的角色：** 展示「作用不必来自 \(\mathcal{C}\) 自身的 \(\otimes\)」——可以是 monoidal 范畴对 \(\mathcal{C}\) 的作用；为 Mixed Optics 铺路。
4. **关键结论 / 公式：**

$$
\mathbf{Tr}\langle s,t\rangle\langle a,b\rangle
  \;=\;
\int^{c : [\mathbb{N},\mathcal{C}]}
  \mathcal{C}(s, c\bullet a)\times\mathcal{C}(c\bullet b, t),
\qquad
c\bullet a \;=\; \sum_m c_m \times a^m
$$

推广 Tambara：\(\alpha : P\langle a,b\rangle \to P\langle c\bullet a,\, c\bullet b\rangle\)；∀ 侧仍为对广义 Tambara 的 end。
5. **可跳读提示：** Day 卷积与 fibrations 细节可略；记住「多焦点 = 序列作用 + 推广 Tambara」。本仓库 Step 3 对 Traversal 仅占位。
6. **对照本文 / 仓库：** 本文 §5.2。

---

### 7.4 § Mixed Optics

1. **原文标题：** *Mixed Optics*
2. **本节目的：** 允许同一个 monoidal \(\mathcal{M}\) 分别作用在两个范畴 \(\mathcal{C},\mathcal{D}\)（actegory），定义 mixed optic，并用两端不同的 profunctor \(P : \mathcal{C}^{\mathrm{op}}\times\mathcal{D}\to\mathrm{Set}\) 与双作用 Tambara 给出表示。
3. **在整章论证中的角色：** 框架的最广形式；把「一张量、一范畴」推广到「一作用者、两边可异」。
4. **关键结论 / 公式：**

$$
\mathcal{O}\langle s,t\rangle\langle a,b\rangle
  \;=\;
\int^{m : \mathcal{M}}
  \mathcal{C}(s, m\bullet a)\times\mathcal{D}(m\bullet b, t)
$$

$$
\alpha_{\langle a,b\rangle,m} : P\langle a,b\rangle \to P\langle m\bullet a,\, m\bullet b\rangle
\quad(P : \mathcal{C}^{\mathrm{op}}\times\mathcal{D}\to\mathrm{Set})
$$

5. **可跳读提示：** 本仓库未实现 mixed；读主线 Lens/Prism 后可作扩展阅读。
6. **对照本文 / 仓库：** 本文 §5 表末行；无对应 Step 代码。

---

## 延伸阅读

1. Bartosz Milewski — *DaoFP* Chapter 19（Tambara Modules）；博客 Profunctor Optics / Tambara 系列  
2. Pickering, Gibbons, Wu — *Profunctor Optics: Modular Data Accessors*  
3. 本仓库：[原理详解.md](原理详解.md) §4–5；[Strong-Profunctor组合.md](Strong-Profunctor组合.md) §7；[学习路线.md](学习路线.md) Step 4–5；[`app-step4`](../app-step4/Main.hs) / [`app-step5`](../app-step5/Main.hs)  
4. Hackage：`lens`、`optics`、`profunctors`（读 `Strong`/`Choice` 类型，对照手写版）
