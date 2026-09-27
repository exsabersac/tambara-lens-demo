# tambara-lens-demo

从 **经典 get/set Lens** 走到 **Tambara 模 / profunctor optics** 的动手学习仓库。

面向：已经会一点 Haskell、想弄清「为什么 Lens 要写成 `forall p. Strong p => …`」、
以及 Strong/Choice 和 Tambara、existential optic 之间关系的读者（学习路径作者：yu binbin）。

- **仅依赖 `base`**（不引入 `lens` / `profunctors` 包），约束与构造全部手写。
- Stack **lts-21.25**，GHC **9.4.8**。
- 注释以中文为主，术语保留精确英文（Profunctor、Tambara、coend …）。

更长的推理链见 **[docs/原理详解.md](docs/原理详解.md)**；三种 Lens 形态对比（get/set、Strong、van Laarhoven）见 **[docs/Lens二形态对比.md](docs/Lens二形态对比.md)**。

## 前置条件

1. 安装 [GHCup](https://www.haskell.org/ghcup/)，准备好 Stack。
2. 本仓库已固定 snapshot：

```yaml
# stack.yaml
snapshot: lts-21.25
```

3. 若本机有自定义 GHC：确保能解析到 9.4.8（lts-21.25 自带）。

在本演示环境中，请先：

```bash
source /home/box/.ghcup/env
```

## 构建与运行

```bash
cd tambara-lens-demo
stack build

stack exec step1-classic-lens
stack exec step2-strong-lens
stack exec step2b-van-laarhoven
stack exec step3-optics-table
stack exec step4-tambara
stack exec step5-optic-tambara
stack exec step6-library-notes
```

`package.yaml` 声明全部可执行文件；`stack build` 会经 hpack 再生 `.cabal`。

## 学习路线（Steps 1–6）

| 步骤 | 可执行文件 | 源码 | 学什么 |
|------|------------|------|--------|
| 1 | `step1-classic-lens` | [app/Main.hs](app/Main.hs) | 经典 `view`/`set` Lens、三条定律、复合 |
| 2 | `step2-strong-lens` | [app-step2/Main.hs](app-step2/Main.hs) | `Profunctor` + `Strong`；`Lens = forall Strong` |
| 2b | `step2b-van-laarhoven` | [app-step2-vl/Main.hs](app-step2-vl/Main.hs) | van Laarhoven：`forall f. Functor f => …`（`lens` 库形态） |
| 3 | `step3-optics-table` | [app-step3/Main.hs](app-step3/Main.hs) | 约束表：Lens / Prism / Affine / Iso / Traversal |
| 4 | `step4-tambara` | [app-step4/Main.hs](app-step4/Main.hs) | `Tambara`；Strong≅Tambara_(,)，Choice≅Tambara_Either |
| 5 | `step5-optic-tambara` | [app-step5/Main.hs](app-step5/Main.hs) | existential / coend ↔ ∀ Tambara；round-trip |
| 6 | `step6-library-notes` | [app-step6/Main.hs](app-step6/Main.hs) | 与 lens / optics 库对照；Iso 微例；下一步阅读 |

叙事版展开、常见坑：见 [docs/学习路线.md](docs/学习路线.md)。  
约束 ↔ optic ↔ 张量：见 [docs/概念对照表.md](docs/概念对照表.md)。  
原理长文：见 [docs/原理详解.md](docs/原理详解.md)。

## 文档索引

- [docs/README.md](docs/README.md) — 文档目录
- [docs/学习路线.md](docs/学习路线.md) — 初学者叙事指南
- [docs/概念对照表.md](docs/概念对照表.md) — 速查表
- [docs/原理详解.md](docs/原理详解.md) — 原理推理链（推荐精读）
- [docs/Lens二形态对比.md](docs/Lens二形态对比.md) — 三种形态：get/set、Strong、van Laarhoven

## 许可

BSD-3-Clause（见 `package.yaml`）。
