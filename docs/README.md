# 文档索引

本目录是 [tambara-lens-demo](../README.md) 的初学者文档。建议顺序：

1. **先跑代码**：`stack build` 后依次 `stack exec step1-…` … `step6-…`（含 `step2b-van-laarhoven`）
2. **对照源码读注释**：每个 `app-stepN/Main.hs` 顶部有该步目标说明
3. **读本目录**：

| 文档 | 内容 |
|------|------|
| [学习路线.md](学习路线.md) | 把 steps 1–6 串成故事；常见坑 |
| [概念对照表.md](概念对照表.md) | 约束 ↔ optic ↔ 张量 速查 |
| [原理详解.md](原理详解.md) | **原理长文**：get/set → profunctor → Tambara → existential/coend |
| [Lens二形态对比.md](Lens二形态对比.md) | 三种形态：(A) get/set、(B) Strong、(C) van Laarhoven |
| [van-Laarhoven教程.md](van-Laarhoven教程.md) | **(C) 详细教程**：推导、记录嵌套、类型变化、换 `f`、与 Strong 对照 |
| [Strong-Profunctor组合.md](Strong-Profunctor组合.md) | **(B) 组合专章**：`(l . m) p = l (m p)`、类型表、分配律、与 VL 对照 |

仓库根目录 [README.md](../README.md) 含构建说明与步骤总表。

## 源码入口

| 步骤 | 路径 |
|------|------|
| 1 | [`../app/Main.hs`](../app/Main.hs) |
| 2 | [`../app-step2/Main.hs`](../app-step2/Main.hs) |
| 2b VL | [`../app-step2-vl/Main.hs`](../app-step2-vl/Main.hs) |
| 3 | [`../app-step3/Main.hs`](../app-step3/Main.hs) |
| 4 | [`../app-step4/Main.hs`](../app-step4/Main.hs) |
| 5 | [`../app-step5/Main.hs`](../app-step5/Main.hs) |
| 6 | [`../app-step6/Main.hs`](../app-step6/Main.hs) |
