# 23 × 23 环面棋盘的皇后独立支配数

[English](README.md) · [完整论文 PDF](paper/main.pdf) · [Lean 主定理](formal/ToroidalQueens23/Main.lean)

本项目证明固定规模的确值 **i(Q₂₃ᵗ) = 12**：
在上下、左右边缘相接的23 × 23棋盘上，12枚互不攻击的皇后能够占据或攻击全部格子；11枚或更少无法满足这些条件。

作者：Weixin Yu，Independent Researcher，iweixin1214@gmail.com。

## 如何复现

安装 elan、Git 和 Lean 所需的 C 编译环境，然后运行：

```sh
git clone https://github.com/nobugchaos/toroidal-queens-23.git
cd toroidal-queens-23/formal
lake update
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean SemanticAudit.lean
```

Lean 固定为4.34.0，mathlib 固定为提交 `5ed2965256430c3649e86755f9576b54eca72435`。
依赖缓存下载失败时可以正常编译依赖；项目自身的枚举会在构建时执行，需要数分钟。

快速核查源码和12枚构造：

```sh
python scripts/check_sources.py
python scripts/verify_witness.py
```

## 证明与验证范围

`formal/ToroidalQueens23/Main.lean` 给出完整量词的最小值定理。
`formal/SemanticAudit.lean` 证明实际棋盘语义与项目定义一致。
`paper/main.pdf` 和 `paper/main.tex` 包含完整英文论证；`proof/OVERVIEW.md` 给出证明路线。

原有19个证明/审计源码从交付包提取到新目录后，完整构建通过，共1492个构建任务。
三处原生计算均已重新运行。依赖源码与固定归档逐项比较一致；这次本地复验复用了依赖编译缓存。
最新记录见 `evidence/recheck-2026-11-09/`，GitHub Actions 的实际运行状态另行显示。

源码没有 `sorry`、`admit` 或手写公理。完整结果包含三处 `native_decide`：
有限域幂和表、8,388,608个掩码的完备性检验、40,620,104个候选三元组的覆盖检验。
因此完整证明也信任原生编译和运行环境。12枚构造采用普通 `decide`。

本项目只处理23阶固定实例。当前文献检索未发现同一确值的先前证明，尚未确认历史首次；
没有宣称任意规模通解、外部同行评审或已向 arXiv 投稿。

大型历史 LRAT 文件和依赖二进制未纳入仓库，Lean 主证明不依赖它们。
公开日志中的本机路径已脱敏，原始与公开文件的对应摘要见 `provenance/`。
