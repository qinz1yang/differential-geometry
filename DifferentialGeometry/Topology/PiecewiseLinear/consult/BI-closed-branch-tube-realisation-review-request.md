# C1 branch tube: does the `realisation` clause fit the reviewed derived-neighbourhood route?

Status: request written by the lead on 2026-09-23 after the lease-c worker's analysis
(`Skeleton/OPUS_FILL_LOG_C.md`, `# Batch 6 (branch tube)`, entry `exists_isSourceTrackedBranchTube`).
No statement has been changed; the leaf is frozen pending this review.

请按同目录 `REVIEW-TEMPLATE.md` 审查 `liao9yuan/differential-geometry-dev` 的
`moise-integration`（镜像提交见 lead 发送时附注），文件 `Skeleton/ClosedBranchCaseOne.lean` 的唯一
叶子 `exists_isSourceTrackedBranchTube`（第 169 行）与真模块
`LoopTheorem/ClosedBranchCaseOneTransport.lean` 里的结构 `IsSourceTrackedBranchTube`（字段
`derived`、`cyclic`、`realisation`）。先读 `consult/AN-…`（C1 的原审查摘要）与
`Skeleton/OPUS_FILL_LOG_C.md` 的 `# Batch 6` 条目。请用中文，约 1200 字。

背景：C1 的姊妹叶子 `isPLBoundaryTubeProducer_double`（A2.4a）本日已由证明工作者关闭（沿边界
分支弧逐图表造管子，端点用齐次 cross-half-space 正规形），`DescentStepOrientable` 其余三个
叶子里有一个（`not_branchPreimage_eq_of_isOrientable`）就是 `ClosedBranchCaseOne` 的同名定理
模 `exists_isSourceTrackedBranchTube`，所以这个叶子同时挡住 C1 和 A2。

工作者的发现（手算，未在 Lean 里形式化）：`realisation` 要求管子的每条射线在给定 collar
坐标 `ρ` 下是 `J` 上的严格单调图像（字段里的 `s i t ≠ 0`、`ψ (r i, t) = ρ (D (φ (a i t, s i t)))`
等）。而 `derived` 要求 `N = derivedNeighborhood R Lc`（某个细分 `R` 的导出邻域）。在审查通过的
路线上（分支子复形的导出邻域），紧邻分支的每个三角形上，边界路径沿分支的两步增量分别是
`(1 - 2 x_r)/18` 和 `(2 x_r - 1)/18`，不可能同时为正，因此 `w` 在那里对任何顶点位置都不是严格
单调的。这说明审查通过的路线无法满足 `realisation`；它不说明陈述为假。

请裁定：

1. 核对上述增量计算：在导出邻域模型里，`realisation` 的单调性要求是否确实与 `derived` 冲突？
   如果冲突，是否存在别的 `R`、`Lc`（仍满足 `derived`）使 `realisation` 成立？
2. 若冲突不可避免：给出最小修正——(a) 把 `realisation` 改写为只按 `t = 0`、`t = 1` 处的半页与
   侧（half sheet, side）来陈述，或 (b) 去掉 `derived` 而让管子适配 `ρ`。请说明每种修正对
   消费者的影响：`ClosedBranchCaseOne` 的 `not_branchPreimage_eq_of_isOrientable`、C1 传输模块
   `ClosedBranchCaseOneTransport`、`ClosedBranchCaseOneTubeCarrier`、`ClosedBranchOrientability`，
   以及 A2 的 `not_branchPreimage_eq_of_isOrientable`。
3. 若你认为陈述本身为假：给出逐字段满足假设的反例。

最后报告：推荐哪个修正、修正后的字段文本、最可能的意外。外审是证据而非裁决；lead 会对照
Lean 逐条核实，并报告分歧。
