# Compact Section 34: first statement review

Status: the owner supplied a first review of the earlier snapshot `09672b87`; see digest AS.
This full request need not be sent again. Any follow-up should address only the recorded
interface changes and identify the already-fixed generator difference.

请按同目录 `REVIEW-TEMPLATE.md` 审查
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`e1201fcfc15858264188c569799e67890a2e1f55`，文件
`Skeleton/Section34Compact.lean`（12 个开放叶子）。先读 `Skeleton/README.md`、
`FREE_INPUTS.md` 的 B1.b.8、设计答复 `consult/AO-moise341-design-answer-digest.md` §1。
请用中文，约 1500 字；OK 叶子只列一行，反例必须逐项满足当前 Lean 假设。

这是 `Moise331`、`Moise305Tame` 到 `Moise341OnNeighborhood`，再经已证明的 inward push
到 `Moise341` 的条件装配。独立复编为退出码 0、恰好 12 条叶子 sorry；有限 rank 下降及
labelled-cell 延拓已证明。尚未证明几何叶子，不能据此认定 34.1 已闭合。

本轮明确修订：`Section34CompactGraphFrame.carriesFundamentalGroupOnto` 真实调用嵌套环面
generator，并在装配中传给 `compactTraceHomology`。这是唯一改变的叶子签名，其余 11 个
叶子和两个端点签名不变。四面体只检查外侧 cut 组合关系；小容差下须先细分，整链共同
carrier fixture 仍为 UNTESTED。

重点裁定：

1. 十类有限 cut 是否完整记录边界顶点的 `outerFace` 和边界边的 `outerArc`？源侧 closure
   公式、目标侧完整边界 tilings 是否相容，是否遗漏外侧端点或交集？将源胞腔固定为这些
   closure，是否比“自由胞腔加关联关系”多要求了不能供给的性质？
2. `exists_compactCutAndGraph` 是否忠实承担兼容细分、33.1 正则邻域、先外环面和容差、再
   `f₁`、再内环面的联合选择？p.239 link condition 作为字段是否可在相应细分后产生；
   不要把有边界的圆盘 link 当成球面 link。
3. envelope、shell、general-position 及 trace-homology 四步是否各有足够假设？尤其核对
   envelope 叶子没有单独接收 `IsOpen V` 时，现有 cut/carrier 条件是否足以供给辅助球；
   不预设这个遗漏一定错误。generator 到整条 trace 的 H₁ 满射仍须证明。
4. 压缩和 bigon 的有限下降是否保持同一全局数据？P6、P7 的外侧目标胞腔、exact meets、
   空 sector 和 target-recognition 是否足以供给包括 splitting disks 的完整延拓？
5. 请给一个满足全部相关假设的共同非退化模型，区分纸面构造与已在 Lean 检验的 fixture；
   若发现不可供给或空泛，指出具体字段及应修复的陈述。

最后报告遗漏义务、共同 fixture、最可能的意外。外审是证据而非裁决；lead 会对照 Lean
逐条核实，并报告分歧。
