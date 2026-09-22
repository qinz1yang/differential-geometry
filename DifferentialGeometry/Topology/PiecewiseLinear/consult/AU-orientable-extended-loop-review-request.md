# Intrinsic orientable extended loop theorem: first statement review

Status: READY FOR OWNER REVIEW. The two leaves are UNREVIEWED. This does not close the older
unrestricted `Moise264` or change the Section 33 endpoint's dependency.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`ac933e4c61453e5bdcb1d592cc0c5b5795fa234d`，文件
`Skeleton/ExtendedLoopTheoremOrientable.lean` 及真实命题模块
`ExtendedLoopTheoremStatement.lean`。先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.i。
背景是 Moise 26.4；约 1500 中文字，OK 只列一行，反例逐项满足全部 Lean 假设。

真实命题模块已零诊断编译、公理和标准 linter 审计；骨架独立复检恰好两条 sorry。
`moise264_orientable (h252 : Moise252) : Moise264Orientable` 是真实条件装配。

本轮必须先裁定接口：旧 `Moise264` 在辅助向量空间 E 中要求 two-sided，且不要求 K
可定向。新受限版明确要求 K 可定向，并在 `K.space` 的子空间拓扑中要求 two-sided。
K、L 均有限，L 为闭组合曲面，位于 K 的内部；E 的维数不必为 3。没有宣称二者蕴含。

请审两叶及装配，重点为：

1. `exists_bicollar_complement_with_boundary_collars` 同时选择 PL bicollar W、R 为
   `closure (K.space \ W)`、与旧边界兼容的新边界，以及每个 collar-end 分支回到 L
   的半 collar。它没有环路或盘输入输出。这些字段能否从 intrinsic two-sidedness
   联合供给？不能选择任意不相容的 R 或另一个 collar 后再拼接。
2. 半 collar 末端映射 `f : C(B,L.space)` 与 `p : C(L.space,B)` 的 LeftInverse 条件，
   是否可由一个曲面连通分支上的逆同胚向其他 clopen 分支作常值延拓得到。请保留 L
   不连通的情况；如需条件，指出生产者，而非静默加连通性。
3. `exists_nontrivial_boundary_loop_of_bicollar_complement` 对同一个 W、ρ、R，把原核
   转移到某个新边界分支上的非平凡闭路，且闭路在 R 中零伦。它不输出嵌入盘。请检查
   nonseparating 情形和最内圈/van Kampen 步骤是否足够；不是声称原来的任意 g 本身
   必须直接给出同一条边界闭路。
4. 装配从 K 向 R 继承可定向性，调用 25.2 后用现成 `DiskBoundaryCollar` 接半 collar。
   请核对旧边界避让、盘只在新盘边界碰 L、以及借 p 保留边界的非零伦性。
5. 共同 fixture 提议为组合三球内的标准非退化 PL 环面、同一个双 collar 和经线核。
   另检验多分支及不分离的 L，不能只在三球中的分离环面上验证后即删掉这些情形。

最后列遗漏义务、共同 fixture、最可能的意外。fixture 目前 UNTESTED；外审结论须经
lead 对照原始 Lean 陈述尽调，不能据此直接宣称 26.4 或 33.1 已闭合。
