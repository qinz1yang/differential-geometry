# Derived-neighborhood complement: first producer review

Status: READY FOR OWNER REVIEW. Both geometric leaves are UNREVIEWED; the joint fixture is
UNTESTED. This decomposition does not close the original frozen Section 33 leaf.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`7fc0ff29d79cd97a1cc577019996f9e470f68fc2`，文件 `Skeleton/DerivedNeighborhoodComplement.lean`。
先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.m，以及真实模块
`DerivedNeighborhoodRay.lean`、`DerivedNeighborhood.lean`、`DerivedNeighborhoodRetraction.lean`、
`DerivedWeights.lean` 与 `PseudoCell.lean` 的 `IsTube`。约 1500 中文字，OK 只列一行。

两真实基础模块已独立零诊断编译、公理闭包与 13 项环境 linter 审计；新骨架恰两条
叶子 sorry。独立复制源码审计核对了冻结 `section33_tube_product` 的完整展开类型相同、
装配确实消费两个新叶与真实像端传输，装配体无直接 sorry。公理闭包仍含这两叶的
`sorryAx`，因此不是 endpoint 的完成证书。原 §33 骨架未导入此骨架，也未删除原叶。

请逐叶裁定 `isEmbedding_derivedNeighborhoodRay`、`range_derivedNeighborhoodRay`，重点为：

1. 射线是固定映射 `(b,t) ↦ (1-t) • b + t • p(b)`；`p` 使用
   `subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K)`，
   与实际二次导出邻域及现有收缩采用同一次细分。是否每条射线恰有一个边界起点，
   连续逆在面交界处能否相容。强变形收缩或基本群等价不替代这两项结论。
2. `A` 是有限三维组合带边流形，`K.faces ⊆ A.faces`，且
   `K.space ⊆ interior A.space`。这里允许任意子复形，比冻结消费者的一维图核更一般。
   请检查是否真能保持此一般性，包括孤立点、端点、非纯维及不连通核心。若需修订，
   必须说明冻结 `IsTube` 的哪一条字段供给修订条件。
3. `mem_faceNeighborhood_space_iff` 约束最大重心权重。不能直接把边界写成总 core mass
   等于 1/2。对第一细分单形内的点，设 m 为 core 权重之和、a/b 为 core/noncore
   最大权重，拟用 `t = m * (1 - b/a)`、`(x - t*p(x))/(1-t)` 取回射线坐标。
   请核对严格/非严格不等式与环境 frontier 的对应，以及分母、边界退化、跨面一致性。
   worker 的 913 个有理权重点算术检查只检验局部公式，不是几何证明或联合 fixture。
4. 冻结装配从同一 `IsTube.derivedModel`、`unionEq` 取得
   `N = (derivedNeighborhood A K).space`，再由 `isNeighborhood` 导出核心位于环境内部。
   像端只用 h 在紧集 N 上的连续性和单射性，经 `CompactEmbeddingComplement` 运输；
   不假定 h 全域连续。请核供给链是否还缺少几何或相对边界证书。
5. 联合 fixture 候选：充分细分三球内的一条三角形闭路加一个孤立内点，再取具有真实
   内部非 PL 扰动的环境同胚作为 h。须给同一三角剖分、图核、导出邻域和全部
   `IsTube` 字段的联合证书；当前未形式化，不能仅以标准实心环面代替任意图核情形。

最后列遗漏义务、共同非退化 fixture、最可能的意外。核心位于环境边界的四面体顶点
只是说明为何不能删去 `hKint`；它不满足全部假设，不是该叶或 `IsTube` 的反例。
FALSE 必须给满足全部字段的联合反例；外审是证据，lead 会再核 Lean 原文。
