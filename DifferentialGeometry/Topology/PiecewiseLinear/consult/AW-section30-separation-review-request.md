# Section 30.3: first annular separator surgery review

Status: READY FOR OWNER REVIEW. The geometric leaf is UNREVIEWED; its fixture is UNTESTED.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`e9735916425f40f5b34f3eda3287e32e9bcc6212`，文件 `Skeleton/Section30Separation.lean`。
先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.k、`MoiseChain.lean` 的 `Moise303`。
原书 p. 215；约 1500 中文字，OK 只列一行，反例须满足完整 Lean 假设。

独立窄检查恰好一条 sorry，`moise303 : Moise303` 真实装配，未给 H、K 添加连通性。
一般路径判据 `separates_of_not_joinedIn` 已移到 `DifferentialGeometry/Topology/Connected/Separation.lean`，
整个真实模块零诊断、公理及 13 项 linter 审计通过。装配调用现成路径绕行定理，而非
把 `Separates` 结论当成新叶子的输出。

唯一叶 `exists_annular_split_ball` 的职责是联合产生：旧环带 A₁、新盘 Δ₁、小切割
三球 Q、删除带在 C 中的相对开性、Q 安全边界的 PL 开环带参数化。它既不接收 H、K
或原分离证书，也不输出分离结论。请核查：

1. 原式 D₁∩D₂=Δ、Δ 在两盘内部、两盘在 C 中为 Δ 的邻域，以及 C 在开 M 中相对
   闭，是否足够在任意指定 Ω 内联合选择所有输出。不要给 Δ 边界另加当前供给不了的
   横截条件；须说明适配有限 PL 分片、端点和折线接缝的构造。
2. `C ∩ O = A₁ \ (∂Δ ∪ J₁)` 是否真可供给，保证替换后的 C' 在 M 中闭。
   Q 必须包含整个被删带及新盘，且 Q⊆Ω，因而与两侧目标集合不交。
3. 核心等式是 `frontier Q \ C' = ψ '' (J × Ioo 0 1)`，且这条安全开环带避开原 C。
   应取正则邻域被固定第二张盘切出的一个三球。整块正则邻域的剩余边界另有一个开盘，
   是不连通的，不能直接当作这里的 Q。请确认正确 Q 的边界恰能达到当前公式。
4. 输出是否强于原书或隐藏其他独立几何定理；如需修订，请保留真实路径绕行能消费的
   精确边界控制。仅有某个抽象环带或同胚类型不足以替代边界等式。
5. 联合 fixture 是立方体边界加中间水平盘，D₁、D₂ 为上下短 collar 延伸。
   H 为立方体内中盘两侧的两个点，K 为外部一点，故 H 不连通。请逐项核查其完整输出，
   尤其 Q、删除带相对开性和安全边界，而不是只核原命题的输入。

最后列遗漏义务、共同 fixture、最可能的意外。局部绕行论证失败不自动构成整个叶子
的反例；lead 将对照实际 Lean 假设复核外审意见。
