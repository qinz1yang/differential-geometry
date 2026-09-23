# Section 34 (compact form), the source face order: is `compactSourceFace_iff_cutLe` provable from the cut frame as written?

Status: request written by the lead on 2026-09-23 after the lease-c worker's analysis
(`Skeleton/OPUS_FILL_LOG_C.md`, `## compactSourceFace_iff_cutLe — STUCK (not "short")`) and the
earlier due-diligence note `consult/Q-section34-terminal-due-diligence.md` (SUSPECT on the
non-compact twin `section34SourceFace_iff_cutLe`).  No statement has been changed.

请按同目录 `REVIEW-TEMPLATE.md` 审查 `liao9yuan/differential-geometry-dev` 的
`moise-integration`（镜像提交见 lead 发送时附注），文件 `Skeleton/Section34Compact.lean` 的叶子
`compactSourceFace_iff_cutLe`（第 330 行）及其词汇（真模块 `Section34CompactVocabulary.lean`：
`Section34BoundedLabel` 第 42 行、`Section34CompactCutStep` 第 233 行、`Section34CompactCutLe`
第 254 行、`section34CompactCutNeighborhood` 第 258 行、`Section34CompactCutFrame` 第 291 行，共
27 款；`section34Face src l = {m | src m ⊆ src l}` 在 `Section34Frame.lean` 第 296 行）。请用中文，
约 1500 字；反例必须逐款满足 `Section34CompactCutFrame`。

叶子：`∀ l m, src m ⊆ src l ↔ Section34CompactCutLe m l`，即源切割的十类胞腔（顶点球、四面体球、
分割盘、面盘、patch、面弧、边弧、标记点、外面、外弧）之间的集合包含恰是 `CutStep` 的自反传递
闭包。切割框架给出：每个 `src l` 是 `IsPLCellOn (dim l)` 的 PL 胞腔，`srcBd l` 是真子面之并
（集合意义的面），两胞腔之交是公共面之并，包含蕴含维数下降，以及各类胞腔的公式
（面弧 `= V_w ∩ D_σ`，标记点 `= D_e ∩ D_σ`，patch `= Q_t ∩ V_w`，边弧 `= Q_t ∩ D_e`，
外面 `O_w = closure (srcBd V_w \ (C ∪ ⋃ D_e))`，外弧 `o_e = closure (srcBd D_e \ C)`，
面盘/四面体球 `= closure (conv σ \ ⋃ V_w)`），不相交的非关联对，`D_e = V_w ∩ V_w'`，
`w ⊆ V_w`，以及每个三角形是某四面体的面。

工作者的发现（lead 已对照定义核实）：

1. 方向 `⇐` 中有两步不由任何一款直接给出：`CutStep (.faceArc a) (.outerFace o)`（`a.1.2 = o.1`，
   `conv σ ⊆ frontier K.space`）要求 `V_w ∩ D_σ ⊆ closure (srcBd V_w \ (C ∪ ⋃ D_e))`；
   `CutStep (.markedPoint p) (.outerArc q)` 要求标记点在 `closure (srcBd D_e \ C)` 中。两者都
   说"顶点球/分割盘在边界面处穿过 `∂C`"。lead 的推导：由第 7–9 款，边界面 `σ` 的面弧是
   patch `(t, w)` 的真面（第 8 款），故落在该 2-胞腔的内蕴边界上；`∂V_w` 是 PL 2-球面，弧的
   内点两侧各有一个 2-胞腔，`σ` 只属于一个四面体 `t`，另一侧不在 `C` 内，而 `D_e ∩ D_σ` 是单点，
   故弧的内点是 `srcBd V_w \ (C ∪ ⋃ D_e)` 的极限点，取闭包得整条弧。这需要"PL 3-胞腔的边界是
   2-流形"和"2-胞腔内蕴边界的唯一性"（树中尚无此 API，见 Q 注释第 4 节）。不短，但似乎可推。
2. 方向 `⇒` 依赖位置事实：例如 `σ` 为内部面而其某条边 `e' ⊆ ∂C` 时，标记点 `D_{e'} ∩ D_σ`
   若恰落在 `e'` 上且在 `srcBd D_{e'}` 上，则 `src (.markedPoint p) ⊆ src (.outerArc q)` 成立
   而 `CutStep` 因 `conv σ ⊄ frontier K.space` 为假。框架没有"标记点与面弧落在 `conv σ` 的
   相对内部"或"图的每条边被其两端的顶点球覆盖、与 `D_e` 恰交于一个内点"的款项。

请裁定：

1. 在 27 款之下，叶子是否为真？请给出一个逐款满足框架、使 `⇒` 或 `⇐` 失败的退化位置（明确到
   可以逐款核对），或说明现有款项（特别是第 7–10 款与 `∀ l, ∃ m, dim m = 3 ∧ src l ⊆ src m`）
   已排除所有退化位置并给出五行证明纲要，指出昂贵的一步。
2. 若需补款：由于框架的生产者 `exists_compactCutAndGraph` 尚未证明（本文件第 218 行的叶子），
   加款的代价只在生产者一侧。请给出最小的补款集合，使本叶子变成短证明，例如源侧铺砌
   `srcBd V_w = ⋃_{e ∋ w} D_e ∪ ⋃_{t ∋ w} X_{tw} ∪ O_w`（`w` 为边界顶点时）、
   `srcBd D_e = ⋃_t I_{te} ∪ o_e`、标记点与面弧在 `conv σ` 的相对内部、图的边被其两端球覆盖；
   并说明其余消费者（`exists_compactFaceDisks`、`exists_compactResidualBalls`、
   `compactTargetRecognition`、`compactTrace_of_noOperation`）只是多得假设。写出 Lean 形式。
3. 非紧孪生 `section34SourceFace_iff_cutLe`（`Skeleton/Section34Terminal.lean` 第 179 行，输入
   `Section34NormalPlus`，其中的 `Section34CutFrame` 见 `Section34Frame.lean` 第 495–530 行，
   `Section34CutStep` 第 594 行）是否有同样的问题？Q 注释说它默认了"带面弧的三角形是某四面体
   的面"；紧形式已加此款。若需补款，请给出与紧形式一致的款项，以便一次修两处。

最后报告：叶子是否可照现状证明；是否需要补款及最小集合；最可能的意外。外审是证据而非裁决；
lead 会对照 Lean 逐条核实，并报告分歧。
