# CGN edge matching: which hypothesis does the frozen leaf lack for the orientation character?

Status: request written by the lead on 2026-09-23 after the Codex lane's partial delivery on the
edge matching (`Skeleton/FILL_LOG.md`, section "Codex item 7 — CGN edge matching, checked partial
layer"; eleven real modules, no leaf closed) and the earlier worker analysis
(`Skeleton/OPUS_FILL_LOG_D.md`, "exists_section34EdgeMatching — STUCK"). No statement changed.

请按同目录 `REVIEW-TEMPLATE.md` 审查 `qinz1yang/differential-geometry-dev` 的 `codex/moise-integration`
（提交见 lead 发送时附注），文件 `Skeleton/ControlledGraphNeighborhood.lean` 的叶子
`exists_section34EdgeMatching`（第 537 行；接口在第 AC 轮外审冻结）及其装配（第 617–660 行），词汇
`Section34PiercingConditions`（`Section34Frame.lean` 第 1011 行）、`Section34VertexPreparation`
（第 926 行）。先读 `Skeleton/OrientationCharacterBridge.md`（六个子叶）、`FILL_LOG.md` 的
"Codex item 7" 一节（已证 11 个模块：`GraphCoboundary` 的 ZMod 2 上边界引理含自环重边、来源分割盘不交、
球面补盘的平面图表、每条边一张共用的盘映射 `φ e`、顶点标记落入 `interior (Dv w)`），以及
`OPUS_FILL_LOG_D.md` 中该叶的 STUCK 段。请用中文，约 1500 字；反例必须逐款满足叶子的实际假设。

lead 已对照 Lean 核实的事实：

1. 叶子的 `hpack : Section34PiercingConditions …` 共 22 款，**没有** `G w` 与 `h` 的任何距离界。
2. 生产者 `exists_section34PiercingPackage`（第 371 行，开放叶）在 `Section34PiercingConditions`
   之外单独返回 `∀ w, ∀ x ∈ Cc w, dist (G' w x) (h x) < ε w`；装配把它取为 `hG₁dist`（第 619 行）。
3. 受保护圆移除 `exists_section34ProtectedCircleRemoval`（第 519 行）返回新的 `G₂` 及
   `hoff₂ : ∀ w, EqOn (G₂ w) (G₁ w) {x ∈ Cc w | ∀ e, G₁ w x ∉ interior (Sp e)}` 和
   `∀ w, EqOn (G₂ w) (G₁ w) (simplexBody 𝒦' w.1)`（装配丢弃了后者）；不返回距离界。
4. 调用处还在作用域里的：`hcore₂ : ∀ w, h '' Kcore w ⊆ interior (G₂ w '' Cp w)`、
   `hDmark : ∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w)`、`hSpK`；叶子一个也没收到。
5. `Section34VertexPreparation` 第 969 款：`∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (ε w) ⊆ interior (Q w)`；
   第 937 款：`h '' Cc w` 落在极大图册的一张图卡里；第 999 款是对任意 `F` 的稳定性款
   （`(∀ z ∈ Cp w, dist (h z) (F z) < ε w) → h '' Kcore w ⊆ interior (F '' Cp w)`）。
6. `Section34PiercingConditions` 第 1034 款：`∀ w, IsPLHomeomorphInto 3 (G w) (Cp w)`。

Codex 卡住的两点：(a) 沿图的每个 mod 2 边循环 `F`，`Σ_{e∈F} (sourceSign e + targetSign e) = 0`
（源与目标标记球面图表在共用盘上的取向变化之和）；它认为需要整胞腔的接近性，而叶子收不到；
(b) 各顶点的参考球面映射在共用盘上与选定的 `φ e` 逐点一致，需要先有 (a) 的顶点符号做正向修正。

请裁定：

1. 在现有 22 + 14 款下（无距离界），(a) 是否可推？若不可，请给最小补款。候选 A（直接转发生产者输出，
   调用处由 `hoff₂` 与 `hG₁dist` 立刻得到）：
   ```lean
   (hGdist : ∀ w, ∀ x ∈ Cc w, (∀ e, G w x ∉ interior (Sp e)) → dist (G w x) (h x) < ε w)
   ```
   候选 B：只在标记附近的接近性（某个含 `simplexBody 𝒦' w.1` 的开集上）；候选 C：把取向条款
   本身写进 `Section34PiercingConditions`，由生产者叶证明。哪个最小且调用处可供？
2. 路线核对：`G w` 是连通胞腔 `Cp w` 上的嵌入（第 1034 款），`h` 是 `U` 上的嵌入，故 `G w` 相对 `h`
   的局部度在 `Cp w` 上恒定；在 `Cc w \ ⋃ interior (Sp e)` 的某个开子集上 `G w` 与 `h` 相距小于
   `ε w`，而 `ball (h x) (ε w) ⊆ interior (Q w)` 落在一张图卡里，直线同伦不经过原点，故相对度为 `+1`；
   于是源与目标在每个共用盘两侧的取向变化相同，任何循环和为零，不需要 `U` 或 `M₂` 的整体可定向性
   （`U` 非定向、循环有实心 Klein 瓶邻域时亦然）。请确认或指出漏洞（例如 `Cc w \ ⋃ interior (Sp e)`
   可能没有内点；`Sp e` 与 `G w '' simplexBody`、`h '' Kcore` 不交是否足以保证）。
3. 对 (b)：以"每条边一张共用 `φ e`，每个顶点一张参考球面映射，再由顶点符号做 `IsPLCirclePositive`
   修正"的顺序（桥笔记第 2、5 项）是否足够，还是参考映射必须在符号确定之后再选？
4. 文件整体：`exists_nested_torus_of_deleted_family`（叶子结论 (f)）除 `CyclicBallUnion`、
   `Section34FaceTorusCycle` 与环面壳之外是否还缺输入？

最后报告：需不需要补款及最小集合；(a) 的路线是否成立；最可能的意外。外审是证据而非裁决；
lead 会对照 Lean 逐条核实，并报告分歧。
