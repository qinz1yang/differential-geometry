# Section 34 P4, the disk-outside-the-ball case: is field 4 of the invariants preserved?

Status: request written by the lead on 2026-09-22 after the lease-a worker's analysis
(`Skeleton/OPUS_FILL_LOG_A.md`, `# Batch 7 (P4, bigon)`, entry `exists_section34Compression`,
item 3).  No statement has been changed; the case is frozen pending this review.

请按同目录 `REVIEW-TEMPLATE.md` 审查 `liao9yuan/differential-geometry-dev` 的
`moise-integration`（镜像提交见 lead 发送时附注，与 `a52998be8` 之后的任一提交等价，相关文件
未变），文件 `Skeleton/Section34Normalization.lean` 的叶子 `exists_section34Compression`（P4）及其
词汇 `Section34FaceBallInvariants`、`Section34Compression`（真模块
`Section34FaceBallVocabulary.lean`，第 136 行起）。先读
`Skeleton/OPUS_FILL_LOG_A.md` 的 `# Batch 7` 中 P4 条目的第 3 点（case (b)），以及
`FREE_INPUTS.md` 的 B1.b.7。请用中文，约 1200 字；反例必须逐项满足当前 Lean 假设。

问题只有一个。`Section34Compression … s` 给出一个顶点球 `tgtVBd w` 上的压缩盘 `Dj`，其边界
`Jd = Dj ∩ fblBd s` 在面球 `fbl s` 的边界上，`Dj \ Jd` 与其他面球不交。P4 要求产出新的面球族
`g`，使 `Section34FaceBallInvariants` 的十个字段保持，`Section34Compression` 的 rank 下降。
书上（Moise 第 34 节，Operation 1，Lemma 6）只在边界上检查 5(5)。

- 情形 (a)：`Dj \ Jd ⊆ interior (fbl s)`，沿 `Dj` 切开 `fbl s`，取含 rim 的那一半。工作者已
  证明这一步的一般砖 `IsPLBall.exists_compression_of_proper_disk`（`ProperDiskCompression.lean`），
  并认为字段 1–6、8–10 与两个计数可以完成，字段 7（`fblBd s ∩ frontier T_s` 在面环面 `T_s`
  上 carry `H₁`）需要两个环面事实（不交的本质圆同调至多差符号；carry 的平面子曲面有一条
  carry 的边界圆）。不必审这些。
- 情形 (b)：`Dj \ Jd` 在 `fbl s` 之外。唯一可用的新球是 `fbl s ∪ X ∪ (Dj 之外的 collar)`，其中
  `X` 是 `E ∪ Dj` 围出的口袋（`E ⊆ fblBd s` 是 `Jd` 在 `fblBd s` 上截出的一侧）。工作者指出：
  当 `X` 落在顶点球并集 `⋃ w, tgtV w` 之外（`fbl s` 搭在 `V_w` 上的穹顶下方的口袋）时，另一个
  面球 `fbl s'` 可以经 `E ∩ interior V_w`（`w` 为公共顶点）进入 `X`，并在 `X` 内离开 `V_w`；
  `hinv` 的字段 4（`s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)`）不排除这种位置；于是
  增大后的球与 `fbl s'` 的交集会跑出 `interior (⋃ w, tgtV w)`，字段 4 失败。这不是完整反例
  （或许存在别的新球），但书上的构造在这里失效。

请裁定：

1. 在当前 Lean 假设下（`hinv`、`Section34Compression`、`Section34Exterior`、切割框架与图框架
   的全部字段），情形 (b) 中上述位置是否真的可能出现？请给一个逐字段满足假设的具体模型，
   或证明某个已有字段（例如字段 3、字段 6、`Section34Exterior`、图框架第 8 款）已经排除它。
2. 若可能出现：P4 的冻结陈述是否仍然为真（存在别的满足十个字段且 rank 下降的新球族），
   还是陈述需要修正？若需修正，给出最小修正（例如把 `Section34Compression` 的情形 (b) 限制为
   `Dj ⊆ ⋃ w, tgtV w`，或在字段 4 上做何种放宽），并说明 P5（已证，Zorn）、bigon 滑动、
   两个 trace 叶子和 `Section34Terminal` 的消费者是否受影响。
3. 若不可能出现：指出排除它的确切假设链，以便工作者按此证明。

最后报告：情形 (b) 是否可以照书证明；是否需要改陈述；最可能的意外。外审是证据而非裁决；
lead 会对照 Lean 逐条核实，并报告分歧。
