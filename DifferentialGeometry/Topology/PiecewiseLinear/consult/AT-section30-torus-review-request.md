# Section 30.6--30.7: first producer statement review

Status: ANSWER RECEIVED AND CHECKED, 2026-09-22. All seven statements are reviewed OK and
frozen; their proofs and both joint Lean fixtures remain OPEN/UNTESTED. The answer and lead
due diligence are recorded in [BC](BC-section30-torus-first-review-digest.md). The original
request and fixed snapshot follow; the conditional assemblies do not close the named inputs.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`f3a1e6ba2f153cc1df42b50c9da4d8ec95def22d`，文件 `Skeleton/Section30Torus.lean`。
先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.h 和本文件的模块说明；书为 Moise
pp. 216–218。约 1500 中文字，OK 只列一行；反例必须同时满足当前 Lean 的全部假设。

七叶已独立窄编译，只有七条预期 sorry。三个真实装配分别为
`moise306_of_moise252`、`moise307_of_moise306_of_moise252`、`moise307_of_moise252`。
八个被复用的真实供给定理公理闭包均无 sorryAx；装配仍经新叶含 sorryAx。

请逐叶裁定，特别检查：

1. 30.6 已有 `IsToroidalShell.exists_separating_surface_bettiOne_eq_two`，输出有限、连通、
   可定向、Euler 特征为零的分离曲面。剩下 genus-one recognition 是否恰当；不能删掉
   可定向性而把 Klein bottle 一起纳入。PL torus 的有限组合曲面三角剖分是否独立可供给。
2. `subset_interior_of_nested_tori` 的边界、regular-closed、内外连通条件是否足够确认
   是同一个有界区域，并推出两条严格嵌套包含。所有 ambient interior 都在 R³ 中。
3. 环面到实体环面内部的非平凡基本群核，与嵌套环面包含不零伦，是否分别由 Z²→Z 和
   shell 回缩供给，不暗用 30.8 或任何逼近定理。现成 `SurfaceEssentialDisk` 从 25.2
   在指定开集内生产实际 PL essential disk，故装配没有另收无限制 26.4。
4. 外压缩叶结论要求一个 PL 三球 B，`R.space ⊆ interior B` 且 `B ⊆ U`。任意开 U
   已包含紧的 R 和整张压缩盘，是否足以用同一正则邻域保持此支撑控制？只证明压缩球面
   包一个三球不够。内压缩叶要求两个有限 PL 三球之并恰为 R，交为两张不交边界盘；
   是否真能从该盘获得，且没有把 `HasCylindricalDiagram` 换名当成叶子。
5. 给整链的共同非退化嵌套环面 fixture；外压缩叶另给可满足其局部假设的模型。外分支
   在完整嵌套上下文中不可能，不等于这个独立局部叶空泛。当前 fixture 都是 UNTESTED。

最后列遗漏义务、共同 fixture、最可能的意外。外审是证据而非裁决；lead 会逐项核反例。
