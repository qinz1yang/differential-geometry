# Compact Section 34: second statement review (interface changes only)

Status: request written by the lead on 2026-09-22 after the first review (digest AS, snapshot
`09672b87`); its two FIX verdicts were applied to the skeleton and are the object of this round.

请按同目录 `REVIEW-TEMPLATE.md` 审查
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`a43963103731be1339f47f85c871388cfa383563`，文件
`Skeleton/Section34Compact.lean`（12 个开放叶子，第 929–1111 行）。先读
`consult/AS-section34-compact-first-review-digest.md`（上一轮的裁定和 lead 的核对）、
`FREE_INPUTS.md` 的 B1.b.8、`Skeleton/README.md`。请用中文，约 1200 字；上一轮已 OK 且本轮
签名未变的十个叶子只列一行确认；反例必须逐项满足当前 Lean 假设。

这是 `Moise331`、`Moise305Tame` 到 `Moise341OnNeighborhood`，再经已证明的 inward push 到
`Moise341` 的条件装配。独立复编为退出码 0、恰好 12 条叶子 sorry。P2–P5 的非紧版本
（`Skeleton/Section34Normalization.lean`）本日已由证明工作者关闭 P5（`Section34TerminalFaceBalls`，
Zorn 引理，去掉了三个未用假设）并交付 P3 的两块砖（`ChartTameNestedCells`、
`CurveCrossingGeneralPosition`），可作为本文件同名叶子的参照。

本轮只裁定两处按上一轮 FIX 修改的接口，以及一个上一轮未见的既成事实：

1. `exists_compactFaceEnvelopes` 新增输入 `hV : IsOpen V`（第 939 行）。请确认这是端点已经
   供给的信息（`moise341OnNeighborhood` 的 `hV`），不是新的未供给假设；并确认有了它之后
   辅助球的两个 collar 传输确实可在嵌入域内完成，没有再遗漏别的开集或紧性条件。
2. `exists_compactCompression` 新增输入 `hcar : Section34CompactCarrierControl K h ζ H`
   （第 1005 行附近）。请确认它在装配调用点确实可得，且它提供的
   `IsPLCellOn 3 (H t) (frontier (H t))` 足以在每个 incident carrier 内部做填充；上一轮的
   球面反例（有界侧含 `q`）在加了这个假设后是否真的被排除。
3. `Section34CompactGraphFrame.carriesFundamentalGroupOnto` 通过
   `carriesFundamentalGroupOnto_of_nestedSolidTorus` 真实调用嵌套环面 generator，并把 `hgen s`
   传给 `compactTraceHomology`；上一轮审的旧快照里没有这一步。请核对这条导出的假设链，
   以及从 generator 到整条 trace 的整 H₁ 满射仍是 `compactTraceHomology` 内部的证明义务而
   非新假设。

其余十个叶子（`exists_compactCutAndGraph`、`exists_compactFaceShellBalls`、
`exists_compactFaceBallsGeneralPosition`、`compactTraceHomology`、`exists_compactBigonSlide`、
`compactTrace_of_noOperation`、`exists_compactFaceDisks`、`exists_compactResidualBalls`、
`compactSourceFace_iff_cutLe`、`compactTargetRecognition`）签名与上一轮相同；如你发现与
上一轮 OK 裁定相抵触的新问题，请明确指出是哪个字段、哪条假设。

最后报告：本轮两处接口是否可以冻结；十二个叶子是否可以全部标为 frozen 并交给证明工作者；
最可能的意外。外审是证据而非裁决；lead 会对照 Lean 逐条核实，并报告分歧。
