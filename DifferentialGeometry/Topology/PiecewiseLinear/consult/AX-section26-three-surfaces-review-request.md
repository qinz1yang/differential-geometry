# Section 26.7: first three-surface producer review

Status: ANSWER RECEIVED AND CHECKED, 2026-09-22. All four statements are reviewed OK and
frozen; their proofs remain OPEN and the two-boundary-component Lean fixture is UNTESTED.
The answer and lead due diligence are recorded in
[BA](BA-section26-three-surfaces-first-review-digest.md). The original request follows;
the existing corrected `Moise267` statement has not been changed.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`df6cbdc7481ef9b3a57cb72df280dff9718fd918`，文件 `Skeleton/Section26ThreeSurfaces.lean`。
先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.l、`MoiseChain.lean` 的 `Moise267`。
原书 p. 195 及三弧定理 2.7（pp. 20–21）。约 1500 中文字，OK 只列一行。

独立编译恰好四条 sorry，装配类型仍为 `moise267 : Moise267`，四叶外无直接 sorry。
真实边界粘合、曲面内部连通与稠密、闭曲面有界侧定理已检查公理闭包。不得重加共同
边界的连通性：当前命题只要求它非空，允许多圈共同边界。

请逐叶裁定，重点为：

1. `exists_triod_chart_at_common_boundary` 只产生一个适当的规则边界点，非任意指定点。
   比书中的小横截盘更完整：要求真正 PL 乘积图卡，其源域内三曲面成员资格分别等价于
   三个标准半平面的成员资格。有限 PL 片与共同边界的规则边是否足以供给此加强。
2. `exists_surface_interior_frontier_contact` 只输出补分支与某片内部的一个边界接触点；
   一维共同边界不能单独支撑整个补分支的 frontier。请检查所有补分支，而不仅无界分支。
3. `isOpen_preimage_frontier_component_surface_interior` 是单曲面内部、远离另一闭障碍
   的局部开放性，既不假定也不输出整个曲面包含于 frontier。装配用已有连通性、闭性
   与稠密性传播到全片。x 位于障碍内时 component 为空，这个极端也应成立。
4. `exists_frontier_pair_witnesses_of_triod_chart` 由三弧循环次序以及每一对曲面构成的
   连通闭组合曲面，给出两片接触点和第三片异侧点。是否足以阻止不同局部扇区成为同一
   全局侧；有没有把目标全片边界公式或有界性暗中塞回叶子。后两者应由装配完成。
5. 联合 fixture：取 PL 环面的两个互补环带，再把其中一个环带的副本向内推，固定
   两条边界圈。得到三个内部分离、共同边界有两个分支的环带。请核图卡、接触点、
   无界分支边界以及第三片处于有界侧的同一组数据；当前只是 UNTESTED 的纸面模型。

最后列遗漏义务、共同 fixture、最可能的意外。FALSE 必须给满足全部字段的联合反例；
外审是证据而非裁决，lead 会核对 Lean 原文及原书后再修改骨架。
