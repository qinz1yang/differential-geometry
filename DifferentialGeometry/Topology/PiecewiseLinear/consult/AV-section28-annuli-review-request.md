# Section 28.6: first annulus producer statement review

Status: READY FOR OWNER REVIEW. Both leaves are UNREVIEWED; the common fixture is UNTESTED.

请按同目录 `REVIEW-TEMPLATE.md` 审查 GitHub
`liao9yuan/differential-geometry-dev` 的 `moise-integration`，固定镜像提交
`510a3d1015405d12ca480a4bbb9134b9666077ea`，文件 `Skeleton/Section28Annuli.lean`。
先读 `Skeleton/README.md`、`FREE_INPUTS.md` B1.j、实际命题 `MoiseChain.lean` 中的
`Moise286`；原书 p. 204。约 1500 中文字，OK 只列一行，反例核对完整 Lean 假设。

独立窄检查恰好两条 sorry；`moise286 : Moise286` 的装配未改命题签名，真实消费两叶，
公理闭包只有标准三项及这两个开放叶引入的 sorryAx。

关键区别：第一叶提出“整族多边形的共同 PL 乘积坐标”，明确强于原书 28.3 写出的
standard position，不能把这项加强视作书中原句。它只要求边界坐标，不要求延拓到
整个实体环面，也不能反向调用正要证明的 28.6。

请重点裁定：

1. `exists_product_coordinates_for_disjoint_essential_polygons` 是否能从当前 CST、
   两两不交 PL 圈及“在环面边界上不围 PL 盘”的 frozen 假设，得到两个 PL 圈 J、Q
   和一个 `J × Q → frontier S` 的 PL 同胚，使全族 G_i 同时成为不同 J-fibers？
   尤其核对 essential 的当前定义能否供给所需同伦/同位结论，是否偷偷假定分类定理。
2. `exists_annulus_parametrization_of_product_circle_cut` 不再收实体环面或 essential
   假设，输入是真实的共同坐标及有限单射标记。输出必须是实际 connectedComponentIn
   的 ambient closure，且两端恰为两个原标签，不是某个抽象同胚的环带。
3. `n > 1`、n=2、任意排列标签、极短标记间隔是否都可处理。不能先假定 Fin n 的编号
   已按循环序排列；也不能把两端取成同一圈。现成 CircleArcs、PL product、closure
   transport 和 AnnulusCylinder API 已查，但尚未代替这两项供给。
4. 共同 fixture 是方实体环面 `1 ≤ max(|x|,|y|) ≤ 3, |z| ≤ 1` 上位于 y=0、正负
   x 两侧的两个矩形经圈。请给共同坐标与 no-disk 证书的数学核查；目前没有联合 Lean
   inhabitant，不能把图形描述算作已认证 fixture。

最后列遗漏义务、共同 fixture、最可能的意外。强度或供给接口有问题请给精确修订，
不要仅以“原书路线不同”判 FALSE；完整反例仍需满足每项 Lean 假设。
