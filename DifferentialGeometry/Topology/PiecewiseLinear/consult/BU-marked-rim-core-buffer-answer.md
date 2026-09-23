# BU — marked rim core buffer：审查答复

**审查基准：** `liao9yuan/differential-geometry-dev:moise-integration`，固定提交 `f1cac4bc4997fb3b8c535d07b417648a75807858`。以下路径相对 `DifferentialGeometry/Topology/PiecewiseLinear/`。本文件是数学及源码接口审查，不是 Lean 编译、证明完成或公理审计；下面的签名均待编译核验，裁定是供 lead 核验的证据。

**读取限制：** 此提交上的 BU 请求、`DualCells.lean`、`DerivedNeighborhood.lean` 及下文列出的实际供应模块已读。请求所指的 `TubeEdgePairOverlap.lean`、`GraphDualCellRadialBoundary.lean` 在尝试的固定提交路径返回 404；另尝试了前者的 `Skeleton/` 路径及 qinz1yang 同提交路径，仍未取得文件。因此，不能声称独立读过这两份 Lean 证明或复核其零诊断记录。以下接受 BU 对它们结论的转述，并从实际定义重新给出所需数学核对。

## 1. 先纠正三处叙述；路线裁定

**推荐修复后的 (C)：面内 bridge disk → 单个顶点球的带标记棱柱 → 循环粘合 → 保中心解扭 → 对整个循环并集向外加 collar。** 不再要求 `C_v` 是以 `v` 为顶点的锥，也不另取较小的 `N(J)` 再试图吞下所有 arms。

`section34CompactGraphSkeleton K` 的实际定义是 **K 的一维骨架**；compact vocabulary 中的 `K'` 是另给的相容 subdivision，不是这个定义自动调用的 barycentric subdivision。`Section34CompactFaceTorusCycle` 目前证明的是 worker 选择 `K'=K` 时的**三个**顶点球。六顶点版本要换用实际 rim 上的六个 subdivision vertices，不能仍写 `v ∈ s.1` 后声称已覆盖六个球。

| 候选/断言 | 裁定 | 原因 |
|---|---|---|
| (A) 只把现成 unmarked product 重新导出为 marked product | UNDISCHARGEABLE | 构造没有保留指定 rim；缺失的是 pair/axis 控制，不是一个遗漏的投影。 |
| 给 (A) 原定理原假设直接加“L 是零截面” | FALSE | 原假设允许 L 位于 ambient manifold 的边界。 |
| (B) 同一 derived 层级的 `N(J) ⊆ interior N_s` | FALSE | 下文的 `y=(c+d)/2` 同时在 `N(J)` 和 `frontier N_s`。 |
| 以 `v` 为锥顶，径向延拓 `frontier C_v` | FALSE | 同一射线上有两个不同的 frontier 点。 |
| (C) 用面内 bridge disk 作两步 straightening | FIX | 数学上有可产出的局部证书；需要相对弧及相对中心的两个实质新接口。 |
| 正确索引、含 `K.space ⊆ interior M.space` 的 compact buffer | FIX（证明路线，不改目标） | 未发现满足完整假设的反例；下列装配预计可证，尚非已验证的 Lean producer。 |

### (A) 究竟忘了什么？

实际调用链是 `NeighborhoodCylinder.exists_cylindricalDiagram_derivedNeighborhood_circle` → `CylindricalClassification.exists_cylindricalDiagram_derivedNeighborhood_circle_eq_ends` → `SolidTorusProduct.isTopologicalSolidTorus_derivedNeighborhood_circle`。

第一步把邻域分成两球，任选公共端盘的 parametrisation，并使用未标记的 ball-pair extension；既没有输出 `f({stdCenter 1}×I)=L.space`，也没有保留弧的原像。第二步的 pseudo-isotopy 又没有固定中心条款。因此，对选出的最终 diagram，L 的原像只能写成整个 cylinder 中的 `f ⁻¹' L.space`；没有证据说明它是某个常值截面，甚至不能从已导出的结论识别它是哪条曲线。等端 diagram 的 axis image 确实是它自己所定义的 product core，但没有等式把它认作 L；不能把任意 interior point 的 axis image 当成 L。

有一个值得复用的**真正 SMALL** 部分：`CylindricalProduct.exists_homeomorph_prod_circle_of_eq_ends` 的第二个结论明确给出 `(e.symm (x,t) : E3) = f(x,t)`。一旦上游已有正确 axis，商空间这一步确实保留它。丢失发生在更早的选图和解扭，不在这个商定理。

另一个完整反例：取有限三角剖分的三球 M，令 L 为其一个边界三角形的 rim。L 是连通、无边界的一维组合流形，M 可定向，全部原 unmarked 定理假设成立。`derivedNeighborhood M L ⊆ M.space`，故 L 的点不可能在该邻域的**环境内部**；而 `D²×S¹` 零截面的像必在环境内部（不变域定理）。这否定“原假设不动直接标记”的普遍加强，不否定 BU 中另有 interior margin 的目标。

## 2. 实际 flag 计算：既给反例，也给正确的 bridge

取一个内层非退化四面体的全复形 K，并在更大的同心放大四面体内三角剖分其壳层，得到有限组合三球 M，保留 K 为子复形且 `K.space ⊆ interior M.space`。例如内层顶点为 `0,e₁,e₂,e₃`，外层是绕重心放大三倍的四面体；壳层取相容拉序三角剖分。取 `s={v,u,w}={0,e₁,e₂}`，`L=restrict K (section34CompactGraphSkeleton K)`。每个 rim 顶点都有向 `e₃` 的第三条 arm，s 的边又全是 K 的边界边：这不是无 arms 或边界消失的特例。

记 `c=b({v,u})`、`d=b(s)`。在 `M'` 的三角形 `[v,c,d]` 中，实际 `DerivedNeighborhood.derivedNeighborhoodFaces` 选出第二次细分的六个小三角形中的四个，恰为

\[
\max(\lambda_v,\lambda_c)\geq\lambda_d.
\]

原因是 L 的 face-centroids 在这一个 flag triangle 中恰有 `v,c`，没有 `d`。在第二次细分的极大 flag 中，最小顶点必须是 `v` 或 `c`。`DualCells.mem_graphDualCell_faces_iff_of_flag` 再把它限制到 v 的 closed star。

于是 `y=(c+d)/2`、`x=(v+c+d)/3` 均属于 `frontier C_v`，并且 `x=v+(2/3)(y-v)`；在上述 barycentric coordinates 中稍微增大 `λ_d` 就得到邻域外的点。这直接核对径向反例，不把“星形”误当作“frontier 径向单射”。

令 J 为 s 的 rim 子复形，所有对象使用同一个 ambient M、同一个 derived 层级。`y∈N_M(J)`，因为 `M'` 的边 `{c,d}` 含 J 的 edge-centroid c。另一方面

\[
y_\epsilon=(1/2-\epsilon)c+(1/2+\epsilon)d\notin N_M(L),\qquad 0<\epsilon<1/2.
\]

`y∈N_s⊆N_M(L)`，所以 `y∈frontier N_s`。这逐项满足实际 compact 数据，否定 (B) 的严格包含。改成更深 subdivision 可能取得较小邻域，但须另证 shrink/engulfing；单调性只有非严格包含，不能产生 buffer。

**正面证书。** 写 `c_-=b({u,v})`、`c_+=b({v,w})`。实际截面 `B_v=C_v∩[s]` 是边界依次为

\[
v,c_-,(c_-+d)/2,(v+c_-+d)/3,(v+d)/2,
(v+c_++d)/3,(c_++d)/2,c_+
\]

的 PL 八边形盘。其边界的一条弧是 `A_v=C_v∩rim(s)=[c_-,v]∪[v,c_+]`；另一条弧记为 β_v，则

\[
 B_v\cap\operatorname{frontier}C_v=\beta_v,
 \qquad A_v\cap\beta_v=\{c_-,c_+\}.
\]

B_v 的一维边界是其 PL 参数的 `stdSimplexBoundary 2` 像，不是环境 `frontier B_v`（后者是整个二维盘）。它证明 A_v 是球 C_v 中的**边界平行 proper arc**。这是比“C_v 是球、两个 cap 是盘”多出的必要证据：一般 proper PL arc 可以打结。允许 arms 留在整个 C_v 中；bridge 只用于证明指定弧不打结，不删减目标球。

## 3. 精确的候选子叶签名

这些是**拟议接口**，不是树中已有名字；`by sorry` 仅在本 Markdown 中表示待证明签名，没有创建或修改 Lean 文件。标准三角形的中心使用树中的 `stdCenter 1`，不是不属于该三角形的零向量。下面的 `BUBridge` 是显式盘证书；其供应者是 L1，不把未生产的“marked tube”重新包装成假设。

```lean
open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V2" => (Fin 3 → ℝ)
local notation "Δ" => stdSimplex ℝ (Fin 3)
local notation "p" => (stdCenter 1 : Fin 3 → ℝ)
local instance : DecidableEq E3 := Classical.decEq E3

def buV0 : V2 := fun i => if i = 0 then 1 else 0
def buV1 : V2 := fun i => if i = 1 then 1 else 0

def buBase : Set V2 := {x | x ∈ Δ ∧ x 2 = 0}
def buSides : Set V2 := {x | x ∈ Δ ∧ (x 0 = 0 ∨ x 1 = 0)}

def BUBridge (C A B : Set E3) (a b : E3) : Prop :=
  ∃ q : V2 → E3,
    IsPLHomeomorphOn q Δ B ∧ B ⊆ C ∧
    q '' buBase = A ∧ B ∩ frontier C = q '' buSides ∧
    q buV0 = a ∧ q buV1 = b

def buDisk : Set E2 := Metric.closedBall (0 : E2) 1
def buCircle : Set E2 := Metric.sphere (0 : E2) 1

def buZeroSection : Set (buDisk × buCircle) :=
  {q | (q.1 : E2) = 0}

-- A0 — SMALL: the face adapter supplies the disk used by L1.
theorem bu_triangleDisk
    (K : Geometry.SimplicialComplex ℝ E3)
    (s : Section34CompactSimplexIndex K 3) :
    ∃ F : Geometry.SimplicialComplex ℝ E3,
      F.faces.Finite ∧ F.faces ⊆ K.faces ∧
      IsPLBall 2 F.space ∧
      F.space = convexHull ℝ (s.1 : Set E3) ∧
      (boundaryComplex 2 F).space = section34CompactSimplexRim s.1 ∧
      (boundaryComplex 2 F).faces ⊆
        (restrict K (section34CompactGraphSkeleton K)).faces := by
  sorry

-- L0 — SMALL: the source neighbourhood stays off the ambient boundary.
theorem bu_derivedNeighborhood_subset_interior
    (M L : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hLM : L.faces ⊆ M.faces)
    (hLint : L.space ⊆ interior M.space) :
    (derivedNeighborhood M L).space ⊆ interior M.space := by
  sorry

-- L1 — MEDIUM: local flag disk; F also permits the six-vertex version.
theorem bu_bridge_graphDualCell
    (M L F : Geometry.SimplicialComplex ℝ E3)
    [Finite M.faces] [Finite F.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hLM : L.faces ⊆ M.faces)
    (hLdim : ∀ e ∈ L.faces, e.card ≤ 2)
    (hFM : F.faces ⊆ M.faces)
    (hF : IsPLBall 2 F.space)
    (hFint : F.space ⊆ interior M.space)
    (hJL : (boundaryComplex 2 F).faces ⊆ L.faces)
    {u v w : E3} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h0 : ({u, v} : Finset E3) ∈ (boundaryComplex 2 F).faces)
    (h1 : ({v, w} : Finset E3) ∈ (boundaryComplex 2 F).faces) :
    BUBridge
      (graphDualCell M L v).space
      ((boundaryComplex 2 F).space ∩ (graphDualCell M L v).space)
      (F.space ∩ (graphDualCell M L v).space)
      (({u, v} : Finset E3).centroid ℝ id)
      (({v, w} : Finset E3).centroid ℝ id) := by
  sorry

-- L2 — NEW_THEORY: boundary-parallel arc, with two marked cap centres.
-- Deliberately does not prescribe BOTH entire cap parametrisations.
theorem bu_markedPrism_of_bridge
    {C A B D0 D1 : Set E3}
    (hC : IsPLBall 3 C)
    (hD0 : D0 ⊆ frontier C) (hD1 : D1 ⊆ frontier C)
    (hdis : Disjoint D0 D1)
    {r0 r1 : V2 → E3}
    (hr0 : IsPLHomeomorphOn r0 Δ D0)
    (hr1 : IsPLHomeomorphOn r1 Δ D1)
    (hb : BUBridge C A B (r0 p) (r1 p)) :
    ∃ ρ : V2 × ℝ → E3,
      IsPLHomeomorphOn ρ (Δ ×ˢ Icc (0 : ℝ) 1) C ∧
      ρ '' (Δ ×ˢ {(0 : ℝ)}) = D0 ∧
      ρ '' (Δ ×ˢ {(1 : ℝ)}) = D1 ∧
      ρ (p, 0) = r0 p ∧ ρ (p, 1) = r1 p ∧
      ρ '' ({p} ×ˢ Icc (0 : ℝ) 1) = A := by
  sorry

-- L3 — MEDIUM: glue SINGLE vertex prisms, not doubled edge prisms.
-- Addition in Fin (n + 3) is cyclic.
theorem bu_cylindricalDiagram_of_marked_cycle
    (n : ℕ) (C : Fin (n + 3) → Set E3)
    (ρ : Fin (n + 3) → V2 × ℝ → E3)
    (hρ : ∀ i,
      IsPLHomeomorphOn (ρ i) (Δ ×ˢ Icc (0 : ℝ) 1) (C i))
    (hmeet : ∀ i,
      C i ∩ C (i + 1) = ρ i '' (Δ ×ˢ {(1 : ℝ)}))
    (hcap : ∀ i,
      ρ i '' (Δ ×ˢ {(1 : ℝ)}) =
        ρ (i + 1) '' (Δ ×ˢ {(0 : ℝ)}))
    (hfar : ∀ i j, i ≠ j → j ≠ i + 1 → i ≠ j + 1 →
      Disjoint (C i) (C j))
    (hmark : ∀ i, ρ i (p, 1) = ρ (i + 1) (p, 0)) :
    ∃ f : V2 × ℝ → E3,
      IsCylindricalDiagram f Δ (⋃ i, C i) ∧
      f (p, 0) = f (p, 1) ∧
      f '' ({p} ×ˢ Icc (0 : ℝ) 1) =
        ⋃ i, ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  sorry

-- L4 — NEW_THEORY: relative-to-centre untwisting.
-- E3 matters: the embedded three-manifold supplies orientability.
theorem bu_untwist_preserving_axis
    {S : Set E3} {f : V2 × ℝ → E3}
    (hf : IsCylindricalDiagram f Δ S)
    (hclosed : f (p, 0) = f (p, 1)) :
    ∃ g : V2 × ℝ → E3,
      IsCylindricalDiagram g Δ S ∧
      (∀ x ∈ Δ, g (x, 0) = g (x, 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, g (p, t) = f (p, t) := by
  sorry

-- L5 — SMALL: the EXISTING quotient theorem retains coordinates.
theorem bu_zeroMarkedProduct_of_eq_ends
    {S : Set E3} {f : V2 × ℝ → E3}
    (hf : IsCylindricalDiagram f Δ S)
    (hends : ∀ x ∈ Δ, f (x, 0) = f (x, 1)) :
    ∃ Φ : (buDisk × buCircle) ≃ₜ S,
      Subtype.val '' (Φ '' buZeroSection) =
        f '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  sorry

-- L6 — MEDIUM: outward collar of the ENTIRE prescribed torus.
theorem bu_thickening_fixed_on_compact
    {N A U : Set E3}
    (hN : IsCombinatorialSolidTorus N)
    (hA : IsCompact A) (hAN : A ⊆ interior N)
    (hU : IsOpen U) (hNU : N ⊆ U) :
    ∃ P : Set E3, P ⊆ U ∧ N ⊆ interior P ∧
      ∃ e : N ≃ₜ P,
        ∀ x : N, (x : E3) ∈ A → (e x : E3) = (x : E3) := by
  sorry

-- Assembly target from A0 and L0–L6, NOT another geometric leaf.
-- This is the three-vertex worker specialization K' = K.
theorem exists_compactRimCoreBuffer
    {M K : Geometry.SimplicialComplex ℝ E3} [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hKM : K.faces ⊆ M.faces)
    (hKint : K.space ⊆ interior M.space)
    (s : Section34CompactSimplexIndex K 3) :
    let L := restrict K (section34CompactGraphSkeleton K)
    let Ns := ⋃ v ∈ (s.1 : Set E3), (graphDualCell M L v).space
    ∃ P : Set E3, P ⊆ interior M.space ∧ Ns ⊆ interior P ∧
      ∃ Φ : (buDisk × buCircle) ≃ₜ P,
        section34CompactSimplexRim s.1 =
          Subtype.val '' (Φ '' buZeroSection) := by
  sorry

end DifferentialGeometry.Topology.PiecewiseLinear
```

### 假设供应及证明费用（checks 4–6）

**L0。** `hLM,hLint` 来自 `hKM,hKint` 和 skeleton restriction。用边界子复形在 subdivision 下的相容性及 flag 判据，排除 `N_M(L)∩∂M`；再用 `frontier_space_eq_boundaryComplex_space`。不能只引用 `derivedNeighborhood_space_subset`：它只给 `⊆ M.space`，没有 interior。这里没有新的尺度选择。

**L1。** 三顶点时令 F 为 s 的面复形；从 simplex 的 affine independence/cardinality 得 `IsPLBall 2 F.space`，其 boundary complex 的 space 正是 `section34CompactSimplexRim s.1`。这正是 A0 `bu_triangleDisk`：取 `restrict K (convexHull ℝ (s.1 : Set E3))`，核对其面为 s 的非空子集、边界面为真子集。不是 graph-frame 假设。其余供应来自 `hKM,hKint`、`restrict_faces_subset`、`card_le_two_of_mem_restrict_section34CompactGraphSkeleton`。证明就是上面的八边形及边界识别。一般 F 时沿 v 的二维 link interval 拼这些 flag sectors，输出同一个 bridge；这是六顶点版需要的局部 fan 归纳，不能把三顶点算式直接 `simpa` 成六顶点。昂贵处是**准确识别 `B∩frontier C`**，仅证明 B 是盘不够。

**L2。** `C_v` 是球由 `hM.isPLBall_graphDualCell`；相邻交盘由 `graphDualCell_space_inter` 和 `hM.isPLBall_splittingDisk`；两个 cap 不交由 `graphDualCell_triple_inter_eq_empty`。中心参数 r 可由真实 `isTube_graphDualCell` 接 `IsTube.exists_centered_splitDisk_parametrization` 供应：前者需要 finite ambient、graph dimension ≤1、至少一条边及所有 graph vertices 在 `Int M`，这些都由当前 source 数据给出；不使用待构造的 graph frame。`hb` 由 L1。

证明 L2：相容三角剖分球、bridge 和 caps；在 bridge 的相对邻域中把 A 拉直到 β 的**内侧平行弧**；识别为标准平凡 proper arc；在边界球面匹配两个 cap 并固定端点；最后在标准球上用保极点的边界延拓取得棱柱。费用在第二步的 **relative PL arc straightening**，不能把 A 推到 β 本身，也不能对原 `C_v` 使用已否定的径向锥。当前检查到的 `TubeCenteredPrismCoordinates`、`SplitDiskCylinderCoordinates` 都没有这个轴条款。

**L3。** 对一个 circle 排序后，相邻交盘和中心相等由上述源数据给出；非相邻不交须由**rim 是 L 的 induced cycle**核验，再用 graph-dual-cell incidence。三顶点情况没有非相邻对；barycentric 六边形也没有 chord。先在一个 cap 选择参数，沿链用两张 cap 图的 transition 传播；它固定 p，故 axis 不变。闭合后只剩一个固定 p 的 disk monodromy。不要同时强迫两端任意给定的完整盘图：它们可能有不兼容的边界取向。也不要要求 `Path x x` 单射；`IsCylindricalDiagram` 恰好允许首尾识别。

**L4。** `CylinderEndMap.exists_isPLHomeomorphOn_endMap` 与顶端单射性给 monodromy `u p=p`。`IsCylindricalDiagram.isCombinatorialSolidTorus` 及 `CylindricalMonodromy` 的嵌入三维可定向性路线给正向边界映射。新义务是 **disk isotopy 保持 p**：先把正向边界 isotopy 沿以 p 为中心的标准盘延拓，再对固定边界且固定 p 的余项用相对 Alexander trick。这次锥发生在**标准盘**，与原 `C_v` 的径向反例无关。然后重参数化 f，逐时刻固定其 axis。按 NEW_THEORY 认领，不能直接引用现有 unpointed existential；重用其内部证明或可降低实现费用，但须先验证中心不动。

**L5。** 重用 `CylindricalProduct.exists_homeomorph_prod_circle_of_eq_ends` 的坐标等式，再接 `CenteredDiskSimplexMap` 的 `0 ↦ stdCenter 1` 图和 circle homeomorphism。这里要求的是拓扑 product；不要把圆盘的曲边边界错误地当作有限 PL polyhedron。

**L6。** `hN` 三点版由 `Section34CompactFaceTorusCycle` 的 source 恒等像特例供应；六点版用已有 `CyclicBallUnion.isCombinatorialSolidTorus_iUnion_of_cycle`，或 L3 的 diagram 加真实 cylindrical recognition。`hNU` 由 L0，`hAN` 由 L5 的零截面和不变域定理，`hA` 由有限 polygon 的紧性。取 `U=interior M.space`，对 **整个** `frontier N` 用 `Bicollar.exists_bicollar_of_isConnected`（必要时用其分支版），在 U 内并避开 A 缩 collar，选择内外方向并外推边界，拼接内部恒等映射。其二维 manifold、connectedness 来自组合环面的 frontier；two-sidedness 来自它确为 `frontier N`，不能无供应地假定。这个步骤不是 (B) 的径向 engulfing，也不要求 arms 本身是一条轴。

## 4. 装配与极端情况

装配顺序为 **A0 → L0/L1 → L2 → L3 → L4 → L5 → L6**。先得到 `Ψ : D²×S¹ ≃ₜ N_s`，零截面为指定 rim；再得到固定 rim 的 `e : N_s ≃ₜ P`，取 `Φ=Ψ.trans e`。L6 给严格 buffer。原 compact 目标是这一装配的 corollary，**不要再把它登记成另一个 NEW_THEORY 叶子**，也不要让 L2/L4/L6 消费完整 graph frame 或 Moise341：那会把所求对象作为供应输入。就此单独 brick 而言，`hK` 的整个三维流形条件没有被上述路线使用；`hKM`、有限性及指定三角形已够。保留原调用形状无妨，不要再加强这个冗余条件。

四种极端必须分开：**三顶点**取 L3 的 `n=0`；**六顶点**取 `n=3`，ambient、F、L 相容细分，union 的索引确为全部六个 rim vertices。**degree≥3** 只增加留在 C_v 内的 arms；L2 的像是完整 C_v，L6 膨胀完整 N_s，所以没有漏掉它们。**K 的边界边**没有问题，因为 `K⊆Int M`；若改成只在 K 内作邻域而不再有这一 ambient margin，(A) 的边界反例立即适用。**K'=K** 是允许的 source subdivision 选择，不是声称 `barycentricSubdivision K=K`；后者不适用于非退化三维复形。

还须拒绝一个未在四种极端中明说的推广：任意 polygon 上的顶点球不一定按 cycle 相交；若 L 在这些顶点之间另有 chord，L3 的 `hfar` 没有供应，不能仅凭“rim 是圆”调用循环球定理。真正离开 rim、终止于未选顶点的 arms，与连接两个已选顶点的 chord 不同。

**缺失义务：** 原始 flag bridge、其相对弧 straightening 和保中心解扭的真实 producer；此外保留 ambient-interior 与 outward-collar 两个控制包装，不将它们当作现成结论。

**共同非退化 fixture：** 上述内层四面体及严格更大的相容壳层 M，同一边界三角形、每个 rim 顶点的第三条 arm；相容细分给六点版本。它满足源假设并允许所述几何证书，但这里没有声称已构造并编译整条 Lean inhabitant。

**最可能的意外：** unmarked 的端盘匹配或 pseudo-isotopy 再次移动了选定中心；需逐步保留 axis 等式，而不是事后以“生成元”“同伦等价”或“也是环面”替代零截面。
