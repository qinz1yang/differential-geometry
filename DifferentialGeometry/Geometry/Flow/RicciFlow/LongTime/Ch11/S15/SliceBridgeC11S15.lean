import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileDefsC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceSeeds_CX2

set_option autoImplicit false

/-!
# S-CH11-S15 G2a：P6 (b) 的 history late 形 ⇒ RegularSlice 形（`_C11S15`）

`LargerBallCanonicalLateSupply_C11E`（= ch12 `P6_S23` 的体 = `P6LateSupply_P6A`）是 **RegularSlice 形**：
`s : RegularSlice F.observation`，history 取 `s.history = F.observation.observe s.time _`，
点取 `(s.history.stageAt ⟨s.time, _, le_rfl⟩).Carrier`。而 P6A 的 `LargerBallCanonicalLateAt_P6A`、
`largerBallCanonicalLateAt_of_le_one_P6A` 与 G1 都是 **history late 形**：`F.tower.history n`、
`t ∈ Icc 0 horizon`。两者之间树内原无桥。

桥用 Ch12 的 slice ⇔ tower 对齐（`SliceSeeds_CX2`）：`s.history = (F.tower.history ⌈s.time⌉).restrict cut`
（`slice_history_restrict_CX2 := rfl`），`hasSmallParabolicCurvature` 沿 restrict 提升
（`smallParabolicCurvature_of_restriction_CX2`），ball / 体积 / 点沿 `HEq` 传递
（`metricBall_heq_CX2`、`ballVolume_heq_CX2`、`restrictPoint_heq_CX2`）。本文件补两个 `HEq` 传递引理
（标量曲率、canonical witness）与桥本身。无新假设。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 标量曲率沿 stage 相等 + metric / 点的 `HEq` 不变。 -/
theorem metricScalarAt_heq_C11S15 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {x : P.Carrier} {y : Q.Carrier} (hxy : HEq x y) :
    metricScalarAt g x = metricScalarAt h y := by
  subst hPQ
  cases hgh
  cases hxy
  rfl

/-- "带 neck chart 的 spatial canonical witness" 沿 stage 相等 + metric / 点的 `HEq` 搬运。 -/
theorem canonicalWitness_heq_C11S15 {P Q : OrientedThreeStage.{u}} {g : P.Metric} {h : Q.Metric}
    (hPQ : P = Q) (hgh : HEq g h) {x : P.Carrier} {y : Q.Carrier} (hxy : HEq x y)
    {ε C1 C2 : ℝ} (hW : ∃ W : SpatialCanonicalWitness h ε C1 C2 y, W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε := by
  subst hPQ
  cases hgh
  cases hxy
  exact hW

/-- **G2a 桥**：P6 (b) 的 history late 形（全部 `A > 0`）⇒ RegularSlice 形
`LargerBallCanonicalLateSupply_C11E`（= `P6LateSupply_P6A`）。 -/
theorem largerBallCanonicalLateSupply_of_history_C11S15 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ}
    (h : LargerBallCanonicalLateSupply_P6A F ε C1 C2) :
    LargerBallCanonicalLateSupply_C11E F ε C1 C2 := by
  intro A hA
  obtain ⟨K₁, T, hK₁, hT, hbody⟩ := h A hA
  refine ⟨K₁, T, hK₁, hT, ?_⟩
  intro s hTs p r hr hsmall hvol y hy hKy
  let H := GC.LongTime.Ch12.sliceTowerHistory_CX2 s
  let cut := GC.LongTime.Ch12.sliceTowerTime_CX2 s
  let t0 : Icc (0 : ℝ) s.history.horizon := ⟨s.time, s.positive.le, le_rfl⟩
  have hsmall' := GC.LongTime.Ch12.smallParabolicCurvature_of_restriction_CX2 H cut t0 p hsmall
  have hvolume := GC.LongTime.Ch12.ballVolume_heq_CX2 (H.restrict_stageAt cut t0)
    (H.restrict_sliceMetric cut t0) (GC.LongTime.Ch12.restrictPoint_heq_CX2 H cut t0 p).symm r
  have hv : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage (GC.LongTime.Ch12.restrictTime_CX2 H cut t0))
        (GC.LongTime.Ch12.restrictTime_CX2 H cut t0))
        (GC.LongTime.Ch12.restrictPoint_CX2 H cut t0 p) r := hvol.trans_eq hvolume
  have hy' := (GC.LongTime.Ch12.metricBall_heq_CX2 (H.restrict_stageAt cut t0)
    (H.restrict_sliceMetric cut t0) (GC.LongTime.Ch12.restrictPoint_heq_CX2 H cut t0 p).symm
    (GC.LongTime.Ch12.restrictPoint_heq_CX2 H cut t0 y).symm (A * r)).mp hy
  have hR := metricScalarAt_heq_C11S15 (H.restrict_stageAt cut t0)
    (H.restrict_sliceMetric cut t0) (GC.LongTime.Ch12.restrictPoint_heq_CX2 H cut t0 y).symm
  have hW := hbody (GC.LongTime.Ch12.sliceTowerIndex_CX2 s)
    (GC.LongTime.Ch12.restrictTime_CX2 H cut t0) (GC.LongTime.Ch12.restrictPoint_CX2 H cut t0 p)
    r hTs hr hsmall' hv (GC.LongTime.Ch12.restrictPoint_CX2 H cut t0 y) hy' (hKy.trans_eq hR)
  exact canonicalWitness_heq_C11S15 (H.restrict_stageAt cut t0) (H.restrict_sliceMetric cut t0)
    (GC.LongTime.Ch12.restrictPoint_heq_CX2 H cut t0 y).symm hW

end GC.LongTime.Ch11
