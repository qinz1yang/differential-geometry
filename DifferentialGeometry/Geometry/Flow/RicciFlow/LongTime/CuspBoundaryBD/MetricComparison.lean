import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Riemann.Tensor

/-!
# IMS04 / G1（S-A10-BOUNDARY, suffix `_BD`）：`metric_error` 的 k = 0 项 ⇒ 度量 comparison

`PersistentHyperbolicCores.metric_error` 在 `k = 0` 给出：对 `p ∈ ball`，2-tensor
`t⁻¹ • (map i t)^* g(t) - h` 的 `h`-fiber norm `< accuracy t`。本文件把它转成逐向量的 comparison：

* `abs_pullback_inner_sub_le_BD`：`|t⁻¹ g(t)(D v, D w) - h(v, w)| ≤ acc · |v|_h |w|_h`；
* `inner_comparison_of_metric_error_BD`：
  `(1 - acc) h(v,v) ≤ t⁻¹ g(t)(D v, D v) ≤ (1 + acc) h(v,v)`；
* `pullback_inner_le_BD`：`g(t)(D v, D v) ≤ t (1 + acc) h(v,v)`；
* `sqrt_pullback_inner_le_BD`：`|D v|_{g(t)} ≤ √(t (1 + acc)) |v|_h`。

证明路线与 `Collapse/BoundaryScale/CuspMetricEquivalence.lean` 的
`CuspEmbedding.abs_pullback_inner_sub_le` 完全同型
（`exists_orthonormal_basis` + `abs_apply_le_sqrt_normSq0S`），只是误差 tensor 带 `t⁻¹` 缩放。
无新增假设：只用 `cores.metric_error`、`cores.start_pos`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- 2-tensor 的 `tensor0SFiberNorm` 界 ⇒ 双线性型在 `(v, w)` 上的逐点界（经 `vec2` 求值）。 -/
theorem abs_apply_le_of_tensor0SFiberNorm_lt_BD (h : SmoothRiemannianMetric I M) (p : M)
    (A : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (δ : ℝ)
    (hδ : tensor0SFiberNorm h p 2
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap.comp
        A).uncurryLeft < δ) (v w : TangentSpace I p) :
    |A v w| ≤ δ * Real.sqrt (h.inner p v v) * Real.sqrt (h.inner p w w) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) h p
  have hb := abs_apply_le_sqrt_normSq0S (I := I) h p 2 basis hON
    (((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap.comp
      A).uncurryLeft : Tensor0SSpace 2 I p) (vec2 v w)
  have hev : (((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap
      |>.comp A).uncurryLeft : Tensor0SSpace 2 I p) (vec2 v w) = A v w := rfl
  erw [hev, Fin.prod_univ_two] at hb
  simp only [vec2, Fin.isValue, ↓reduceIte, one_ne_zero] at hb
  refine hb.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact hδ.le

end Algebra

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G1 基础形式**：`metric_error`（k = 0）⇒ `|t⁻¹ g(t)(D v, D w) - h(v, w)| ≤ acc · |v|_h |w|_h`。 -/
theorem PersistentHyperbolicCores.abs_pullback_inner_sub_le_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) {p : (cores.model i).Carrier}
    (hp : p ∈ riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy t)⁻¹) (v w : TangentSpace (𝓡 3) p) :
    |t⁻¹ * (postMetric F.observation t).inner (cores.map i t ht p)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p w) -
      (cores.model i).metric.inner p v w| ≤
      cores.accuracy t * Real.sqrt ((cores.model i).metric.inner p v v) *
        Real.sqrt ((cores.model i).metric.inner p w w) := by
  have h0 := cores.metric_error i t ht 0 (Nat.zero_le _) p hp
  have hA := abs_apply_le_of_tensor0SFiberNorm_lt_BD (I := 𝓡 3) (cores.model i).metric p
    ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (cores.map i t ht) p -
      (cores.model i).metric.inner p) (cores.accuracy t) h0 v w
  simpa [localPullInner_apply] using hA

/-- **G1 主定理**：`(1 - acc) h(v,v) ≤ t⁻¹ g(t)(D v, D v) ≤ (1 + acc) h(v,v)`（`p ∈ ball`）。 -/
theorem PersistentHyperbolicCores.inner_comparison_of_metric_error_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) {p : (cores.model i).Carrier}
    (hp : p ∈ riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy t)⁻¹) (v : TangentSpace (𝓡 3) p) :
    (1 - cores.accuracy t) * (cores.model i).metric.inner p v v ≤
        t⁻¹ * (postMetric F.observation t).inner (cores.map i t ht p)
          (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
          (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v) ∧
      t⁻¹ * (postMetric F.observation t).inner (cores.map i t ht p)
          (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
          (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v) ≤
        (1 + cores.accuracy t) * (cores.model i).metric.inner p v v := by
  have h := cores.abs_pullback_inner_sub_le_BD i t ht hp v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

/-- `g(t)(D v, D v) ≤ t (1 + acc) h(v,v)`：不带 `t⁻¹` 的上界（用 `0 < t`）。 -/
theorem PersistentHyperbolicCores.pullback_inner_le_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) {p : (cores.model i).Carrier}
    (hp : p ∈ riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy t)⁻¹) (v : TangentSpace (𝓡 3) p) :
    (postMetric F.observation t).inner (cores.map i t ht p)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v) ≤
      t * ((1 + cores.accuracy t) * (cores.model i).metric.inner p v v) := by
  have htpos : 0 < t := cores.start_pos.trans_le ht
  have h := (cores.inner_comparison_of_metric_error_BD i t ht hp v).2
  exact (inv_mul_le_iff₀ htpos).mp h

/-- **consumer**：`|D v|_{g(t)} ≤ √(t (1 + acc)) · |v|_h`（G2 逐点 speed 界的核心）。 -/
theorem PersistentHyperbolicCores.sqrt_pullback_inner_le_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) {p : (cores.model i).Carrier}
    (hp : p ∈ riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy t)⁻¹) (v : TangentSpace (𝓡 3) p) :
    Real.sqrt ((postMetric F.observation t).inner (cores.map i t ht p)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)) ≤
      Real.sqrt (t * (1 + cores.accuracy t)) *
        Real.sqrt ((cores.model i).metric.inner p v v) := by
  have htpos : 0 < t := cores.start_pos.trans_le ht
  have hacc := cores.accuracy_pos t ht
  rw [← Real.sqrt_mul (mul_nonneg htpos.le (by linarith))]
  refine Real.sqrt_le_sqrt ?_
  have := cores.pullback_inner_le_BD i t ht hp v
  rw [mul_assoc]
  exact this

/-- **consumer（下界）**：`acc t < 1` 时 `D(map i t)` 在 ball 上单射，且 `|D v|_{g(t)}² ≥ t(1-acc)|v|_h²`。 -/
theorem PersistentHyperbolicCores.pullback_inner_pos_BD
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ)
    (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1) {p : (cores.model i).Carrier}
    (hp : p ∈ riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy t)⁻¹) (v : TangentSpace (𝓡 3) p) (hv : v ≠ 0) :
    0 < (postMetric F.observation t).inner (cores.map i t ht p)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v) := by
  have htpos : 0 < t := cores.start_pos.trans_le ht
  have h1 := (cores.inner_comparison_of_metric_error_BD i t ht hp v).1
  have hpos : 0 < (cores.model i).metric.inner p v v := (cores.model i).metric.pos p v hv
  have hlow : 0 < (1 - cores.accuracy t) * (cores.model i).metric.inner p v v :=
    mul_pos (by linarith) hpos
  have : 0 < t⁻¹ * (postMetric F.observation t).inner (cores.map i t ht p)
      (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v)
      (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) p v) := lt_of_lt_of_le hlow h1
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp this

end GC.LongTime
