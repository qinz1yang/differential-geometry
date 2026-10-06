import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ShrinkingCylinderIsometries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBandEstimatesNK
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Geometry.Curvature.ScalarPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder

/-!
# Route W, c4：`IncomingBackwardNeck` 的圆柱侧 band 估计（S-W-NECK G5，后缀 `_NK`，第 2 部分）

`IncomingBackwardNeck.metric v`（`v ∈ [-1, 0]`，surgery 前 `s = τ₀ + r² v` 的 slice 经 neck chart 拉回、
`(r²)⁻¹` 归一化）由 `parabolic_closeness`（`b = 0`，`a ≤ 2 ≤ k`）与收缩圆柱 `g_cyl(v)` 的
`C²` 距离 `≤ η < δ`（`derivNorm_le_NK`，经
`tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm`）。
`g_cyl(v)` 的 Ricci 算子范数 `≤ 1/2`（`v ≤ 0`；`Ric = g_{S²}`），所以一般的标量扰动定理
`abs_scalar_curvature_sub_le_of_small_metric_derivatives` 给 `|R − (1−v)⁻¹| ≤ 3·(721η)/(1−η)`：
`δ ≤ 1/40000`、`v ∈ [-1/2, 0]` 时 `R ≥ 2/3 − 0.06 ≥ 3/5`（`band_cyl_NK`，比 `1/2` 有余量）；
`(dz)² ≤ g_cyl(v)(w,w) ≤ g/(1-η) ≤ 2g`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r : ℝ}

/-- 圆柱侧：`v ∈ [-1, 0]` 的 backward metric 与收缩圆柱 `g_cyl(v)` 的 `C^m`（`m ≤ 2`）距离 `≤ η < δ`。 -/
theorem IncomingBackwardNeck.derivNorm_le_NK (B : IncomingBackwardNeck H i neck r)
    (hk : 2 ≤ k) :
    ∃ η : ℝ, η < δ ∧ ∀ v : ℝ, v ∈ Icc (-1 : ℝ) 0 → ∀ x ∈ neckClosedTest δ, ∀ m : ℕ, m ≤ 2 →
      metricDerivNorm m (B.metric v)
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
          (neckBuffer δ))
        ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
          (neckBuffer δ)) x ≤ η := by
  obtain ⟨η, hη, hbound⟩ := B.parabolic_closeness
  refine ⟨η, hη, fun v hv x hx m hm => ?_⟩
  have h := hbound m 0 (by omega) ⟨v, hv⟩ x hx
  have hv1 : v < 1 := hv.2.trans_lt zero_lt_one
  have hgc : shrinkingCylinderMetric ⟨v, hv1⟩ =
      PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v :=
    shrinkingCylinderMetric_eq_flow ⟨v, hv1⟩
  have hD : B.timeDifferenceJet 0 ⟨v, hv⟩ = metricTensorField (B.metric v) -
      metricTensorField ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
        (neckBuffer δ)) := by
    ext y w
    rw [B.timeDifferenceJet_eq]
    simp only [iteratedDerivWithin_zero, min_eq_left hv.2, hgc]
    rfl
  simp only at h
  rw [cylinderTensorCovDeriv_eq_tensor02CovDeriv, hD] at h
  rw [hgc] at h
  have h2 := tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm (B.metric v)
    ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer δ))
    ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer δ))
    m x
  rw [← h2]
  exact h

theorem real_aux_NK (a b W U p : ℝ) (hb : 0 ≤ b) (hW : 2 * a ≤ W) (hU : 2 * b ≤ U)
    (hcs : p ^ 2 ≤ a * b) (hp : U = p) (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) : U ≤ W / 4 := by
  subst hp
  have h1 : (2 * a) * (2 * b) ≤ W * U := mul_le_mul hW hU (by positivity) hW0
  have h4 : 4 * U ^ 2 ≤ W * U := by nlinarith
  rcases hU0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

/-- 收缩圆柱（限制到 `neckBuffer δ`）的 Ricci 算子范数 `≤ 1/2`（`v ≤ 0`）。 -/
theorem ricciSharp_shrinkingCylinder_norm_le_NK {δ v : ℝ} (hv : v ≤ 0) (x : neckBuffer δ)
    (w : TangentSpace NeckCylinderModel x) :
    let gRef := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
      (neckBuffer δ)
    Real.sqrt (gRef.inner x (ricciSharp gRef x w) (ricciSharp gRef x w)) ≤
      (1 / 2 : ℝ) * Real.sqrt (gRef.inner x w w) := by
  intro gRef
  have hv1 : v < 1 := hv.trans_lt zero_lt_one
  set u := ricciSharp gRef x w with hu
  have hUdef : gRef.inner x u u =
      (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 w.1 u.1 := by
    rw [hu, inner_ricciSharp]
    have h1 := Curvature.ricciTensor_restrictOpen
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) (neckBuffer δ) x w
      (ricciSharp gRef x w)
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at h1
    exact h1.trans (PDE.RicciFlow.ricciTensor_shrinkingCylinderMetric v x.1 w _)
  have hinner : ∀ y : TangentSpace NeckCylinderModel x, gRef.inner x y y =
      2 * (1 - v) * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 y.1 y.1 +
        y.2 * y.2 := fun y => PDE.RicciFlow.shrinkingCylinderMetric_inner hv1 x.1 y y
  have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq
    (Geometry.roundMetric (E := ThreeSpace) (n := 2)) x.1.1 w.1 u.1
  have ha := metric_inner_self_nonneg (Geometry.roundMetric (E := ThreeSpace) (n := 2))
    x.1.1 w.1
  have hb := metric_inner_self_nonneg (Geometry.roundMetric (E := ThreeSpace) (n := 2))
    x.1.1 u.1
  have hW0 : 0 ≤ gRef.inner x w w := metric_inner_self_nonneg gRef x w
  have hU0 : 0 ≤ gRef.inner x u u := metric_inner_self_nonneg gRef x u
  have hW : 2 * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 w.1 w.1 ≤
      gRef.inner x w w := by
    rw [hinner]; nlinarith [mul_self_nonneg w.2]
  have hU : 2 * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 u.1 u.1 ≤
      gRef.inner x u u := by
    rw [hinner]; nlinarith [mul_self_nonneg u.2]
  have hle := real_aux_NK _ _ _ _ _ hb hW hU hcs hUdef hU0 hW0
  rw [Real.sqrt_le_left (by positivity)]
  rw [mul_pow, Real.sq_sqrt hW0]
  linarith

/-- 圆柱侧的 band 估计（带余量）：`v ∈ [-1/2, 0]` 的 backward metric 在 `|z| ≤ δ⁻¹` 上
`R ≥ 3/5`、`(dz w)² ≤ 2 g(w,w)`。 -/
theorem IncomingBackwardNeck.band_cyl_NK (B : IncomingBackwardNeck H i neck r) (hk : 2 ≤ k)
    (hδ : δ ≤ 1 / 40000) :
    ∀ v : ℝ, v ∈ Icc (-1 / 2 : ℝ) 0 → ∀ x : neckBuffer δ, x ∈ neckClosedTest δ →
      3 / 5 ≤ metricScalarAt (B.metric v) x ∧
      ∀ w : TangentSpace NeckCylinderModel x,
        (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x w) ^ 2 ≤
          2 * (B.metric v).inner x w w := by
  obtain ⟨η, hη, hbound⟩ := B.derivNorm_le_NK hk
  intro v hv x hx
  have hv' : v ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [hv.1], hv.2⟩
  have hv1 : v < 1 := hv.2.trans_lt zero_lt_one
  set gRef := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen
    (neckBuffer δ) with hgRef
  have hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m (B.metric v) gRef gRef x ≤ η :=
    fun m hm => hbound v hv' x hx m hm
  have hη0 : 0 ≤ η := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hηs : η ≤ 1 / 40000 := by linarith
  refine ⟨?_, fun w => ?_⟩
  · have h := abs_scalar_curvature_sub_le_of_small_metric_derivatives (B.metric v) gRef x η
      (by linarith) hsmall (1 / 2)
      (fun w => ricciSharp_shrinkingCylinder_norm_le_NK hv.2 x w)
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
    rw [hdim] at h
    have hR : metricScalarAt gRef x = (1 - v)⁻¹ := by
      rw [hgRef, metricScalarAt_restrictOpen]
      exact PDE.RicciFlow.shrinkingCylinderMetric_scalar hv1 x.1
    rw [hR] at h
    have h23 : (2 : ℝ) / 3 ≤ (1 - v)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by linarith)]
      norm_num
      linarith [hv.1]
    have hfrac : (3 : ℝ) * ((240 * 3 * η + η * (1 / 2)) / (1 - η)) ≤ 3 / 50 := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith
    have := (abs_le.mp h).1
    push_cast at this
    linarith
  · have h0 := hsmall 0 (by norm_num)
    have hcmp := (Geometry.Metric.sqrt_inner_comparison_of_metric_difference (B.metric v) gRef x
      η (by linarith) h0 w).1
    have hA : 0 ≤ gRef.inner x w w := metric_inner_self_nonneg _ _ _
    have hB' : 0 ≤ (B.metric v).inner x w w := metric_inner_self_nonneg _ _ _
    have hsq := pow_le_pow_left₀ (by positivity) hcmp 2
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hA, Real.sq_sqrt hB'] at hsq
    have hinner : gRef.inner x w w =
        2 * (1 - v) * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.1.1 w.1 w.1 +
          w.2 * w.2 := PDE.RicciFlow.shrinkingCylinderMetric_inner hv1 x.1 w w
    have hround := metric_inner_self_nonneg (Geometry.roundMetric (E := ThreeSpace) (n := 2))
      x.1.1 w.1
    have hlow : w.2 ^ 2 ≤ gRef.inner x w w := by
      rw [hinner]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 - v)) hround]
    rw [mfderiv_height_apply_NK]
    nlinarith [sq_nonneg w.2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
