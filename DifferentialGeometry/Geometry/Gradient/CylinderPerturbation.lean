import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.RestrictedCylinderAxis
import DifferentialGeometry.Geometry.Metric.SharpPerturbation
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Metric.LengthPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Gradient

theorem gradFun_height_close_to_axis
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    (gRef : SmoothRiemannianMetric I M)
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ)) (x : M × ℝ)
    (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hsmall : metricDerivNorm 0 g (cylinderMetric gRef) (cylinderMetric gRef) x ≤ δ) :
    let d := gradFun g Prod.snd x - cylinderAxis x
    Real.sqrt ((cylinderMetric gRef).inner x d d) ≤ 2 * δ := by
  have h := metricSharp_difference_bound g (cylinderMetric gRef) x
    (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd x).toLinearMap δ (by linarith) hsmall
  change Real.sqrt ((cylinderMetric gRef).inner x
    (gradFun g Prod.snd x - gradFun (cylinderMetric gRef) Prod.snd x)
    (gradFun g Prod.snd x - gradFun (cylinderMetric gRef) Prod.snd x)) ≤
      δ / (1 - δ) * Real.sqrt ((cylinderMetric gRef).inner x
        (gradFun (cylinderMetric gRef) Prod.snd x) (gradFun (cylinderMetric gRef) Prod.snd x)) at h
  rw [gradFun_height_eq_cylinderAxis, cylinderMetric_axis_unit, Real.sqrt_one, mul_one] at h
  apply h.trans
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hsmall
  rw [div_le_iff₀ (by linarith : 0 < 1 - δ)]
  nlinarith

theorem gradFun_restricted_height_close_to_axis
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (gRef : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens (M × ℝ))
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) O) (x : O)
    (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hsmall : metricDerivNorm 0 g ((cylinderMetric gRef).restrictOpen O)
      ((cylinderMetric gRef).restrictOpen O) x ≤ δ) :
    let d := gradFun g (fun y : O ↦ (y : M × ℝ).2) x - restrictedCylinderAxis O x
    Real.sqrt (((cylinderMetric gRef).restrictOpen O).inner x d d) ≤ 2 * δ := by
  let f : O → ℝ := fun y ↦ (y : M × ℝ).2
  let g₀ := (cylinderMetric gRef).restrictOpen O
  have h := metricSharp_difference_bound g g₀ x
    (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) f x).toLinearMap δ (by linarith) hsmall
  change Real.sqrt (g₀.inner x (gradFun g f x - gradFun g₀ f x)
      (gradFun g f x - gradFun g₀ f x)) ≤
    δ / (1 - δ) * Real.sqrt (g₀.inner x (gradFun g₀ f x) (gradFun g₀ f x)) at h
  have haxis : gradFun g₀ f x = restrictedCylinderAxis O x :=
    gradFun_restricted_height_eq_restrictedCylinderAxis gRef O x
  rw [haxis, restrictedCylinderAxis_unit, Real.sqrt_one, mul_one] at h
  apply h.trans
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hsmall
  rw [div_le_iff₀ (by linarith : 0 < 1 - δ)]
  nlinarith

theorem sqrt_inner_sub_gradFun_restricted_height_le
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (gRef : SmoothRiemannianMetric I M) (O : TopologicalSpace.Opens (M × ℝ))
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) O) (x : O)
    (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : metricDerivNorm 0 g ((cylinderMetric gRef).restrictOpen O)
      ((cylinderMetric gRef).restrictOpen O) x ≤ ε)
    (w : TangentSpace (I.prod 𝓘(ℝ)) x) (r : ℝ)
    (hw : Real.sqrt (((cylinderMetric gRef).restrictOpen O).inner x
      (w - restrictedCylinderAxis O x) (w - restrictedCylinderAxis O x)) ≤ r) :
    let d := w - gradFun g (fun y : O ↦ (y : M × ℝ).2) x
    Real.sqrt (g.inner x d d) ≤ Real.sqrt (1 + ε) * (r + 2 * ε) := by
  let g₀ := (cylinderMetric gRef).restrictOpen O
  let a := gradFun g (fun y : O ↦ (y : M × ℝ).2) x
  let v := restrictedCylinderAxis (I := I) O x
  have ha : Real.sqrt (g₀.inner x (a - v) (a - v)) ≤ 2 * ε :=
    gradFun_restricted_height_close_to_axis gRef O g x ε hε hsmall
  have hneg : Real.sqrt (g₀.inner x (v - a) (v - a)) =
      Real.sqrt (g₀.inner x (a - v) (a - v)) := by
    rw [show v - a = -(a - v) by abel]
    simp only [map_neg, neg_apply, neg_neg]
  have hmodel : Real.sqrt (g₀.inner x (w - a) (w - a)) ≤ r + 2 * ε := by
    have ht := DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le g₀ x (w - v) (v - a)
    rw [sub_add_sub_cancel, hneg] at ht
    exact ht.trans (add_le_add hw ha)
  exact (sqrt_inner_comparison_of_metric_difference g g₀ x ε (by linarith) hsmall (w - a)).2.trans
    (mul_le_mul_of_nonneg_left hmodel (Real.sqrt_nonneg _))

end DifferentialGeometry.Geometry.Gradient
