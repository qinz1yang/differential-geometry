import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Path.Speed

set_option autoImplicit false

open Set Bundle Manifold
open scoped ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_of_curve_speed_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hC : ∀ t ∈ Ioo a b, Real.sqrt (g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) ≤ C) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal C * ENNReal.ofReal (b - a) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  apply Manifold.riemannianEDist_le_of_curve_speed_bound hab hγ
  intro t ht
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  exact ENNReal.ofReal_le_ofReal (hC t ht)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem riemannian_curve_edist_le_of_speed_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hC : ∀ t, Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))) ≤ C) (x y : ℝ) :
    riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y := by
  have hordered (a b : ℝ) (hab : a ≤ b) :
      riemannianEDistOf g (γ a) (γ b) ≤ (C : ℝ≥0∞) * edist a b := by
    have h := riemannianEDistOf_le_of_curve_speed_bound g hab hγ.contMDiffOn
      (fun t _ => hC t)
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using h
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · rw [riemannianEDistOf_comm, edist_comm x y]
    exact hordered y x hyx

end DifferentialGeometry.Geometry
