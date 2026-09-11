import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic



noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem riemannian_curve_edist_le_of_speed_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hC : ∀ t, Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ))) ≤ C) (x y : ℝ) :
    riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist 𝓘(ℝ, E) (γ x) (γ y) ≤ _
  have hnorm (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)‖ₑ ≤ (C : ℝ≥0∞) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    simpa only [ENNReal.ofReal_coe_nnreal] using! ENNReal.ofReal_le_ofReal (hC t)
  have hordered (a b : ℝ) (hab : a ≤ b) :
      Manifold.riemannianEDist 𝓘(ℝ, E) (γ a) (γ b) ≤ (C : ℝ≥0∞) * edist a b := by
    apply (riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl hab).trans
    rw [pathELength_eq_lintegral_mfderiv_Icc]
    calc
      (∫⁻ t in Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)‖ₑ) ≤
          ∫⁻ _t in Icc a b, (C : ℝ≥0∞) := lintegral_mono (fun t => hnorm t)
      _ = (C : ℝ≥0∞) * edist a b := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · rw [riemannianEDist_comm, edist_comm x y]
    exact hordered y x hyx

end DifferentialGeometry.Geometry
