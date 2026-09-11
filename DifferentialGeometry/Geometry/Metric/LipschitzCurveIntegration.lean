import DifferentialGeometry.Geometry.Metric.LipschitzCurves
import DifferentialGeometry.Geometry.Metric.NeighborhoodRetraction



noncomputable section

open Bundle Manifold Set MeasureTheory DifferentialGeometry Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in


theorem aestronglyMeasurable_riemannianCurveSpeed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y) :
    AEStronglyMeasurable (riemannianCurveSpeed g γ) volume := by
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨n, e, r, U, he, _, _, hU, heU, hr, hleft⟩ :=
    exists_compact_embedding_and_retraction (E := E) (M := M)
  let B : ℝ → EuclideanSpace ℝ (Fin n) := e ∘ γ
  have hB : Continuous B := he.continuous.comp (continuous_of_riemannian_lipschitz g hγ)
  have hBU (t : ℝ) : B t ∈ U := heU (mem_range_self (γ t))
  let A : ℝ → U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun t => ⟨(B t, deriv B t), hBU t, mem_univ _⟩
  have hA : Measurable A := (hB.measurable.prodMk (measurable_deriv B)).subtype_mk
  let N : U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))) → ℝ := fun p =>
    Real.sqrt (g.inner (r p.val.1)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) r p.val.1 p.val.2)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) r p.val.1 p.val.2))
  have hN : Continuous N :=
    continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_metric_mfderiv_norm g hU (hr.of_le (by simp)))
  have heq : riemannianCurveSpeed g γ =ᵐ[volume] N ∘ A := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ] with t ht
    have hdB : DifferentiableAt ℝ B t :=
      ((he.mdifferentiableAt (by simp)).comp t ht).differentiableAt
    have hdr := ((hr _ (hBU t)).contMDiffAt (hU.mem_nhds (hBU t))).mdifferentiableAt (by simp)
    have hγeq : r ∘ B = γ := by
      funext s
      exact hleft (γ s)
    have h := riemannianCurveSpeed_comp g hdr hdB
    rw [hγeq] at h
    exact h
  exact (hN.measurable.comp hA).aestronglyMeasurable.congr heq.symm


theorem integrableOn_riemannianCurveSpeed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    (s : Set ℝ) [IsFiniteMeasure (volume.restrict s)] :
    IntegrableOn (riemannianCurveSpeed g γ) s := by
  apply Integrable.mono' (integrable_const (C : ℝ))
    (aestronglyMeasurable_riemannianCurveSpeed g hγ).restrict
  exact Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (riemannianCurveSpeed_nonneg g γ t)]
    exact riemannianCurveSpeed_le_of_lipschitz g hγ t)

end DifferentialGeometry.Geometry
