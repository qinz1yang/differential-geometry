import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.Metric.LipschitzCurves
import Mathlib.Analysis.Calculus.FDeriv.Measurable

section

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem norm_deriv_comp_le_mul_riemannianCurveSpeed
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {P : M → F} {C : ℝ≥0}
    (hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 P)
    (hC : ∀ p (v : TangentSpace 𝓘(ℝ, E) p),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) P p v : F)‖ ≤ C * Real.sqrt (g.inner p v v))
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    ‖deriv (P ∘ γ) t‖ ≤ C * riemannianCurveSpeed g γ t := by
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, F)) t (hP.mdifferentiableAt one_ne_zero) hγ (1 : ℝ)
  have hcoord : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (P ∘ γ) t (1 : ℝ) = deriv (P ∘ γ) t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := P ∘ γ) (x := t)
  have hder := hcoord.symm.trans hchain
  rw [hder]
  exact hC (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)

variable [FiniteDimensional ℝ E] [T3Space M] [CompleteSpace F]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_curve_energy_bound_of_contMDiff_of_hasCompactSupport
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {P : M → F}
    (hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 P) (hPc : HasCompactSupport P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (γ : ℝ → M) (K : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (K : ℝ≥0∞) * edist s t) →
      LipschitzWith (C * K) (P ∘ γ) ∧
      (∀ᵐ t ∂volume, ‖deriv (P ∘ γ) t‖ ^ 2 ≤ (C : ℝ) ^ 2 * (riemannianCurveSpeed g γ t) ^ 2) ∧
      ∀ S : Set ℝ, IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) S →
        IntegrableOn (fun t => ‖deriv (P ∘ γ) t‖ ^ 2) S ∧
        (∫ t in S, ‖deriv (P ∘ γ) t‖ ^ 2) ≤
          (C : ℝ) ^ 2 * ∫ t in S, (riemannianCurveSpeed g γ t) ^ 2 := by
  obtain ⟨B, hB⟩ := exists_metric_mfderiv_bound_of_hasCompactSupport g hP hPc
  let C : ℝ≥0 := B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hbound : ∀ p (v : TangentSpace 𝓘(ℝ, E) p),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) P p v : F)‖ ≤ C * Real.sqrt (g.inner p v v) := by
    intro p v
    exact (hB p v).trans (mul_le_mul_of_nonneg_right (by simp [C]) (Real.sqrt_nonneg _))
  have hdist := edist_map_le_of_metric_mfderiv_bound g hC hP hbound
  refine ⟨C, hC, ?_⟩
  intro γ K hγ
  have hLip : LipschitzWith (C * K) (P ∘ γ) := by
    intro s t
    exact (hdist (γ s) (γ t)).trans
      ((mul_le_mul_right (hγ s t) (C : ℝ≥0∞)).trans_eq (by rw [ENNReal.coe_mul, mul_assoc]))
  have hae : ∀ᵐ t ∂volume,
      ‖deriv (P ∘ γ) t‖ ^ 2 ≤ (C : ℝ) ^ 2 * (riemannianCurveSpeed g γ t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ] with t ht
    have h := norm_deriv_comp_le_mul_riemannianCurveSpeed g hP hbound ht
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  refine ⟨hLip, hae, ?_⟩
  intro S hi
  have hmeas : AEStronglyMeasurable (fun t => ‖deriv (P ∘ γ) t‖ ^ 2) (volume.restrict S) :=
    (aestronglyMeasurable_deriv (P ∘ γ) (volume.restrict S)).norm.pow 2
  have hri : IntegrableOn (fun t => (C : ℝ) ^ 2 * (riemannianCurveSpeed g γ t) ^ 2) S :=
    hi.const_mul ((C : ℝ) ^ 2)
  have hPi : IntegrableOn (fun t => ‖deriv (P ∘ γ) t‖ ^ 2) S := by
    apply hri.mono' hmeas
    filter_upwards [ae_restrict_of_ae (s := S) hae] with t ht
    simpa only [norm_pow, norm_norm] using ht
  refine ⟨hPi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hPi hri (ae_restrict_of_ae hae)

end DifferentialGeometry.Geometry

end

end
