import DifferentialGeometry.Analysis.Calculus.Periodic.ImmersionLift
import DifferentialGeometry.Topology.Manifold.Embedding.CompactNeighborhood
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift

section

noncomputable section

open Set Function Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem exists_lipschitzWith_affinePeriodic_parameterLift
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1)
    {K : ℝ≥0} (hc : ∀ s t, riemannianEDistOf g (γ (ψ s : loopCircle))
      (γ (ψ t : loopCircle)) ≤ (K : ℝ≥0∞) * edist s t) :
    ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨N, n, e, hN, he, hecompact, _, hei⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_embedding_on_nhds_of_isCompact
      (I := 𝓘(ℝ, E)) (isCompact_range γ.continuous)
  obtain ⟨Ce, _, hCe⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g
    (he.of_le (by simp)) hecompact
  let Γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => e (γ (t : loopCircle))
  have hΓ : ContDiff ℝ ∞ Γ := (he.comp hγ).contDiff
  have hΓi (t : ℝ) : Injective (fderiv ℝ Γ t) := by
    have hder : fderiv ℝ Γ t =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (γ (t : loopCircle))).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t) := by
      have h := mfderiv_comp t (he.mdifferentiableAt (by simp)) (hγ.mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv] at h
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ)
        (e (γ (t : loopCircle))) (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm v))) h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply] using! hv
    rw [hder]
    exact (hei _ (hN (mem_range_self _))).comp
      (realContinuousLinearMap_injective_of_one_ne_zero _ (him t))
  have hΓψ : LipschitzWith (Ce * K) (Γ ∘ ψ) := by
    intro s t
    apply (hCe (γ (ψ s : loopCircle)) (γ (ψ t : loopCircle))).trans
    simpa only [ENNReal.coe_mul, mul_assoc] using mul_le_mul' (le_refl (Ce : ℝ≥0∞)) (hc s t)
  exact exists_lipschitzWith_affinePeriodic_lift_of_immersion hΓ hΓi hψ hp hΓψ

end DifferentialGeometry.Geometry

end

end
