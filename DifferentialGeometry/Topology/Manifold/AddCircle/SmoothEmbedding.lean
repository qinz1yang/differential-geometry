import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set
open scoped Manifold ContDiff

namespace AddCircle

theorem isSmoothEmbedding_periodic_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {γ : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := by
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift :=
    isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
      QuotientAddGroup.mk_surjective hγ.contMDiff
  have hi : Function.Injective hp.lift := by
    intro a b hab
    apply (equivIco 1 0).injective
    apply Subtype.ext
    apply hinj
    · simpa using (equivIco 1 0 a).property
    · simpa using (equivIco 1 0 b).property
    · change hp.lift ((equivIco 1 0 a : ℝ) : AddCircle (1 : ℝ)) =
        hp.lift ((equivIco 1 0 b : ℝ) : AddCircle (1 : ℝ))
      simpa only [coe_equivIco] using hab
  have himm : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hs
    intro z
    have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift z (parameterTangent z) ≠ 0 := by
      let t : ℝ := equivIco 1 0 z
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        have hi := (equivIco 1 0 z).property
        exact ⟨hi.1, by simpa using hi.2.le⟩
      have hzt : (t : AddCircle (1 : ℝ)) = z := coe_equivIco
      rw [← hzt, ← deriv_comp_coe (hs.mdifferentiable (by simp) (t : AddCircle (1 : ℝ)))]
      exact hne t ht
    intro a b hab
    obtain ⟨α, rfl⟩ := exists_smul_parameterTangent z a
    obtain ⟨β, rfl⟩ := exists_smul_parameterTangent z b
    rw [map_smul, map_smul] at hab
    rw [(smul_left_injective ℝ hv) hab]
  exact ⟨himm, (hs.continuous.isClosedEmbedding hi).isEmbedding⟩

theorem deriv_comp_coe_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle (1 : ℝ) → E}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ f) (t : ℝ) :
    deriv (fun x : ℝ => f (x : AddCircle (1 : ℝ))) t ≠ 0 := by
  rw [deriv_comp_coe (hf.contMDiff.mdifferentiable (by simp) (t : AddCircle (1 : ℝ)))]
  intro heq
  apply parameterTangent_ne_zero (t : AddCircle (1 : ℝ))
  exact (hf.isImmersion.isImmersionAt (t : AddCircle (1 : ℝ))).injective_mfderiv
    (by simp) (heq.trans (map_zero _).symm)

end AddCircle
