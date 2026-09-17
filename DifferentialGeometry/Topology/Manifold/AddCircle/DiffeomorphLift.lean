import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Analysis.Calculus.Deriv.Slope

open scoped ContDiff Manifold
namespace AddCircle

theorem exists_real_diffeomorphism_lift
    (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞) :
    ∃ F : ℝ ≃ₘ[ℝ] ℝ, ∀ t : ℝ, (F t : AddCircle (1 : ℝ)) = ψ (t : AddCircle (1 : ℝ)) := by
  obtain ⟨F, hF⟩ := DifferentialGeometry.Topology.exists_real_homeomorphism_lift ψ.toHomeomorph
  change ∀ t : ℝ, (F t : AddCircle (1 : ℝ)) = ψ (t : AddCircle (1 : ℝ)) at hF
  have hi (t : ℝ) : (F.symm t : AddCircle (1 : ℝ)) = ψ.symm (t : AddCircle (1 : ℝ)) := by
    apply ψ.injective
    change ψ (F.symm t : AddCircle (1 : ℝ)) = ψ (ψ.symm (t : AddCircle (1 : ℝ)))
    rw [← hF, F.apply_symm_apply, ψ.apply_symm_apply]
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ F :=
    isLocalDiffeomorph_coe.contMDiff_of_continuous_of_comp F.continuous
      ((ψ.contMDiff.comp contMDiff_coe).congr hF) le_rfl
  have hsi : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ F.symm :=
    isLocalDiffeomorph_coe.contMDiff_of_continuous_of_comp F.symm.continuous
      ((ψ.symm.contMDiff.comp contMDiff_coe).congr hi) le_rfl
  exact ⟨{ toEquiv := F.toEquiv, contMDiff_toFun := hs, contMDiff_invFun := hsi }, hF⟩

theorem exists_increasing_diffeomorphism_lift_or_neg
    (ψ : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞) :
    ∃ F : ℝ ≃ₘ[ℝ] ℝ, (∀ t : ℝ, F (t + 1) = F t + 1) ∧
      (∀ t : ℝ, 0 < deriv F t) ∧
      ((∀ t : ℝ, ψ (t : AddCircle (1 : ℝ)) = (F t : AddCircle (1 : ℝ))) ∨
        (∀ t : ℝ, ψ (t : AddCircle (1 : ℝ)) = -(F t : AddCircle (1 : ℝ)))) := by
  have hne (G : ℝ ≃ₘ[ℝ] ℝ) (x : ℝ) : deriv G x ≠ 0 := by
    have hd := (G.symm.contMDiff.contDiff.differentiable (by simp) (G x)).hasDerivAt.comp x
      (G.contMDiff.contDiff.differentiable (by simp) x).hasDerivAt
    have heq : G.symm ∘ G = (id : ℝ → ℝ) := funext G.symm_apply_apply
    rw [heq] at hd
    have h := hd.unique (hasDerivAt_id x)
    intro hzero
    rw [hzero, mul_zero] at h
    exact zero_ne_one h
  obtain ⟨F, hF⟩ := exists_real_diffeomorphism_lift ψ
  rcases F.toHomeomorph.continuous.strictMono_of_inj F.injective with hm | hm
  · have hp := DifferentialGeometry.Topology.increasing_homeomorphism_lift_affinePeriodic
      ψ.toHomeomorph F.toHomeomorph hF hm
    refine ⟨F, hp, fun t => lt_of_le_of_ne hm.monotone.deriv_nonneg
      (Ne.symm (hne F t)), Or.inl (fun t => (hF t).symm)⟩
  · let N : ℝ ≃ₘ[ℝ] ℝ :=
      { toEquiv := Equiv.neg ℝ
        contMDiff_toFun := contDiff_id.neg.contMDiff
        contMDiff_invFun := contDiff_id.neg.contMDiff }
    let G := F.trans N
    have hG (t : ℝ) : (G t : AddCircle (1 : ℝ)) =
        (ψ.toHomeomorph.trans (Homeomorph.neg (AddCircle (1 : ℝ)))) (t : AddCircle (1 : ℝ)) := by
      change ((-F t : ℝ) : AddCircle (1 : ℝ)) = -ψ (t : AddCircle (1 : ℝ))
      rw [QuotientAddGroup.mk_neg, hF]
    have hGm : StrictMono G := hm.neg
    have hp := DifferentialGeometry.Topology.increasing_homeomorphism_lift_affinePeriodic
      (ψ.toHomeomorph.trans (Homeomorph.neg (AddCircle (1 : ℝ)))) G.toHomeomorph hG hGm
    refine ⟨G, hp, fun t => lt_of_le_of_ne hGm.monotone.deriv_nonneg
      (Ne.symm (hne G t)), Or.inr ?_⟩
    intro t
    change ψ (t : AddCircle (1 : ℝ)) = -((-F t : ℝ) : AddCircle (1 : ℝ))
    rw [QuotientAddGroup.mk_neg, neg_neg, hF]

end AddCircle
