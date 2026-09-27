import DifferentialGeometry.Topology.LoopSpace.HomeomorphismLift
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import Mathlib.Topology.Order.IntermediateValue








noncomputable section

open Function Set

namespace DifferentialGeometry.Topology



theorem real_add_one_le_of_circle_eq {x y : ℝ} (hxy : x < y)
    (heq : (x : loopCircle) = (y : loopCircle)) : x + 1 ≤ y := by
  by_contra h
  have hx : x ∈ Ico x (x + 1) := ⟨le_rfl, by linarith⟩
  have hy : y ∈ Ico x (x + 1) := ⟨hxy.le, lt_of_not_ge h⟩
  exact hxy.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp heq)



theorem increasing_homeomorphism_lift_affinePeriodic
    (ψ : loopCircle ≃ₜ loopCircle) (F : ℝ ≃ₜ ℝ)
    (hF : ∀ t : ℝ, (F t : loopCircle) = ψ (t : loopCircle)) (hm : StrictMono F) :
    ∀ t, F (t + 1) = F t + 1 := by
  have hG (t : ℝ) : (F.symm t : loopCircle) = ψ.symm (t : loopCircle) := by
    apply ψ.injective
    rw [← hF, F.apply_symm_apply, ψ.apply_symm_apply]
  have hGm : StrictMono F.symm := by
    intro x y hxy
    apply hm.lt_iff_lt.mp
    simpa only [F.apply_symm_apply] using hxy
  have hbound (f : ℝ → ℝ) (η : loopCircle → loopCircle)
      (hf : ∀ t : ℝ, (f t : loopCircle) = η (t : loopCircle)) (hfm : StrictMono f) (t : ℝ) :
      f t + 1 ≤ f (t + 1) := by
    apply real_add_one_le_of_circle_eq (hfm (by linarith))
    rw [hf, hf, QuotientAddGroup.mk_add]
    simp only [AddCircle.coe_period, add_zero]
  intro t
  apply le_antisymm ?_ (hbound F ψ hF hm t)
  have h := hbound F.symm ψ.symm hG hGm (F t)
  rw [F.symm_apply_apply] at h
  have hh := hm.monotone h
  simpa only [F.apply_symm_apply] using hh



theorem circleHomeomorph_affineLift_or_neg (ψ : loopCircle ≃ₜ loopCircle) :
    (∃ (F : ℝ ≃ₜ ℝ) (hp : ∀ t, F (t + 1) = F t + 1),
      StrictMono F ∧ ∀ θ, ψ θ = affineCircleMap F F.continuous hp θ) ∨
    (∃ (F : ℝ ≃ₜ ℝ) (hp : ∀ t, F (t + 1) = F t + 1),
      StrictMono F ∧ ∀ θ, ψ θ = -affineCircleMap F F.continuous hp θ) := by
  obtain ⟨F, hF⟩ := exists_real_homeomorphism_lift ψ
  rcases F.continuous.strictMono_of_inj F.injective with hm | hm
  · left
    let hp := increasing_homeomorphism_lift_affinePeriodic ψ F hF hm
    refine ⟨F, hp, hm, ?_⟩
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact (hF t).symm
  · right
    let G := F.trans (Homeomorph.neg ℝ)
    let η := ψ.trans (Homeomorph.neg loopCircle)
    have hG (t : ℝ) : (G t : loopCircle) = η (t : loopCircle) := by
      change ((-F t : ℝ) : loopCircle) = -ψ (t : loopCircle)
      rw [QuotientAddGroup.mk_neg, hF]
    have hGm : StrictMono G := hm.neg
    let hp := increasing_homeomorphism_lift_affinePeriodic η G hG hGm
    refine ⟨G, hp, hGm, ?_⟩
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change ψ (t : loopCircle) = -((-F t : ℝ) : loopCircle)
    rw [QuotientAddGroup.mk_neg, neg_neg, hF]

end DifferentialGeometry.Topology
