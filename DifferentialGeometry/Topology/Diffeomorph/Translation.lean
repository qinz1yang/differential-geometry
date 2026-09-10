import DifferentialGeometry.Topology.Diffeomorph.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped ContDiff Manifold NNReal

namespace Diffeomorph

theorem exists_isotopy_translation_of_isBounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : Bornology.IsBounded K) (v : E) :
    ∃ H : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t : ℝ, ∀ x ∈ K, H t x = x + Real.smoothTransition t • v) ∧
      ∃ J : Set E, IsCompact J ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Jᶜ ∧ Set.EqOn (H t).symm id Jᶜ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let b : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    b.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  obtain ⟨R₀, hR₀, hKR₀⟩ := hK.exists_pos_norm_le
  let R : ℝ := R₀ + ‖v‖ * B + 1
  have hprod : 0 ≤ ‖v‖ * (B : ℝ) := mul_nonneg (norm_nonneg _) B.coe_nonneg
  have hR : 0 < R := by dsimp only [R]; linarith
  have hR₀R : R₀ ≤ R := by dsimp only [R]; linarith
  have hsmall : ‖v‖ * (B : ℝ) < R := by dsimp only [R]; linarith
  let f : E → E := fun x => b (R⁻¹ • x) • v
  have hf : ContDiff ℝ ∞ f :=
    (b.contDiff.comp (contDiff_const.smul contDiff_id)).smul contDiff_const
  let C : ℝ≥0 := ‖v‖₊ * (B * ‖R⁻¹‖₊)
  have hC : C < 1 := by
    rw [← NNReal.coe_lt_coe]
    change ‖v‖ * ((B : ℝ) * ‖R⁻¹‖) < 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← mul_assoc]
    exact (mul_inv_lt_iff₀ hR).2 (by simpa only [one_mul] using hsmall)
  have hlip : LipschitzWith C f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (b (R⁻¹ • x) • v) (b (R⁻¹ • y) • v) ≤ (C : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_smul, norm_smul]
    have hbxy := hB.norm_sub_le (R⁻¹ • x) (R⁻¹ • y)
    rw [← smul_sub, norm_smul] at hbxy
    calc
      ‖b (R⁻¹ • x) - b (R⁻¹ • y)‖ * ‖v‖ ≤
          ((B : ℝ) * (‖R⁻¹‖ * ‖x - y‖)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hbxy (norm_nonneg _)
      _ = (C : ℝ) * dist x y := by simp only [C, NNReal.coe_mul, coe_nnnorm, dist_eq_norm]; ring
  have hs : HasCompactSupport f :=
    (b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')).smul_right
  have heq : ∀ x ∈ K, f x = v := by
    intro x hx
    have hxball : R⁻¹ • x ∈ Metric.closedBall (0 : E) b.rIn := by
      change dist (R⁻¹ • x) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      calc
        R⁻¹ * ‖x‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left ((hKR₀ x hx).trans hR₀R) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    dsimp only [f]
    rw [b.one_of_mem_closedBall hxball, one_smul]
  refine ⟨addLipschitzIsotopy hf hlip hC, contDiff_addLipschitzIsotopy hf hlip hC,
    contDiff_addLipschitzIsotopy_symm hf hlip hC, addLipschitzIsotopy_zero hf hlip hC,
    ?_, exists_isCompact_eqOn_addLipschitzIsotopy hf hlip hC hs⟩
  intro t x hx
  rw [addLipschitzIsotopy_apply, heq x hx]

end Diffeomorph
