import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Two distinct points have positive scale-relative error bounds and a single comparable positive
marker, yet their perturbed retained blocks coincide. This only refutes an inference from the
listed abstract data; it does not assert failure of the actual geometric adjustments.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Collapse

open Set

def retainedBlockRadius (R : ℝ) (a : Bool) : ℝ := if a then R else 1

def retainedBlockOriginal (R : ℝ) (a : Bool) : ℝ × ℝ :=
  if a then (0, R) else (0, 0)

def retainedBlockPerturbed (R : ℝ) : Bool → ℝ × ℝ := Function.const Bool (0, R)

theorem retained_block_two_point_data {e R : ℝ} (hR : 0 < R) (hRe : R < e) :
    (∀ a, 0 < retainedBlockRadius R a) ∧
    (∀ a, ‖retainedBlockPerturbed R a - retainedBlockOriginal R a‖ ≤
      e * retainedBlockRadius R a) ∧
    (Finset.univ.filter (fun a : Bool => 0 < (retainedBlockOriginal R a).2)).card = 1 ∧
    (∀ a, 0 < (retainedBlockOriginal R a).2 → retainedBlockRadius R a = R) := by
  have he : 0 < e := hR.trans hRe
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    cases a <;> simp [retainedBlockRadius, hR]
  · intro a
    cases a
    · simpa [retainedBlockPerturbed, retainedBlockOriginal, retainedBlockRadius,
        Prod.norm_def, abs_of_pos hR] using And.intro he.le hRe.le
    · simp [retainedBlockPerturbed, retainedBlockOriginal, retainedBlockRadius,
        mul_nonneg he.le hR.le]
  · have hmarkers : Finset.univ.filter
        (fun a : Bool => 0 < (retainedBlockOriginal R a).2) = {true} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      cases a <;> simp [retainedBlockOriginal, hR]
    rw [hmarkers]
    exact Finset.card_singleton true
  · intro a ha
    cases a
    · simp [retainedBlockOriginal] at ha
    · rfl

theorem retained_block_no_cutoff (R : ℝ) :
    ¬ ∃ χ : ℝ × ℝ → ℝ,
      χ (retainedBlockPerturbed R true) = 1 ∧ χ (retainedBlockPerturbed R false) = 0 := by
  rintro ⟨χ, hq, hp⟩
  have heq : retainedBlockPerturbed R true = retainedBlockPerturbed R false := rfl
  rw [← heq, hq] at hp
  norm_num at hp

theorem exists_retained_block_collision {e : ℝ} (he : 0 < e) :
    ∃ R, 0 < R ∧ R < e ∧
      (∀ a, 0 < retainedBlockRadius R a) ∧
      (∀ a, ‖retainedBlockPerturbed R a - retainedBlockOriginal R a‖ ≤
        e * retainedBlockRadius R a) ∧
      (Finset.univ.filter (fun a : Bool => 0 < (retainedBlockOriginal R a).2)).card = 1 ∧
      (∀ a, 0 < (retainedBlockOriginal R a).2 → retainedBlockRadius R a = R) ∧
      ¬ ∃ χ : ℝ × ℝ → ℝ,
        χ (retainedBlockPerturbed R true) = 1 ∧ χ (retainedBlockPerturbed R false) = 0 := by
  let R := e / 2
  have hR : 0 < R := half_pos he
  have hRe : R < e := half_lt_self he
  obtain ⟨hρ, herr, hcount, hscale⟩ := retained_block_two_point_data hR hRe
  exact ⟨R, hR, hRe, hρ, herr, hcount, hscale, retained_block_no_cutoff R⟩

end DifferentialGeometry.Geometry.Collapse
