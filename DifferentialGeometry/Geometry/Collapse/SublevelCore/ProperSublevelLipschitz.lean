import DifferentialGeometry.Geometry.Collapse.SublevelCore.ProperSublevel

/-!
# LC32 kernel in the Lipschitz-difference form

The LC32 kernel `isProperMap_of_abs_sub_dist_lt` (`ProperSublevel.lean`) takes `Continuous η`
together with `|η - d_p| < e`. The review of the wave-3 sheets allows, instead of continuity, the
LC30 clause `LipschitzWith ε (η - d_p)`, which implies it. This file gives that form, and the
compactness of the sublevels `{η ≤ t}` as its consumer.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {X : Type*} [MetricSpace X] [ProperSpace X]

/-- LC32 kernel, Lipschitz form: if `η - d_p` is Lipschitz and `|η - d_p| < e`, then `η` is
proper. -/
theorem isProperMap_of_lipschitz_sub_dist {p : X} {η : X → ℝ} {ε : ℝ≥0}
    (hlip : LipschitzWith ε (fun x => η x - dist p x)) {e : ℝ}
    (hclose : ∀ x, |η x - dist p x| < e) : IsProperMap η := by
  have hη : Continuous η :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η x) (dist p x))
  exact isProperMap_of_abs_sub_dist_lt hη hclose

/-- Every sublevel `{η ≤ t}` of such an `η` is compact. -/
theorem isCompact_sublevel_of_lipschitz_sub_dist {p : X} {η : X → ℝ} {ε : ℝ≥0}
    (hlip : LipschitzWith ε (fun x => η x - dist p x)) {e : ℝ}
    (hclose : ∀ x, |η x - dist p x| < e) (t : ℝ) : IsCompact {x | η x ≤ t} := by
  have hset : {x | η x ≤ t} = η ⁻¹' Icc (-e) t := by
    ext x
    have h := abs_lt.mp (hclose x)
    have hd := dist_nonneg (x := p) (y := x)
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
    exact ⟨fun hx => ⟨by linarith, hx⟩, fun hx => hx.2⟩
  rw [hset]
  exact (isProperMap_of_lipschitz_sub_dist hlip hclose).isCompact_preimage isCompact_Icc

end DifferentialGeometry.Geometry.Collapse
