import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod



namespace DifferentialGeometry.Analysis



theorem deriv_diagonal {F : ℝ × ℝ → ℝ} {t : ℝ} (hF : DifferentiableAt ℝ F (t, t)) :
    deriv (fun s => F (s, s)) t =
      deriv (fun s => F (s, t)) t + deriv (fun s => F (t, s)) t := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, s)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have hl := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (s, t)) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t t))
  have hr := hF.hasFDerivAt.comp_hasDerivAt (f := fun s => (t, s)) t
    ((hasDerivAt_const t t).prodMk (hasDerivAt_id t))
  dsimp only [Function.comp_def] at hd hl hr
  rw [hd.deriv, hl.deriv, hr.deriv, show ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) by ext <;> simp,
    map_add]

end DifferentialGeometry.Analysis

section

open Set Filter

namespace DifferentialGeometry.Analysis

theorem derivWithin_diagonal {F : ℝ × ℝ → ℝ} {T : Set ℝ} {t : ℝ}
    (hT : UniqueDiffWithinAt ℝ T t) (ht : t ∈ T)
    (hF : DifferentiableWithinAt ℝ F (T ×ˢ T) (t, t)) :
    derivWithin (fun s => F (s, s)) T t =
      derivWithin (fun s => F (s, t)) T t + derivWithin (fun s => F (t, s)) T t := by
  have hd := hF.hasFDerivWithinAt.comp_hasDerivWithinAt (f := fun s => (s, s)) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt (s := T))
    (fun s hs => ⟨hs, hs⟩)
  have hl := hF.hasFDerivWithinAt.comp_hasDerivWithinAt (f := fun s => (s, t)) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t t)).hasDerivWithinAt (s := T))
    (fun s hs => ⟨hs, ht⟩)
  have hr := hF.hasFDerivWithinAt.comp_hasDerivWithinAt (f := fun s => (t, s)) t
    (((hasDerivAt_const t t).prodMk (hasDerivAt_id t)).hasDerivWithinAt (s := T))
    (fun s hs => ⟨ht, hs⟩)
  dsimp only [Function.comp_def] at hd hl hr
  rw [hd.derivWithin hT, hl.derivWithin hT, hr.derivWithin hT,
    show ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) by ext <;> simp, map_add]

end DifferentialGeometry.Analysis

end
