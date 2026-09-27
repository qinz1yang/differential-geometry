import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

def fiberwiseAffine (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) :
    Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (M × ℝ) (M × ℝ) n where
  toFun p := (p.1, shift p.1 + scale p.1 * p.2)
  invFun p := (p.1, (p.2 - shift p.1) / scale p.1)
  left_inv p := by
    refine Prod.ext (by rfl) ?_
    change (shift p.1 + scale p.1 * p.2 - shift p.1) / scale p.1 = p.2
    field_simp [hne p.1]
    ring
  right_inv p := by
    refine Prod.ext (by rfl) ?_
    change shift p.1 + scale p.1 * ((p.2 - shift p.1) / scale p.1) = p.2
    field_simp [hne p.1]
    ring
  contMDiff_toFun := contMDiff_fst.prodMk
    ((hshift.comp contMDiff_fst).add ((hscale.comp contMDiff_fst).mul contMDiff_snd))
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contMDiff_snd.sub (hshift.comp contMDiff_fst)).div₀
      (hscale.comp contMDiff_fst) (fun p => hne p.1))

@[simp] theorem fiberwiseAffine_apply (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) (p : M × ℝ) :
    fiberwiseAffine shift scale hshift hscale hne p =
      (p.1, shift p.1 + scale p.1 * p.2) := rfl

@[simp] theorem fiberwiseAffine_symm_apply (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) (p : M × ℝ) :
    (fiberwiseAffine shift scale hshift hscale hne).symm p =
      (p.1, (p.2 - shift p.1) / scale p.1) := rfl

end Diffeomorph

end
