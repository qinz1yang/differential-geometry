import DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold

namespace Diffeomorph

noncomputable def smoothMax (ε : ℝ) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 - p.2, Real.smoothMax ε p.1 p.2)
  invFun p := (p.2 + (p.1 - Real.smoothAbs ε p.1) / 2,
    p.2 - (p.1 + Real.smoothAbs ε p.1) / 2)
  left_inv p := by
    apply Prod.ext <;> dsimp [Real.smoothMax] <;> ring
  right_inv p := by
    have h : p.2 + (p.1 - Real.smoothAbs ε p.1) / 2 -
        (p.2 - (p.1 + Real.smoothAbs ε p.1) / 2) = p.1 := by ring
    apply Prod.ext
    · exact h
    · dsimp [Real.smoothMax]
      rw [h]
      ring
  contMDiff_toFun := ((contDiff_fst.sub contDiff_snd).prodMk
    (Real.smoothMax.contDiff ε)).contMDiff
  contMDiff_invFun := by
    have h := (Real.smoothAbs.contDiff ε).comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    exact ((contDiff_snd.add ((contDiff_fst.sub h).div_const 2)).prodMk
      (contDiff_snd.sub ((contDiff_fst.add h).div_const 2))).contMDiff

@[simp] theorem smoothMax_apply (ε : ℝ) (p : ℝ × ℝ) :
    smoothMax ε p = (p.1 - p.2, Real.smoothMax ε p.1 p.2) := rfl

theorem smoothMax_symm_apply (ε : ℝ) (p : ℝ × ℝ) :
    (smoothMax ε).symm p = (p.2 + (p.1 - Real.smoothAbs ε p.1) / 2,
      p.2 - (p.1 + Real.smoothAbs ε p.1) / 2) := rfl

end Diffeomorph
