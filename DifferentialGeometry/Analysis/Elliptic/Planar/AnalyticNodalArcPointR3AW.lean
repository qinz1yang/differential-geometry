import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalPrincipalR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalPolarR3AW
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarBlowup

/-!
# R3a-ω（`_R3AW`）F4b：仿射换元 jets 与极坐标弧点

`u y = w (p + T y)` 的 jets 是 `D^j w(p) ∘ T^{⊗ j}`；`arcPointR3AW T p r θ = p + T (r e^{iθ})` 的范数、
沿 `r`（带角函数 `ϑ(r)`）与沿 `θ` 的导数，以及径向弧的速度非零。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- 仿射换元 `u y = w (p + T y)` 的 jets：`D^j u (0) m = D^j w (p) (T ∘ m)`。 -/
theorem iteratedFDeriv_affine_comp_R3AW (w : ℂ → ℝ) (p : ℂ) (T : ℂ ≃L[ℝ] ℂ) (j : ℕ)
    (m : Fin j → ℂ) :
    iteratedFDeriv ℝ j (fun y => w (p + T y)) 0 m = iteratedFDeriv ℝ j w p (fun i => T (m i)) := by
  have h1 : (fun y => w (p + T y)) = (fun z => w (p + z)) ∘ T := rfl
  have h2 := T.iteratedFDerivWithin_comp_right (fun z => w (p + z)) uniqueDiffOn_univ
    (show T 0 ∈ (univ : Set ℂ) from mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h2
  rw [h1, h2]
  rw [iteratedFDeriv_comp_add_left]
  simp

/-- 极坐标点 `p + T (r e^{iθ})`。 -/
def arcPointR3AW (T : ℂ ≃L[ℝ] ℂ) (p : ℂ) (r θ : ℝ) : ℂ :=
  p + T ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

theorem norm_symm_arcPoint_R3AW (T : ℂ ≃L[ℝ] ℂ) (p : ℂ) (r θ : ℝ) :
    ‖T.symm (arcPointR3AW T p r θ - p)‖ = |r| := by
  simp only [arcPointR3AW, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

theorem arcPoint_zero_R3AW (T : ℂ ≃L[ℝ] ℂ) (p : ℂ) (θ : ℝ) : arcPointR3AW T p 0 θ = p := by
  simp [arcPointR3AW]

/-- 沿径向弧 `r ↦ p + T (r e^{iϑ(r)})` 的导数。 -/
theorem hasDerivAt_arcPoint_R3AW (T : ℂ ≃L[ℝ] ℂ) (p : ℂ) {ϑ : ℝ → ℝ} {ϑ' r : ℝ}
    (h : HasDerivAt ϑ ϑ' r) :
    HasDerivAt (fun s => arcPointR3AW T p s (ϑ s))
      (T (Complex.exp ((ϑ r : ℝ) * Complex.I) *
        (1 + ((r * ϑ' : ℝ) : ℂ) * Complex.I))) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((ϑ s : ℝ) * Complex.I))
      (Complex.exp ((ϑ r : ℝ) * Complex.I) * ((ϑ' : ℂ) * Complex.I)) r := by
    have := (h.ofReal_comp.mul_const Complex.I).cexp
    simpa using this
  have h3 := h1.mul h2
  have h4 := T.hasFDerivAt.comp_hasDerivAt r h3
  have h5 := h4.const_add p
  convert h5 using 1
  · funext s
    rfl
  · change T _ = T _
    congr 1
    push_cast
    ring

theorem hasDerivAt_arcPoint_angle_R3AW (T : ℂ ≃L[ℝ] ℂ) (p : ℂ) (r t : ℝ) :
    HasDerivAt (fun s : ℝ => arcPointR3AW T p r s)
      (T ((r : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I)) Complex.I t := by
    simpa using (hasDerivAt_id t).ofReal_comp.mul_const Complex.I
  have h2 := (h1.cexp).const_mul (r : ℂ)
  have h3 := T.hasFDerivAt.comp_hasDerivAt t h2
  have h4 := h3.const_add p
  convert h4 using 1
  · funext s
    rfl
  · change T _ = T _
    congr 1

theorem arcDeriv_ne_zero_R3AW (T : ℂ ≃L[ℝ] ℂ) (ϑ x : ℝ) :
    T (Complex.exp ((ϑ : ℝ) * Complex.I) * (1 + ((x : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
  intro h
  have h0 : Complex.exp ((ϑ : ℝ) * Complex.I) * (1 + ((x : ℝ) : ℂ) * Complex.I) = 0 := by
    simpa using h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Complex.exp_ne_zero _ h1
  · have := congrArg Complex.re h1
    simp at this

end DifferentialGeometry.Analysis
