import DifferentialGeometry.Geometry.Connection.ConnectionForm.Curvature

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem connectionFormCovDeriv_contDiffAt
    {n : ℕ∞ω} {A : V → V →L[ℝ] E →L[ℝ] E}
    {s : V → E} {X : V → V} {x : V}
    (hA : ContDiffAt ℝ n A x) (hs : ContDiffAt ℝ (n + 1) s x)
    (hX : ContDiffAt ℝ n X x) :
    ContDiffAt ℝ n (fun y => connectionFormCovDeriv A s (X y) y) x := by
  exact ((hs.fderiv_right (le_refl _)).clm_apply hX).add
    ((hA.clm_apply hX).clm_apply (hs.of_le (le_add_of_nonneg_right (by simp))))

theorem connectionFormCurvature_contDiffAt
    {n : ℕ∞ω} {A : V → V →L[ℝ] E →L[ℝ] E}
    {X Y : V → V} {s : V → E} {x : V}
    (hA : ContDiffAt ℝ (n + 1) A x)
    (hX : ContDiffAt ℝ n X x) (hY : ContDiffAt ℝ n Y x)
    (hs : ContDiffAt ℝ n s x) :
    ContDiffAt ℝ n (fun y => connectionFormCurvature A y (X y) (Y y) (s y)) x := by
  have hD : ContDiffAt ℝ n (fderiv ℝ A) x := hA.fderiv_right (le_refl _)
  have hA' : ContDiffAt ℝ n A x := hA.of_le (le_add_of_nonneg_right (by simp))
  exact (((((hD.clm_apply hX).clm_apply hY).clm_apply hs).sub
    (((hD.clm_apply hY).clm_apply hX).clm_apply hs)).add
      ((hA'.clm_apply hX).clm_apply ((hA'.clm_apply hY).clm_apply hs))).sub
        ((hA'.clm_apply hY).clm_apply ((hA'.clm_apply hX).clm_apply hs))

theorem connectionFormCurvature_contDiffOn
    {n : ℕ∞ω} {A : V → V →L[ℝ] E →L[ℝ] E}
    {X Y : V → V} {s : V → E} {U : Set V} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (n + 1) A U)
    (hX : ContDiffOn ℝ n X U) (hY : ContDiffOn ℝ n Y U)
    (hs : ContDiffOn ℝ n s U) :
    ContDiffOn ℝ n (fun y => connectionFormCurvature A y (X y) (Y y) (s y)) U := by
  intro x hx
  exact (connectionFormCurvature_contDiffAt (hA.contDiffAt (hU.mem_nhds hx))
    (hX.contDiffAt (hU.mem_nhds hx)) (hY.contDiffAt (hU.mem_nhds hx))
    (hs.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

end DifferentialGeometry.Geometry.Connection
