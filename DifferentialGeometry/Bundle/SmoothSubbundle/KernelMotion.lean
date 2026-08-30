import DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]

theorem hasDerivAt_apply_eq_zero_of_continuousLinearMap
    {A : Real → E →L[Real] F} {w : Real → E}
    {A' : E →L[Real] F} {w' : E} {t : Real}
    (hA : HasDerivAt A A' t) (hw : HasDerivAt w w' t)
    (hzero : ∀ s, A s (w s) = 0) :
    A' (w t) + A t w' = 0 := by
  have hprod : HasDerivAt (fun s => A s (w s))
      (A' (w t) + A t w') t := hA.clm_apply hw
  have hconst : HasDerivAt (fun _ : Real => (0 : F)) 0 t :=
    hasDerivAt_const t 0
  have hzero' : HasDerivAt (fun s => A s (w s)) 0 t := by
    simpa only [hzero] using hconst
  exact hprod.unique hzero'

theorem continuousLinearMap_eq_zero_of_isPositive_inner_eq_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {B : E →L[Real] E} (hB : B.IsPositive) {w : E}
    (hw : ⟪B w, w⟫_ℝ = 0) : B w = 0 := by
  let b : LinearMap.BilinForm Real E := LinearMap.mk₂ Real
    (fun x y : E => ⟪B x, y⟫_ℝ)
    (by intros; rw [map_add, inner_add_left])
    (by intros; rw [map_smul]; simp [real_inner_smul_left])
    (by intros; rw [inner_add_right])
    (by intros; simp [real_inner_smul_right])
  have hbnonneg : ∀ x : E, 0 ≤ b x x := by
    intro x
    simpa [b] using hB.inner_nonneg_left x
  have hbsymm : LinearMap.IsSymm b := by
    refine ⟨?_⟩
    intro x y
    simpa [b, real_inner_comm] using hB.inner_left_eq_inner_right x y
  have hker : w ∈ LinearMap.ker b :=
    (b.apply_apply_same_eq_zero_iff hbnonneg hbsymm).mp (by simpa [b] using hw)
  have hbw : b w = 0 := LinearMap.mem_ker.mp hker
  apply ext_inner_left Real
  intro z
  have hz := congrArg (fun L : E →ₗ[Real] Real => L z) hbw
  change ⟪B w, z⟫_ℝ = 0 at hz
  rw [real_inner_comm]
  simpa using hz

theorem continuousLinearMap_kernel_annihilation_of_isPositive
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {A B : E →L[Real] E} (hB : B.IsPositive)
    (hzero : ∀ w : E, w ∈ A.ker → ⟪B w, w⟫_ℝ = 0) :
    ∀ w : E, w ∈ A.ker → B w = 0 := by
  intro w hw
  exact continuousLinearMap_eq_zero_of_isPositive_inner_eq_zero hB (hzero w hw)

theorem linearMap_kernel_annihilation_of_commuting
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {A B : E →ₗ[Real] E} (hB : B.IsSymmetric)
    (hcomm : B.comp A = A.comp B)
    (hzero : ∀ w : E, w ∈ A.ker → ⟪B w, w⟫_ℝ = 0) :
    ∀ w : E, w ∈ A.ker → B w = 0 := by
  intro w hw
  have hBwker : B w ∈ A.ker := by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun L : E →ₗ[Real] E => L w) hcomm
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hw,
      map_zero] at h
    exact h.symm
  have hquad_plus := hzero (w + B w) (A.ker.add_mem hw hBwker)
  have hquad_minus := hzero (w - B w) (A.ker.sub_mem hw hBwker)
  have hpair : ⟪B w, B w⟫_ℝ = 0 := by
    simp only [map_add, map_sub, inner_add_left, inner_sub_left,
      inner_add_right, inner_sub_right] at hquad_plus hquad_minus
    have hsymm : ⟪B (B w), w⟫_ℝ = ⟪B w, B w⟫_ℝ := by
      simpa using hB (B w) w
    nlinarith [hquad_plus, hquad_minus, hzero w hw, hsymm]
  have hnormsq : ‖B w‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hpair
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
