import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# The radial profile of the dihedral model of `RP³ # RP³`

Chapter 7, packet P8c. With `ω = 3π/4` the profile
`μ s = 2 cos (ω (s + 1/4)) / cos (ω (s - 1/4))` is smooth, positive and strictly decreasing on
`(-5/12, 5/12)`, satisfies the inversion identity `μ s * μ (-s) = 4` and, with
`κ = 2 cos (3π/8) = μ (1/4)`, the neck identity `μ s + μ (1/2 - s) = 2κ`. In stereographic
coordinates `w ↦ π (σ⁻¹ (μ s • w))` the first identity is the antipodal map and the second one is
the affine collar gluing `r ↦ 2 - r` of the connected sum.
-/

set_option autoImplicit false

noncomputable section

open Real Set
open scoped ContDiff

namespace GC.Geometry.SphericalProduct

def dihedralFrequency : ℝ := 3 * π / 4

def dihedralProfile (s : ℝ) : ℝ :=
  2 * cos (dihedralFrequency * (s + 1 / 4)) / cos (dihedralFrequency * (s - 1 / 4))

def dihedralNeck : ℝ := 2 * cos (3 * π / 8)

def dihedralDomain : Set ℝ := Ioo (-(5 / 12)) (5 / 12)

theorem isOpen_dihedralDomain : IsOpen dihedralDomain := isOpen_Ioo

theorem Icc_subset_dihedralDomain : Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ dihedralDomain :=
  Icc_subset_Ioo (by norm_num) (by norm_num)

theorem cos_dihedral_add_pos {s : ℝ} (hs : s ∈ dihedralDomain) :
    0 < cos (dihedralFrequency * (s + 1 / 4)) := by
  apply cos_pos_of_mem_Ioo
  have h1 : 0 < π * (3 * (s + 1 / 4) / 4 + 1 / 2) := mul_pos pi_pos (by linarith [hs.1])
  have h2 : 0 < π * (1 / 2 - 3 * (s + 1 / 4) / 4) := mul_pos pi_pos (by linarith [hs.2])
  unfold dihedralFrequency
  constructor <;> nlinarith

theorem cos_dihedral_sub_pos {s : ℝ} (hs : s ∈ dihedralDomain) :
    0 < cos (dihedralFrequency * (s - 1 / 4)) := by
  apply cos_pos_of_mem_Ioo
  have h1 : 0 < π * (3 * (s - 1 / 4) / 4 + 1 / 2) := mul_pos pi_pos (by linarith [hs.1])
  have h2 : 0 < π * (1 / 2 - 3 * (s - 1 / 4) / 4) := mul_pos pi_pos (by linarith [hs.2])
  unfold dihedralFrequency
  constructor <;> nlinarith

theorem dihedralProfile_pos {s : ℝ} (hs : s ∈ dihedralDomain) : 0 < dihedralProfile s :=
  div_pos (mul_pos two_pos (cos_dihedral_add_pos hs)) (cos_dihedral_sub_pos hs)

theorem neg_mem_dihedralDomain {s : ℝ} (hs : s ∈ dihedralDomain) : -s ∈ dihedralDomain :=
  ⟨by linarith [hs.2], by linarith [hs.1]⟩

theorem dihedralProfile_mul_neg {s : ℝ} (hs : s ∈ dihedralDomain) :
    dihedralProfile s * dihedralProfile (-s) = 4 := by
  have ha := (cos_dihedral_add_pos hs).ne'
  have hb := (cos_dihedral_sub_pos hs).ne'
  have e1 : dihedralFrequency * (-s + 1 / 4) = -(dihedralFrequency * (s - 1 / 4)) := by ring
  have e2 : dihedralFrequency * (-s - 1 / 4) = -(dihedralFrequency * (s + 1 / 4)) := by ring
  unfold dihedralProfile
  rw [e1, e2, cos_neg, cos_neg, div_mul_div_comm, div_eq_iff (mul_ne_zero hb ha)]
  ring

theorem cos_three_pi_div_eight_pos : 0 < cos (3 * π / 8) := by
  apply cos_pos_of_mem_Ioo
  constructor <;> linarith [pi_pos]

theorem dihedralNeck_pos : 0 < dihedralNeck := mul_pos two_pos cos_three_pi_div_eight_pos

theorem dihedralNeck_lt_one : dihedralNeck < 1 := by
  have h : cos (3 * π / 8) < cos (π / 3) :=
    cos_lt_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) (by linarith [pi_pos])
      (by linarith [pi_pos])
  rw [cos_pi_div_three] at h
  unfold dihedralNeck
  linarith

theorem dihedralProfile_quarter : dihedralProfile (1 / 4) = dihedralNeck := by
  unfold dihedralProfile dihedralNeck dihedralFrequency
  rw [show 3 * π / 4 * (1 / 4 + 1 / 4) = 3 * π / 8 by ring,
    show 3 * π / 4 * (1 / 4 - 1 / 4 : ℝ) = 0 by ring, cos_zero, div_one]

theorem dihedralProfile_neg_quarter : dihedralProfile (-(1 / 4)) = 4 / dihedralNeck := by
  have hc := cos_three_pi_div_eight_pos.ne'
  unfold dihedralProfile dihedralNeck dihedralFrequency
  rw [show 3 * π / 4 * (-(1 / 4) + 1 / 4) = 0 by ring,
    show 3 * π / 4 * (-(1 / 4) - 1 / 4 : ℝ) = -(3 * π / 8) by ring, cos_zero, cos_neg]
  field_simp
  ring

theorem exists_hasDerivAt_dihedralProfile {s : ℝ} (hs : s ∈ dihedralDomain) :
    ∃ d, d < 0 ∧ HasDerivAt dihedralProfile d s := by
  set k := dihedralFrequency with hk
  have hA : HasDerivAt (fun t => 2 * cos (k * (t + 1 / 4)))
      (2 * (-sin (k * (s + 1 / 4)) * (k * 1))) s :=
    ((((hasDerivAt_id s).add_const (1 / 4)).const_mul k).cos).const_mul 2
  have hB : HasDerivAt (fun t => cos (k * (t - 1 / 4))) (-sin (k * (s - 1 / 4)) * (k * 1)) s :=
    (((hasDerivAt_id s).sub_const (1 / 4)).const_mul k).cos
  have hbpos := cos_dihedral_sub_pos hs
  refine ⟨_, ?_, hA.div hB hbpos.ne'⟩
  have hsin : sin (k * (s - 1 / 4) - k * (s + 1 / 4)) =
      sin (k * (s - 1 / 4)) * cos (k * (s + 1 / 4)) -
        cos (k * (s - 1 / 4)) * sin (k * (s + 1 / 4)) := sin_sub _ _
  rw [show k * (s - 1 / 4) - k * (s + 1 / 4) = -(3 * π / 8) from (by
    rw [hk]; unfold dihedralFrequency; ring), sin_neg] at hsin
  have hs8 : 0 < sin (3 * π / 8) := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos])
    (by linarith [pi_pos])
  have hkpos : 0 < k := by rw [hk]; unfold dihedralFrequency; linarith [pi_pos]
  apply div_neg_of_neg_of_pos _ (pow_pos hbpos 2)
  have : 2 * (-sin (k * (s + 1 / 4)) * (k * 1)) * cos (k * (s - 1 / 4)) -
      2 * cos (k * (s + 1 / 4)) * (-sin (k * (s - 1 / 4)) * (k * 1)) =
      2 * k * (-sin (3 * π / 8)) := by rw [hsin]; ring
  rw [this]
  nlinarith

theorem contDiffOn_dihedralProfile :
    ContDiffOn ℝ ∞ dihedralProfile dihedralDomain := by
  have hA : ContDiff ℝ ∞ (fun t : ℝ => 2 * cos (dihedralFrequency * (t + 1 / 4))) :=
    contDiff_const.mul (contDiff_cos.comp (contDiff_const.mul (contDiff_id.add contDiff_const)))
  have hB : ContDiff ℝ ∞ (fun t : ℝ => cos (dihedralFrequency * (t - 1 / 4))) :=
    contDiff_cos.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact hA.contDiffOn.div hB.contDiffOn fun t ht => (cos_dihedral_sub_pos ht).ne'

theorem continuousOn_dihedralProfile : ContinuousOn dihedralProfile dihedralDomain :=
  contDiffOn_dihedralProfile.continuousOn

theorem strictAntiOn_dihedralProfile : StrictAntiOn dihedralProfile dihedralDomain := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) continuousOn_dihedralProfile
  intro x hx
  simp only [interior_Ioo] at hx
  obtain ⟨d, hd, hD⟩ := exists_hasDerivAt_dihedralProfile hx
  rw [hD.deriv]
  exact hd

theorem dihedralProfile_add_reflect {s : ℝ} (hs : s ∈ dihedralDomain) :
    dihedralProfile s + dihedralProfile (1 / 2 - s) = 2 * dihedralNeck := by
  have hb := (cos_dihedral_sub_pos hs).ne'
  unfold dihedralProfile dihedralNeck
  rw [show dihedralFrequency * (1 / 2 - s - 1 / 4) = -(dihedralFrequency * (s - 1 / 4)) by ring,
    cos_neg, ← add_div, ← mul_add, cos_add_cos,
    show (dihedralFrequency * (s + 1 / 4) + dihedralFrequency * (1 / 2 - s + 1 / 4)) / 2 =
      3 * π / 8 by unfold dihedralFrequency; ring,
    show (dihedralFrequency * (s + 1 / 4) - dihedralFrequency * (1 / 2 - s + 1 / 4)) / 2 =
      dihedralFrequency * (s - 1 / 4) by ring, div_eq_iff hb]
  ring

theorem exists_dihedralProfile_eq {r : ℝ} (hr : r ∈ Icc dihedralNeck (4 / dihedralNeck)) :
    ∃ t ∈ Icc (-(1 / 4) : ℝ) (1 / 4), dihedralProfile t = r := by
  have h := intermediate_value_Icc' (show (-(1 / 4) : ℝ) ≤ 1 / 4 by norm_num)
    (continuousOn_dihedralProfile.mono Icc_subset_dihedralDomain)
  rw [dihedralProfile_quarter, dihedralProfile_neg_quarter] at h
  exact h hr

theorem dihedralProfile_le_neck_iff {t : ℝ} (ht : t ∈ dihedralDomain) :
    dihedralProfile t ≤ dihedralNeck ↔ 1 / 4 ≤ t := by
  rw [← dihedralProfile_quarter]
  exact strictAntiOn_dihedralProfile.le_iff_ge ht (Icc_subset_dihedralDomain ⟨by norm_num,
    le_rfl⟩)

theorem dihedralProfile_lt_neck_iff {t : ℝ} (ht : t ∈ dihedralDomain) :
    dihedralProfile t < dihedralNeck ↔ 1 / 4 < t := by
  rw [← dihedralProfile_quarter]
  exact strictAntiOn_dihedralProfile.lt_iff_gt ht (Icc_subset_dihedralDomain ⟨by norm_num,
    le_rfl⟩)

theorem le_dihedralProfile_iff {t : ℝ} (ht : t ∈ dihedralDomain) :
    4 / dihedralNeck ≤ dihedralProfile t ↔ t ≤ -(1 / 4) := by
  rw [← dihedralProfile_neg_quarter]
  exact strictAntiOn_dihedralProfile.le_iff_ge (Icc_subset_dihedralDomain ⟨le_rfl,
    by norm_num⟩) ht

theorem lt_dihedralProfile_iff {t : ℝ} (ht : t ∈ dihedralDomain) :
    4 / dihedralNeck < dihedralProfile t ↔ t < -(1 / 4) := by
  rw [← dihedralProfile_neg_quarter]
  exact strictAntiOn_dihedralProfile.lt_iff_gt (Icc_subset_dihedralDomain ⟨le_rfl,
    by norm_num⟩) ht

end GC.Geometry.SphericalProduct
