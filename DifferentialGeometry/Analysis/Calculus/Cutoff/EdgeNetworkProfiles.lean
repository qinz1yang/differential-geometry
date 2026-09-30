import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalProfiles
import DifferentialGeometry.Analysis.Calculus.FlatTailDerivativeBounds

set_option autoImplicit false
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

noncomputable def edgeCoordinateProfile : ℝ → ℝ := intervalPlateauProfile (-9) (-8) 8 9
noncomputable def edgeHeightProfile : ℝ → ℝ := descendingIntervalProfile 8 9
noncomputable def jointHeightProfile : ℝ → ℝ := intervalPlateauProfile (1 / 5) (3 / 10) 8 9
noncomputable def edgeSumProfile (x : ℝ) : ℝ := 1 - descendingIntervalProfile (1 / 2) 1 x

theorem edgeProfiles_contDiff : ContDiff ℝ ∞ edgeCoordinateProfile ∧
    ContDiff ℝ ∞ edgeHeightProfile ∧ ContDiff ℝ ∞ jointHeightProfile ∧
    ContDiff ℝ ∞ edgeSumProfile :=
  ⟨contDiff_intervalPlateauProfile _ _ _ _, contDiff_descendingIntervalProfile _ _,
    contDiff_intervalPlateauProfile _ _ _ _, contDiff_const.sub (contDiff_descendingIntervalProfile _ _)⟩

theorem edgeProfiles_mem_Icc (x : ℝ) : edgeCoordinateProfile x ∈ Icc 0 1 ∧
    edgeHeightProfile x ∈ Icc 0 1 ∧ jointHeightProfile x ∈ Icc 0 1 ∧ edgeSumProfile x ∈ Icc 0 1 := by
  refine ⟨intervalPlateauProfile_mem_Icc _ _ _ _ _, descendingIntervalProfile_mem_Icc _ _ _,
    intervalPlateauProfile_mem_Icc _ _ _ _ _, ?_⟩
  have hh := descendingIntervalProfile_mem_Icc (1 / 2) 1 x
  constructor <;> dsimp [edgeSumProfile] <;> linarith [hh.1, hh.2]

theorem edgeProfiles_support : tsupport edgeCoordinateProfile ⊆ Icc (-9) 9 ∧
    tsupport jointHeightProfile ⊆ Icc (1 / 5) 9 :=
  ⟨tsupport_intervalPlateauProfile_subset (by norm_num) (by norm_num),
    tsupport_intervalPlateauProfile_subset (by norm_num) (by norm_num)⟩

theorem edgeSumProfile_zero {x : ℝ} (hx : x ≤ 1 / 2) : edgeSumProfile x = 0 := by
  rw [edgeSumProfile, descendingIntervalProfile_one (by norm_num) hx, sub_self]

theorem edgeSumProfile_one {x : ℝ} (hx : 1 ≤ x) : edgeSumProfile x = 1 := by
  rw [edgeSumProfile, descendingIntervalProfile_zero (by norm_num) hx, sub_zero]

theorem edgeProfiles_low_height {x : ℝ} (hx : x < 3 / 20) :
    edgeHeightProfile x = 1 ∧ jointHeightProfile x = 0 :=
  ⟨descendingIntervalProfile_one (by norm_num) (by linarith),
    intervalPlateauProfile_zero_left (by norm_num) (by linarith)⟩

theorem edgeProfiles_plateaus {x : ℝ} :
    (x ∈ Icc (-8) 8 → edgeCoordinateProfile x = 1) ∧
    (x ∈ Icc (3 / 10) 8 → jointHeightProfile x = 1) :=
  ⟨intervalPlateauProfile_one (by norm_num) (by norm_num),
    intervalPlateauProfile_one (by norm_num) (by norm_num)⟩

theorem exists_edgeProfiles_derivative_bounds :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ f ∈ ({edgeCoordinateProfile, edgeHeightProfile, jointHeightProfile,
      edgeSumProfile} : Set (ℝ → ℝ)),
      (∀ x, ‖fderiv ℝ f x‖ ≤ P) ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P := by
  have hreg := edgeProfiles_contDiff
  obtain ⟨A, hA, hDA, hDDA⟩ := exists_derivative_bounds_of_constant_tails
    (hreg.1.of_le (by simp) : ContDiff ℝ 2 edgeCoordinateProfile)
    (fun x hx => intervalPlateauProfile_zero_left (a := (-9 : ℝ)) (b := -8) (c := 8) (d := 9)
      (by norm_num) hx)
    (fun x hx => intervalPlateauProfile_zero_right (a := (-9 : ℝ)) (b := -8) (c := 8) (d := 9)
      (by norm_num) hx)
  obtain ⟨B, hB, hDB, hDDB⟩ := exists_derivative_bounds_of_constant_tails
    (hreg.2.1.of_le (by simp) : ContDiff ℝ 2 edgeHeightProfile)
    (fun x hx => descendingIntervalProfile_one (a := (8 : ℝ)) (b := 9) (by norm_num) hx)
    (fun x hx => descendingIntervalProfile_zero (a := (8 : ℝ)) (b := 9) (by norm_num) hx)
  obtain ⟨C, hC, hDC, hDDC⟩ := exists_derivative_bounds_of_constant_tails
    (hreg.2.2.1.of_le (by simp) : ContDiff ℝ 2 jointHeightProfile)
    (fun x hx => intervalPlateauProfile_zero_left (a := (1 / 5 : ℝ)) (b := 3 / 10) (c := 8) (d := 9)
      (by norm_num) hx)
    (fun x hx => intervalPlateauProfile_zero_right (a := (1 / 5 : ℝ)) (b := 3 / 10) (c := 8) (d := 9)
      (by norm_num) hx)
  obtain ⟨D, hD, hDD, hDDD⟩ := exists_derivative_bounds_of_constant_tails
    (hreg.2.2.2.of_le (by simp) : ContDiff ℝ 2 edgeSumProfile)
    (fun _ hx => edgeSumProfile_zero hx) (fun _ hx => edgeSumProfile_one hx)
  have hAP : A ≤ A + B + C + D := by linarith
  have hBP : B ≤ A + B + C + D := by linarith
  have hCP : C ≤ A + B + C + D := by linarith
  have hDP : D ≤ A + B + C + D := by linarith
  refine ⟨A + B + C + D, by linarith, ?_⟩
  intro f hf
  simp only [mem_insert_iff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨fun x => (hDA x).trans hAP, fun x => (hDDA x).trans hAP⟩
  · exact ⟨fun x => (hDB x).trans hBP, fun x => (hDDB x).trans hBP⟩
  · exact ⟨fun x => (hDC x).trans hCP, fun x => (hDDC x).trans hCP⟩
  · exact ⟨fun x => (hDD x).trans hDP, fun x => (hDDD x).trans hDP⟩

noncomputable def edgeProfileDerivativeBound : ℝ := Classical.choose exists_edgeProfiles_derivative_bounds

theorem edgeProfileDerivativeBound_ge_one : 1 ≤ edgeProfileDerivativeBound :=
  (Classical.choose_spec exists_edgeProfiles_derivative_bounds).1

theorem edgeProfiles_derivative_le {f : ℝ → ℝ}
    (hf : f ∈ ({edgeCoordinateProfile, edgeHeightProfile, jointHeightProfile,
      edgeSumProfile} : Set (ℝ → ℝ))) :
    (∀ x, ‖fderiv ℝ f x‖ ≤ edgeProfileDerivativeBound) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ edgeProfileDerivativeBound :=
  (Classical.choose_spec exists_edgeProfiles_derivative_bounds).2 f hf

end DifferentialGeometry.Analysis
