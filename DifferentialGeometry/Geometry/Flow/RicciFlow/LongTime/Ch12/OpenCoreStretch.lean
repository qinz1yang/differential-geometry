import DifferentialGeometry.Analysis.Calculus.Interpolation.HalfLineStretch
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Analysis
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

/-- Shift the supplied half-line stretch so that the finite endpoint is zero. -/
theorem exists_negative_stretch_CX1 {r : ℝ} (hr : 0 < r) :
    ∃ D : Diffeomorph 𝓘(ℝ) 𝓘(ℝ)
      (⟨Iio (0 : ℝ), isOpen_Iio⟩ : TopologicalSpace.Opens ℝ) ℝ ∞,
      StrictMono D ∧
      (∀ x, x.val ≤ -(2 * r / 3) → D x = x.val) ∧
      (∀ y, y ≤ -(2 * r / 3) → (D.symm y).val = y) ∧
      (∀ y, -r < (D.symm y).val ↔ -r < y) := by
  obtain ⟨A, _, hmono, hfix, hinv, _, _⟩ := exists_diffeomorph_Iio_eq_halfLineStretch hr
  let U : TopologicalSpace.Opens ℝ := ⟨Iio (0 : ℝ), isOpen_Iio⟩
  let V : TopologicalSpace.Opens ℝ := ⟨Iio r, isOpen_Iio⟩
  let shift : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) U V ∞ := {
    toFun := fun x => ⟨x.val + r, by change x.val + r < r; have hx : x.val < 0 := x.property; linarith⟩
    invFun := fun x => ⟨x.val - r, by change x.val - r < 0; exact sub_neg.mpr x.property⟩
    left_inv := fun x => Subtype.ext (add_sub_cancel_right x.val r)
    right_inv := fun x => Subtype.ext (sub_add_cancel x.val r)
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff V _).mp
      (contMDiff_subtype_val.add contMDiff_const)
    contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp
      ((contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_subtype_val) }
  let back : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ := {
    toFun := fun x => x - r
    invFun := fun x => x + r
    left_inv := fun x => sub_add_cancel x r
    right_inv := fun x => add_sub_cancel_right x r
    contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let D := (shift.trans A).trans back
  have hD (x : U) : D x = A (shift x) - r := rfl
  have hi (y : ℝ) : (D.symm y).val = (A.symm (y + r)).val - r := rfl
  have hDm : StrictMono D := by
    intro x y hxy
    change A (shift x) - r < A (shift y) - r
    have hs : shift x < shift y := by
      change x.val + r < y.val + r
      have hxy' : x.val < y.val := hxy
      linarith
    have hA := hmono hs
    linarith
  have hf (x : U) (hx : x.val ≤ -(2 * r / 3)) : D x = x.val := by
    rw [hD, hfix (shift x) (by change x.val + r ≤ r / 3; linarith)]
    exact add_sub_cancel_right x.val r
  have hfi (y : ℝ) (hy : y ≤ -(2 * r / 3)) : (D.symm y).val = y := by
    rw [hi, hinv (y + r) (by linarith)]
    exact add_sub_cancel_right y r
  refine ⟨D, hDm, hf, hfi, ?_⟩
  intro y
  let x : U := ⟨-r, neg_lt_zero.mpr hr⟩
  have hx : D x = -r := hf x (by change -r ≤ -(2 * r / 3); linarith)
  calc
    -r < (D.symm y).val ↔ x < D.symm y := Iff.rfl
    _ ↔ D x < D (D.symm y) := hDm.lt_iff_lt.symm
    _ ↔ -r < y := by rw [hx, D.apply_symm_apply]

def negativeStretch_CX1 {r : ℝ} (hr : 0 < r) :
    Diffeomorph 𝓘(ℝ) 𝓘(ℝ)
      (⟨Iio (0 : ℝ), isOpen_Iio⟩ : TopologicalSpace.Opens ℝ) ℝ ∞ :=
  Classical.choose (exists_negative_stretch_CX1 hr)

def compressHeight_CX1 {r : ℝ} (hr : 0 < r) (t : ℝ) : ℝ :=
  ((negativeStretch_CX1 hr).symm t).val

theorem compressHeight_lt_zero_CX1 {r : ℝ} (hr : 0 < r) (t : ℝ) :
    compressHeight_CX1 hr t < 0 := ((negativeStretch_CX1 hr).symm t).property

theorem compressHeight_lower_CX1 {r : ℝ} (hr : 0 < r) (t : ℝ) :
    -r < compressHeight_CX1 hr t ↔ -r < t :=
  (Classical.choose_spec (exists_negative_stretch_CX1 hr)).2.2.2 t

theorem compressHeight_fixed_CX1 {r : ℝ} (hr : 0 < r) {t : ℝ}
    (ht : t ≤ -(2 * r / 3)) : compressHeight_CX1 hr t = t :=
  (Classical.choose_spec (exists_negative_stretch_CX1 hr)).2.2.1 t ht

theorem compressHeight_injective_CX1 {r : ℝ} (hr : 0 < r) :
    Injective (compressHeight_CX1 hr) :=
  Subtype.val_injective.comp (negativeStretch_CX1 hr).symm.injective

theorem compressHeight_local_CX1 {r : ℝ} (hr : 0 < r) :
    IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ (compressHeight_CX1 hr) :=
  DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (⟨Iio (0 : ℝ), isOpen_Iio⟩ : TopologicalSpace.Opens ℝ))
    (negativeStretch_CX1 hr).symm.isLocalDiffeomorph

theorem compressHeight_surjective_negative_CX1 {r : ℝ} (hr : 0 < r)
    {t : ℝ} (ht : t < 0) (htr : -r < t) :
    ∃ s : ℝ, -r < s ∧ compressHeight_CX1 hr s = t := by
  let x : (⟨Iio (0 : ℝ), isOpen_Iio⟩ : TopologicalSpace.Opens ℝ) := ⟨t, ht⟩
  refine ⟨negativeStretch_CX1 hr x, ?_, ?_⟩
  · apply (compressHeight_lower_CX1 hr _).mp
    change -r < ((negativeStretch_CX1 hr).symm (negativeStretch_CX1 hr x)).val
    rwa [Diffeomorph.symm_apply_apply]
  · exact congrArg Subtype.val ((negativeStretch_CX1 hr).symm_apply_apply x)

end GC.LongTime.Ch12
