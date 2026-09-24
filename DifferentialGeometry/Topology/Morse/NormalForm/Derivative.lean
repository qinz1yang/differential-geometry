import DifferentialGeometry.Topology.Morse.Attachment.ModelCell

open scoped ContDiff

namespace DifferentialGeometry.Topology.Morse.CellAttachment

theorem contDiff_morseNormalForm {n k : ℕ} {m : ℕ∞ω} (hk : k ≤ n) (c : ℝ) :
    ContDiff ℝ m (morseNormalForm hk c) := by
  unfold morseNormalForm
  fun_prop

theorem fderiv_morseNormalForm {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
  have hp := (contDiff_posPart_normSq hk).differentiable (by simp) |>.differentiableAt (x := y)
  have hn := (contDiff_negPart_normSq hk).differentiable (by simp) |>.differentiableAt (x := y)
  have heq : morseNormalForm hk c = fun z => c + (1 / 2) *
      (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) := funext (morseNormalForm_split hk c)
  have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
      ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hp.sub hn
  rw [heq, fderiv_const_add, fderiv_const_mul hsub, fderiv_fun_sub hp hn]

theorem fderiv_morseNormalForm_eq_zero_iff {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    fderiv ℝ (morseNormalForm hk c) y = 0 ↔ y = 0 := by
  rw [fderiv_morseNormalForm]
  constructor
  · intro h
    have hneg := congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (negPart hk y) 0)) h
    have hpos := congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk 0 (posPart hk y))) h
    simp only [smul_apply, sub_apply,
      fderiv_posPart_normSq_zero_direction, fderiv_negPart_normSq_self,
      fderiv_posPart_normSq_self, fderiv_negPart_normSq_zero_direction,
      zero_apply, smul_eq_mul] at hneg hpos
    have hn : negPart hk y = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖negPart hk y‖])
    have hp : posPart hk y = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖posPart hk y‖])
    rw [← recombine_decompose hk y, hn, hp]
    funext i
    simp [recombine]
  · rintro rfl
    ext v
    rw [smul_apply, sub_apply, fderiv_posPart_normSq, fderiv_negPart_normSq]
    simp [posPart, negPart]

theorem fderiv_morseNormalForm_euclidean_eq_zero_iff {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => morseNormalForm hk c (EuclideanSpace.equiv (Fin n) ℝ z)) y = 0 ↔
      y = 0 := by
  let L := EuclideanSpace.equiv (Fin n) ℝ
  have hder : fderiv ℝ (fun z => morseNormalForm hk c (L z)) y =
      (fderiv ℝ (morseNormalForm hk c) (L y)).comp L.toContinuousLinearMap := by
    exact (fderiv_comp y
      ((contDiff_morseNormalForm (m := ∞) hk c).differentiable (by simp) |>.differentiableAt)
      L.differentiableAt).trans (congrArg (fun A => (fderiv ℝ (morseNormalForm hk c) (L y)).comp A)
        L.fderiv)
  rw [hder]
  constructor
  · intro hz
    have hzero : fderiv ℝ (morseNormalForm hk c) (L y) = 0 := by
      ext v
      have h := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (L.symm v)) hz
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        L.apply_symm_apply, zero_apply] using h
    apply L.injective
    rw [(fderiv_morseNormalForm_eq_zero_iff hk c (L y)).mp hzero, map_zero]
  · rintro rfl
    rw [map_zero, (fderiv_morseNormalForm_eq_zero_iff hk c 0).mpr rfl,
      ContinuousLinearMap.zero_comp]

end DifferentialGeometry.Topology.Morse.CellAttachment
