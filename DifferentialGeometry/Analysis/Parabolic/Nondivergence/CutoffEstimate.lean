import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem eLpNorm_cutoff_residual_le
    {μ : Measure E} {Ω : Set E} (hΩ : MeasurableSet Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u du f : E → V} {a η : E → ℝ}
    (hu : AEStronglyMeasurable u (μ.restrict Ω))
    (hdu : AEStronglyMeasurable du (μ.restrict Ω))
    (hf : AEStronglyMeasurable f (μ.restrict Ω))
    (et ex : E) (hηs : tsupport η ⊆ Ω) {A K0 Kt Kx Kxx : ℝ≥0}
    (ha : ∀ᵐ x ∂μ.restrict Ω, ‖a x‖ ≤ A)
    (hη : ∀ᵐ x ∂μ.restrict Ω, ‖η x‖ ≤ K0)
    (hηt : ∀ᵐ x ∂μ.restrict Ω, ‖fderiv ℝ η x et‖ ≤ Kt)
    (hηx : ∀ᵐ x ∂μ.restrict Ω, ‖fderiv ℝ η x ex‖ ≤ Kx)
    (hηxx : ∀ᵐ x ∂μ.restrict Ω,
      ‖fderiv ℝ (fun y => fderiv ℝ η y ex) x ex‖ ≤ Kxx) :
    eLpNorm (fun x => η x • f x + fderiv ℝ η x et • u x -
      a x • ((2 * fderiv ℝ η x ex) • du x +
        fderiv ℝ (fun y => fderiv ℝ η y ex) x ex • u x)) p μ ≤
      (K0 : ℝ≥0∞) * eLpNorm f p (μ.restrict Ω) +
      ((Kt + A * Kxx : ℝ≥0) : ℝ≥0∞) * eLpNorm u p (μ.restrict Ω) +
      ((2 * A * Kx : ℝ≥0) : ℝ≥0∞) * eLpNorm du p (μ.restrict Ω) := by
  let r : E → V := fun x => η x • f x + fderiv ℝ η x et • u x -
    a x • ((2 * fderiv ℝ η x ex) • du x +
      fderiv ℝ (fun y => fderiv ℝ η y ex) x ex • u x)
  have hr : Ω.indicator r = r := by
    funext x
    by_cases hx : x ∈ Ω
    · exact indicator_of_mem hx r
    · rw [indicator_of_notMem hx]
      have hηzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h))
      have hdηzero : fderiv ℝ η x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hηs h))
      have hd2ηzero : fderiv ℝ (fun y => fderiv ℝ η y ex) x = 0 :=
        fderiv_of_notMem_tsupport ℝ
          (fun h => hx (hηs (tsupport_fderiv_apply_subset ℝ ex h)))
      simp [r, hηzero, hdηzero, hd2ηzero]
  have hrnorm : eLpNorm r p μ = eLpNorm r p (μ.restrict Ω) := by
    rw [← hr, eLpNorm_indicator_eq_eLpNorm_restrict hΩ, hr]
  let F : E → ℝ := fun x => ‖f x‖
  let U : E → ℝ := fun x => ‖u x‖
  let D : E → ℝ := fun x => ‖du x‖
  let C : ℝ := Kt + A * Kxx
  let B : ℝ := 2 * A * Kx
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : ∀ᵐ x ∂μ.restrict Ω,
      ‖r x‖ ≤ (((K0 : ℝ) • F + C • U + B • D) x) := by
    filter_upwards [ha, hη, hηt, hηx, hηxx] with x hax hηz hηtz hηxz hηxxz
    change ‖r x‖ ≤ K0 * ‖f x‖ + C * ‖u x‖ + B * ‖du x‖
    calc
      ‖r x‖ ≤ ‖η x • f x + fderiv ℝ η x et • u x‖ +
          ‖a x • ((2 * fderiv ℝ η x ex) • du x +
            fderiv ℝ (fun y => fderiv ℝ η y ex) x ex • u x)‖ := norm_sub_le _ _
      _ ≤ ‖η x‖ * ‖f x‖ + ‖fderiv ℝ η x et‖ * ‖u x‖ +
          ‖a x‖ * (2 * ‖fderiv ℝ η x ex‖ * ‖du x‖ +
            ‖fderiv ℝ (fun y => fderiv ℝ η y ex) x ex‖ * ‖u x‖) := by
        have ht := norm_add_le (η x • f x) (fderiv ℝ η x et • u x)
        have hx := norm_add_le ((2 * fderiv ℝ η x ex) • du x)
          (fderiv ℝ (fun y => fderiv ℝ η y ex) x ex • u x)
        simp only [norm_smul, norm_mul, Real.norm_ofNat] at ht hx ⊢
        exact add_le_add ht (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      _ ≤ K0 * ‖f x‖ + Kt * ‖u x‖ +
          A * (2 * Kx * ‖du x‖ + Kxx * ‖u x‖) := by
        gcongr
      _ = _ := by dsimp [C, B]; ring
  calc
    eLpNorm r p μ = eLpNorm r p (μ.restrict Ω) := hrnorm
    _ ≤ eLpNorm ((K0 : ℝ) • F + C • U + B • D) p (μ.restrict Ω) :=
      eLpNorm_mono_ae_real hm
    _ ≤ eLpNorm ((K0 : ℝ) • F + C • U) p (μ.restrict Ω) +
        eLpNorm (B • D) p (μ.restrict Ω) :=
      eLpNorm_add_le ((hf.norm.const_smul (K0 : ℝ)).add (hu.norm.const_smul C))
        (hdu.norm.const_smul B) hp
    _ ≤ (eLpNorm ((K0 : ℝ) • F) p (μ.restrict Ω) +
        eLpNorm (C • U) p (μ.restrict Ω)) + eLpNorm (B • D) p (μ.restrict Ω) :=
      add_le_add (eLpNorm_add_le (hf.norm.const_smul (K0 : ℝ))
        (hu.norm.const_smul C) hp) le_rfl
    _ = _ := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_const_smul,
        Real.enorm_eq_ofReal K0.coe_nonneg, Real.enorm_eq_ofReal hC,
        Real.enorm_eq_ofReal hB]
      simp only [F, U, D, eLpNorm_norm, C, B]
      norm_cast
      simp only [ENNReal.ofReal_coe_nnreal]

end DifferentialGeometry.Analysis.Parabolic
