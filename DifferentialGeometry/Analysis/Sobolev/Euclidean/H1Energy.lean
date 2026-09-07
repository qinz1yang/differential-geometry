import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import Mathlib.MeasureTheory.Function.L2Space


noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem integral_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp [hx]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = (eLpNorm f 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]

theorem integral_smooth_h1_energy_le_wkpNorm_sq
    {d : ℕ} {Ω K : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfW : MemWkp 1 2 f Ω) :
    (∫ x in K, f x ^ 2 +
      ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) ≤
        (iteratedWeakSobolevNorm 1 2 f Ω).toReal ^ 2 := by
  classical
  have hf1 := MemWkp.one_iff_memW1p.mp hfW
  let D := fun i : Fin d => fun x => fderiv ℝ f x (EuclideanSpace.single i 1)
  have hD : ∀ i, MemLp (D i) 2 (volume.restrict Ω) := fun i =>
    (chosenWeakPartial'_memLp_of_mem hf1 i).ae_eq
      (chosenWeakPartial_smooth_ae_eq (by norm_num) hΩ hf hf1 i)
  have hDf : ∀ i, eLpNorm (D i) 2 (volume.restrict Ω) =
      eLpNorm (chosenWeakPartial' 2 i f Ω) 2 (volume.restrict Ω) := fun i =>
    (eLpNorm_congr_ae
      (chosenWeakPartial_smooth_ae_eq (by norm_num) hΩ hf hf1 i)).symm
  have hW : (iteratedWeakSobolevNorm 1 2 f Ω).toReal =
      (eLpNorm f 2 (volume.restrict Ω)).toReal +
        ∑ i, (eLpNorm (D i) 2 (volume.restrict Ω)).toReal := by
    rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0 2 Ω f]
    simp only [wkpNorm_zero, ← hDf]
    rw [ENNReal.toReal_add hf1.1.2.ne (ENNReal.sum_ne_top.mpr fun i _ => (hD i).2.ne),
      ENNReal.toReal_sum]
    exact fun i _ => (hD i).2.ne
  have hI : Integrable (fun x => f x ^ 2 + ∑ i, D i x ^ 2) (volume.restrict Ω) :=
    hf1.1.integrable_sq.add (integrable_finsetSum _ fun i _ => (hD i).integrable_sq)
  have hmono := integral_mono_measure (Measure.restrict_mono_set volume hKΩ)
    (Filter.Eventually.of_forall fun x =>
      add_nonneg (sq_nonneg (f x)) (Finset.sum_nonneg fun i _ => sq_nonneg (D i x))) hI
  refine hmono.trans ?_
  rw [integral_add hf1.1.integrable_sq (integrable_finsetSum _ fun i _ => (hD i).integrable_sq),
    integral_finsetSum _ fun i _ => (hD i).integrable_sq, integral_sq_eq_eLpNorm_sq hf1.1]
  simp only [integral_sq_eq_eLpNorm_sq (hD _)]
  rw [hW]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i _ => ENNReal.toReal_nonneg
      (a := eLpNorm (D i) 2 (volume.restrict Ω)))
  have hf0 : 0 ≤ (eLpNorm f 2 (volume.restrict Ω)).toReal := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ ∑ i, (eLpNorm (D i) 2 (volume.restrict Ω)).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  nlinarith

theorem integral_smooth_h1_energy_le_wkpNorm_sq_of_tsupport_subset
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (K : Set (EuclideanSpace ℝ (Fin d))) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) :
    (∫ x in K, f x ^ 2 +
      ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) ≤
        (iteratedWeakSobolevNorm 1 2 f Ω).toReal ^ 2 := by
  have hfW := MemWkp_of_smooth_compactSupport hΩ hf hfc hfs (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1
  have hfu := hfW.extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hfs hfc
  have h := integral_smooth_h1_energy_le_wkpNorm_sq isOpen_univ (subset_univ K) hf hfu
  rwa [wkpNorm_extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hfW hfs hfc] at h

end DifferentialGeometry.Analysis.Sobolev.Euclidean
