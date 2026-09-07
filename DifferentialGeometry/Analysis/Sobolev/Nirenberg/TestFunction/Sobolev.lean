import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.StandardNirenbergTest
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem standardNirenbergTest_congr_of_eqOn_cthickening
    (k : Fin d) (h : ℝ) {η u v : E → ℝ}
    (huv : EqOn u v (cthickening |h| (tsupport η))) :
    standardNirenbergTest k h η u = standardNirenbergTest k h η v := by
  by_cases hh : h = 0
  · simp [hh]
  have heq (x : E) : (η x) ^ 2 * diffQuot k h u x =
      (η x) ^ 2 * diffQuot k h v x := by
    by_cases hx : η x = 0
    · simp [hx]
    have hxs : x ∈ tsupport η := subset_tsupport η hx
    have hbase := huv (self_subset_cthickening (tsupport η) hxs)
    have hshift : u (x + h • EuclideanSpace.single k (1 : ℝ)) =
        v (x + h • EuclideanSpace.single k (1 : ℝ)) := huv (closedBall_subset_cthickening hxs |h| (by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]))
    rw [diffQuot_apply_of_ne k hh, diffQuot_apply_of_ne k hh, hbase, hshift]
  unfold standardNirenbergTest
  congr 1
  funext x
  exact heq x

theorem standardNirenbergTest_tsupport_subset_cthickening
    (k : Fin d) (h : ℝ) (η u : E → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆ cthickening |h| (tsupport η) := by
  intro x hx
  rcases standardNirenbergTest_tsupport_subset k h u hx with hx | hx
  · exact self_subset_cthickening (tsupport η) hx
  · change x + (-h) • EuclideanSpace.single k (1 : ℝ) ∈ tsupport η at hx
    apply closedBall_subset_cthickening hx |h|
    rw [mem_closedBall, dist_eq_norm]
    have heq : x - (x + (-h) • EuclideanSpace.single k 1) =
        h • EuclideanSpace.single k 1 := by module
    rw [heq, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]

end DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_sq_cutoff
    {η : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η) :
    MemLp (fun x => (η x)^2) ∞ volume := by
  apply (hη.pow 2).memLp_of_hasCompactSupport
  simpa only [pow_two] using (hηc.mul_right : HasCompactSupport (fun x => η x * η x))

private theorem memLp_cutoff_partial
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (j : Fin d) :
    MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) ∞ volume := by
  have hcCont : Continuous (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcCs : HasCompactSupport
      (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) :=
    (hηc.mul_left).mul_right
  exact hcCont.memLp_of_hasCompactSupport hcCs

private theorem memLp_standardNirenbergTest
    {u η : E → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemLp (standardNirenbergTest k h η u) 2 volume := by
  exact memLp_diffQuot_two k (-h) ((memLp_diffQuot_two k h hu).mul'
    (memLp_sq_cutoff hη hηc))

private theorem memLp_standardNirenbergTest_partial
    {u g η : E → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (h : ℝ) :
    MemLp (diffQuot k (-h)
      (fun x => (η x)^2 * diffQuot k h g x +
        2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)) 2 volume := by
  exact memLp_diffQuot_two k (-h)
    (((memLp_diffQuot_two k h hg).mul' (memLp_sq_cutoff hη.continuous hηc)).add
      ((memLp_diffQuot_two k h hu).mul' (memLp_cutoff_partial hη hηc j)))

theorem memWkp_standardNirenbergTest
    {u η : E → ℝ} (hu : MemWkp 1 2 u univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemWkp 1 2 (standardNirenbergTest k h η u) univ := by
  have huLp : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  apply MemWkp.one_iff_memW1p.mpr
  refine ⟨?_, fun j => ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_standardNirenbergTest huLp hη.continuous hηc k h
  let g := chosenWeakPartial' 2 j u univ
  have hgLp : MemLp g 2 volume := by
    simpa only [Measure.restrict_univ] using chosenWeakPartial'_memLp_of_mem hu.memW1p j
  let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
  have hderivLp : MemLp G 2 volume := memLp_standardNirenbergTest_partial huLp hgLp hη hηc k j h
  refine ⟨G, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using hderivLp
  · exact hasWeakPartialDeriv_standardNirenbergTest k j h hη
      (hu.memLp.locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hu.memW1p j).locallyIntegrable (by norm_num))
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)

theorem memWkp_standardNirenbergTest_of_memWkp_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u η : E → ℝ} (hu : MemWkp 1 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    MemWkp 1 2 (standardNirenbergTest k h η u) univ := by
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  obtain ⟨C, _, hC⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hχ hχc 1
  have hv : MemWkp 1 2 (fun x => χ x * u x) Ω :=
    hu.smul_smooth_bounded 1 (by norm_num) hΩ hχ (fun j hj x _ => hC x j hj)
  have hvs : tsupport (fun x => χ x * u x) ⊆ Ω :=
    (tsupport_smul_subset_left χ u).trans hχs
  have hvu := hv.extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hvs hχc.mul_right
  have heq : standardNirenbergTest k h η u =
      standardNirenbergTest k h η (fun x => χ x * u x) := by
    apply standardNirenbergTest_congr_of_eqOn_cthickening
    intro x hx
    simp only [hχone x (self_subset_cthickening _ hx), one_mul]
  rw [heq]
  exact memWkp_standardNirenbergTest hvu hη hηc k h

end DifferentialGeometry.Analysis.Sobolev.Euclidean
