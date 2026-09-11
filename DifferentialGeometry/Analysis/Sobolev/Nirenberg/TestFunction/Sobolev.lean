import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem nirenbergTestFunction_congr_of_eqOn_cthickening
    (k : Fin d) (h : ℝ) {η u v : E → ℝ}
    (huv : EqOn u v (cthickening |h| (tsupport η))) :
    nirenbergTestFunction k h η u = nirenbergTestFunction k h η v := by
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
  unfold nirenbergTestFunction
  congr 1
  funext x
  exact heq x

theorem nirenbergTestFunction_tsupport_subset_cthickening
    (k : Fin d) (h : ℝ) (η u : E → ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆ cthickening |h| (tsupport η) := by
  intro x hx
  rcases nirenbergTestFunction_tsupport_subset k h u hx with hx | hx
  · exact self_subset_cthickening (tsupport η) hx
  · change x + (-h) • EuclideanSpace.single k (1 : ℝ) ∈ tsupport η at hx
    apply closedBall_subset_cthickening hx |h|
    rw [mem_closedBall, dist_eq_norm]
    have heq : x - (x + (-h) • EuclideanSpace.single k 1) =
        h • EuclideanSpace.single k 1 := by module
    rw [heq, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
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

private theorem memLp_nirenbergTestFunction
    {u η : E → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemLp (nirenbergTestFunction k h η u) 2 volume := by
  exact memLp_diffQuot_two k (-h) ((memLp_diffQuot_two k h hu).mul'
    (memLp_sq_cutoff hη hηc))

private theorem memLp_nirenbergTestFunction_partial
    {u g η : E → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin d) (h : ℝ) :
    MemLp (diffQuot k (-h)
      (fun x => (η x)^2 * diffQuot k h g x +
        2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)) 2 volume := by
  exact memLp_diffQuot_two k (-h)
    (((memLp_diffQuot_two k h hg).mul' (memLp_sq_cutoff hη.continuous hηc)).add
      ((memLp_diffQuot_two k h hu).mul' (memLp_cutoff_partial hη hηc j)))

theorem memWkp_nirenbergTestFunction
    {u η : E → ℝ} (hu : MemWkp 1 2 u univ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemWkp 1 2 (nirenbergTestFunction k h η u) univ := by
  have huLp : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  apply MemWkp.one_iff_memW1p.mpr
  refine ⟨?_, fun j => ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_nirenbergTestFunction huLp hη.continuous hηc k h
  let g := chosenWeakPartialOrZero 2 j u univ
  have hgLp : MemLp g 2 volume := by
    simpa only [Measure.restrict_univ] using chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j
  let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
  have hderivLp : MemLp G 2 volume := memLp_nirenbergTestFunction_partial huLp hgLp hη hηc k j h
  refine ⟨G, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using hderivLp
  · exact hasWeakPartialDeriv_nirenbergTestFunction k j h hη
      (hu.memLp.locallyIntegrable (by norm_num))
      ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p j).locallyIntegrable (by norm_num))
      (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p j)

theorem memWkp_nirenbergTestFunction_of_memWkp_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u η : E → ℝ} (hu : MemWkp 1 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    MemWkp 1 2 (nirenbergTestFunction k h η u) univ := by
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  obtain ⟨C, _, hC⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hχ hχc 1
  have hv : MemWkp 1 2 (fun x => χ x * u x) Ω :=
    hu.smul_smooth_bounded 1 (by norm_num) hΩ hχ (fun j hj x _ => hC x j hj)
  have hvs : tsupport (fun x => χ x * u x) ⊆ Ω :=
    (tsupport_smul_subset_left χ u).trans hχs
  have hvu := hv.extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hvs hχc.mul_right
  have heq : nirenbergTestFunction k h η u =
      nirenbergTestFunction k h η (fun x => χ x * u x) := by
    apply nirenbergTestFunction_congr_of_eqOn_cthickening
    intro x hx
    simp only [hχone x (self_subset_cthickening _ hx), one_mul]
  rw [heq]
  exact memWkp_nirenbergTestFunction hvu hη hηc k h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem diffQuot_indicator_eq_on_support
    {Ω : Set E} {η u : E → ℝ} (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) {x : E} (hx : η x ≠ 0) :
    diffQuot k h (Ω.indicator u) x = diffQuot k h u x := by
  by_cases hh : h = 0
  · simp [hh]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hbase : x ∈ Ω := hηs (self_subset_cthickening _ hxs)
  have hshift : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hηs
    apply closedBall_subset_cthickening hxs |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, indicator_of_mem hbase, indicator_of_mem hshift]

theorem memLp_cutoff_mul_diffQuot_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {η u : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    MemLp (fun x => η x * diffQuot k h u x) 2 volume := by
  have hu0 : MemLp (Ω.indicator u) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hu
  have h : MemLp (fun x => η x * diffQuot k h (Ω.indicator u) x) 2 volume := (memLp_diffQuot_two k h hu0).mul' (hη.memLp_of_hasCompactSupport hηc (p := ∞))
  apply h.ae_eq
  filter_upwards with x
  by_cases hx : η x = 0
  · simp [hx]
  · rw [diffQuot_indicator_eq_on_support k _ hηs hx]


end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
