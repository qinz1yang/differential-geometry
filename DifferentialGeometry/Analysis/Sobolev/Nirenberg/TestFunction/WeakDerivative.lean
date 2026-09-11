import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_cutoff_mul
    {Ω : Set E} (hΩ : IsOpen Ω) {u χ : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω) :
    MemLp (fun x => χ x * u x) 2 volume := by
  have hm : MemLp (fun x => χ x * u x) 2 (volume.restrict Ω) := hu.mul' ((hχ.memLp_of_hasCompactSupport hχc : MemLp χ ∞ volume).restrict Ω)
  have hi := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hm
  have heq : Ω.indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun hs => hx (hχs hs)), zero_mul]
  rwa [heq] at hi

private theorem nirenbergTest_partial_congr
    (k j : Fin d) (h : ℝ) (η : E → ℝ) {u v g G : E → ℝ}
    (huv : EqOn u v (cthickening |h| (tsupport η)))
    (hgG : EqOn g G (cthickening |h| (tsupport η))) :
    (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x) =
    (fun x => (η x)^2 * diffQuot k h G x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h v x) := by
  funext x
  by_cases hx : η x = 0
  · simp [hx]
  by_cases hh : h = 0
  · simp [hh]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hbase : x ∈ cthickening |h| (tsupport η) := self_subset_cthickening _ hxs
  have hshift : x + h • EuclideanSpace.single k (1 : ℝ) ∈ cthickening |h| (tsupport η) := by
    apply closedBall_subset_cthickening hxs |h|
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, huv hbase, huv hshift, hgG hbase, hgG hshift]

theorem hasWeakPartialDeriv_nirenbergTestFunction_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (k j : Fin d) (h : ℝ) (hweak : DeGiorgi.HasWeakPartialDeriv j g u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
    DeGiorgi.HasWeakPartialDeriv j G (nirenbergTestFunction k h η u) univ := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single j 1) * u x
  have hv : MemLp v 2 volume := memLp_cutoff_mul hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : E => EuclideanSpace.single j (1 : ℝ)))
  have hw : MemLp w 2 volume :=
    (memLp_cutoff_mul hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_mul hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hχs))
  have hvu : EqOn v u (cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [v, hχone x (self_subset_cthickening _ hx), one_mul]
  have hwg : EqOn w g (cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [w, hχone x (self_subset_cthickening _ hx), one_mul,
      fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx j, zero_mul, add_zero]
  have htest := nirenbergTestFunction_congr_of_eqOn_cthickening k h hvu
  have hpart := nirenbergTest_partial_congr k j h η hvu hwg
  have hvloc : LocallyIntegrable v (volume.restrict univ) := by
    simpa only [Measure.restrict_univ] using hv.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hwloc : LocallyIntegrable w (volume.restrict univ) := by
    simpa only [Measure.restrict_univ] using hw.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvwp : DeGiorgi.HasWeakPartialDeriv j w v univ :=
    hasWeakPartialDeriv_mul_cutoff_univ hΩ hu hg j hweak hχ hχc hχs
  have hwp := hasWeakPartialDeriv_nirenbergTestFunction k j h hη hvloc hwloc hvwp
  rw [htest, hpart] at hwp
  exact hwp

theorem memLp_nirenbergTestFunction_partial_local
    {Ω : Set E} (hΩ : IsOpen Ω) {u g η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (k j : Fin d) (h : ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    let G := diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h g x +
      2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h u x)
    MemLp G 2 volume := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := |h|)) hΩ hηs
  let v := fun x => χ x * u x
  let w := fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single j 1) * u x
  have hv : MemLp v 2 volume := memLp_cutoff_mul hΩ hu hχ.continuous hχc hχs
  have hDχ := (hχ.continuous_fderiv (by simp)).clm_apply
    (continuous_const : Continuous (fun _ : E => EuclideanSpace.single j (1 : ℝ)))
  have hw : MemLp w 2 volume :=
    (memLp_cutoff_mul hΩ hg hχ.continuous hχc hχs).add
      (memLp_cutoff_mul hΩ hu hDχ (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hχs))
  have hvu : EqOn v u (cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [v, hχone x (self_subset_cthickening _ hx), one_mul]
  have hwg : EqOn w g (cthickening |h| (tsupport η)) := by
    intro x hx
    simp only [w, hχone x (self_subset_cthickening _ hx), one_mul,
      fderiv_cutoff_apply_zero_on_cthickening hδ hχone hx j, zero_mul, add_zero]
  have hpart := nirenbergTest_partial_congr k j h η hvu hwg
  change MemLp (diffQuot k (-h) _) 2 volume
  rw [← hpart]
  have hηsqc : HasCompactSupport (fun x => (η x)^2) :=
    hηc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hηsq : MemLp (fun x => (η x)^2) ∞ volume :=
    (hη.continuous.pow 2).memLp_of_hasCompactSupport hηsqc
  have hηDc : HasCompactSupport
      (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) := (hηc.mul_left).mul_right
  have hηD : MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1)) ∞ volume :=
    ((continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport hηDc
  have hfirst : MemLp (fun x => (η x)^2 * diffQuot k h w x) 2 volume :=
    (memLp_diffQuot_two k h hw).mul' hηsq
  have hsecond : MemLp (fun x => 2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) * diffQuot k h v x)
      2 volume := (memLp_diffQuot_two k h hv).mul' hηD
  exact memLp_diffQuot_two k (-h) (hfirst.add hsecond)

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
