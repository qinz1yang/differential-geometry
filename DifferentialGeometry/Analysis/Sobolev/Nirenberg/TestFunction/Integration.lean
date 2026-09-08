import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_sq_mul_diffQuot
    {η v : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hv : MemLp v 2 volume) (k : Fin d) (h : ℝ) :
    MemLp (fun x => η x ^ 2 * diffQuot k h v x) 2 volume := by
  have hηsq : MemLp (fun x => η x ^ 2) ∞ volume := by
    apply (hη.pow 2).memLp_of_hasCompactSupport
    simpa only [pow_two] using (hηc.mul_right : HasCompactSupport (fun x => η x * η x))
  exact (memLp_diffQuot_two k h hv).mul' hηsq

theorem integral_mul_standardNirenbergTest_eq
    {w v η : E → ℝ} (hw : MemLp w 2 volume) (hv : MemLp v 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, w x * standardNirenbergTest k h η v x) =
      -∫ x, diffQuot k h w x * (η x ^ 2 * diffQuot k h v x) := by
  by_cases hh : h = 0
  · simp [hh, standardNirenbergTest_zero_h]
  have hid := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh hw
    (memLp_sq_mul_diffQuot hη hηc hv k h)
  dsimp only [standardNirenbergTest]
  linarith

theorem integral_weight_mul_standardNirenbergTest_eq
    {a u v η : E → ℝ} (hau : MemLp (fun x => a x * u x) 2 volume)
    (hv : MemLp v 2 volume) (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    (∫ x, a x * u x * standardNirenbergTest k h η v x) =
      -∫ x, (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h v x) := by
  rw [integral_mul_standardNirenbergTest_eq hau hv hη hηc k h]
  simp only [NirenbergEuclidean.diffQuot_mul]

theorem integral_self_standardNirenbergTest_eq_neg_integral_sq
    {u η : E → ℝ} (hu : MemLp u 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, u x * standardNirenbergTest k h η u x) =
      -∫ x, (η x * diffQuot k h u x) ^ 2 := by
  rw [integral_mul_standardNirenbergTest_eq hu hu hη hηc k h]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem integral_mul_standardNirenbergTest_comm
    {u v η : E → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, u x * standardNirenbergTest k h η v x) =
      ∫ x, v x * standardNirenbergTest k h η u x := by
  rw [integral_mul_standardNirenbergTest_eq hu hv hη hηc k h,
    integral_mul_standardNirenbergTest_eq hv hu hη hηc k h]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

private theorem weighted_diffQuot_coercivity_pointwise
    {a u η : E → ℝ} (k : Fin d) (h : ℝ) {lam A : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (x : E)
    (ha : η x ≠ 0 → lam ≤ translate k h a x)
    (hda : η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (η x * diffQuot k h u x)^2 -
        A^2 / (2 * lam) * (η x * u x)^2 ≤
      (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h u x) := by
  by_cases hη : η x = 0
  · simp [hη]
  let r := η x * diffQuot k h u x
  let s := η x * u x
  let b := diffQuot k h a x
  have hsq : b^2 * s^2 ≤ A^2 * s^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hA).mpr (hda hη)
  have hy := DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add
    r (b * s) lam hlam
  have hab : -(abs r * abs (b * s)) ≤ b * s * r := by
    have ht := neg_abs_le (b * s * r)
    simpa only [abs_mul, mul_comm] using ht
  have hab' : 2 * (b * s * r) ≥ -(lam * r^2 + (1 / lam) * (b * s)^2) := by
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_right (ha hη) (sq_nonneg r)
  have hinv := mul_le_mul_of_nonneg_left hsq (le_of_lt (one_div_pos.mpr hlam))
  have heq : A^2 / (2 * lam) = (1 / lam) * A^2 / 2 := by ring
  have htarget : lam / 2 * r^2 - A^2 / (2 * lam) * s^2 ≤
      translate k h a x * r^2 + b * s * r := by
    rw [heq]
    rw [mul_pow] at hab'
    nlinarith
  calc
    _ ≤ translate k h a x * r^2 + b * s * r := htarget
    _ = _ := by dsimp [r, s, b]; ring

theorem neg_integral_weight_mul_standardNirenbergTest_ge
    {a u η : E → ℝ} (hu : MemLp u 2 volume)
    (hau : MemLp (fun x => a x * u x) 2 volume)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (ha : ∀ x, η x ≠ 0 → lam ≤ translate k h a x)
    (hda : ∀ x, η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (∫ x, (η x * diffQuot k h u x)^2) -
        A^2 / (2 * lam) * (∫ x, (η x * u x)^2) ≤
      -(∫ x, a x * u x * standardNirenbergTest k h η u x) := by
  have hηlp : MemLp η ∞ volume := hη.memLp_of_hasCompactSupport hηc
  have hηu : MemLp (fun x => η x * u x) 2 volume := hu.mul' hηlp
  have hηdq : MemLp (fun x => η x * diffQuot k h u x) 2 volume :=
    (memLp_diffQuot_two k h hu).mul' hηlp
  have hηuSq : Integrable (fun x => (η x * u x)^2) volume := by
    exact (hηu.integrable_mul hηu).congr (Filter.Eventually.of_forall fun x => by simp [pow_two])
  have hηdqSq : Integrable (fun x => (η x * diffQuot k h u x)^2) volume := by
    exact (hηdq.integrable_mul hηdq).congr (Filter.Eventually.of_forall fun x => by simp [pow_two])
  have hR : Integrable (fun x =>
      (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h u x)) volume := by
    have ht := (memLp_diffQuot_two k h hau).integrable_mul (memLp_sq_mul_diffQuot hη hηc hu k h)
    exact ht.congr (Filter.Eventually.of_forall fun x => by simp [NirenbergEuclidean.diffQuot_mul])
  rw [integral_weight_mul_standardNirenbergTest_eq hau hu hη hηc k h, neg_neg]
  calc
    _ = ∫ x, (lam / 2 * (η x * diffQuot k h u x)^2 -
      A^2 / (2 * lam) * (η x * u x)^2) := by
      rw [integral_sub (hηdqSq.const_mul _) (hηuSq.const_mul _), integral_const_mul,
        integral_const_mul]
    _ ≤ _ := integral_mono
      ((hηdqSq.const_mul _).sub (hηuSq.const_mul _)) hR
      (fun x => weighted_diffQuot_coercivity_pointwise k h hlam hA x (ha x) (hda x))

private theorem diffQuot_indicator_eq_on_cutoff
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

private theorem standardNirenbergTest_indicator_eq
    {Ω : Set E} {η u : E → ℝ} (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    standardNirenbergTest k h η (Ω.indicator u) = standardNirenbergTest k h η u := by
  apply standardNirenbergTest_congr_of_eqOn_cthickening
  intro x hx
  exact indicator_of_mem (hηs hx) _

theorem integral_mul_standardNirenbergTest_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {w v η : E → ℝ}
    (hw : MemLp w 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, w x * standardNirenbergTest k h η v x) =
      -∫ x, diffQuot k h w x * (η x ^ 2 * diffQuot k h v x) := by
  have hw0 : MemLp (Ω.indicator w) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hw
  have hv0 : MemLp (Ω.indicator v) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hv
  have hid := integral_mul_standardNirenbergTest_eq hw0 hv0 hη hηc k h
  rw [standardNirenbergTest_indicator_eq k h hηs] at hid
  have hleft : (∫ x, Ω.indicator w x * standardNirenbergTest k h η v x) =
      ∫ x in Ω, w x * standardNirenbergTest k h η v x := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [hleft] at hid
  rw [hid]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : η x = 0
  · simp [hx]
  · rw [diffQuot_indicator_eq_on_cutoff k h hηs hx,
      diffQuot_indicator_eq_on_cutoff k h hηs hx]

theorem integral_weight_mul_standardNirenbergTest_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {a u v η : E → ℝ}
    (hau : MemLp (fun x => a x * u x) 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, a x * u x * standardNirenbergTest k h η v x) =
      -∫ x, (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h v x) := by
  rw [integral_mul_standardNirenbergTest_eq_local hΩ hau hv hη hηc k h hηs]
  simp only [NirenbergEuclidean.diffQuot_mul]

theorem integral_self_standardNirenbergTest_eq_neg_integral_sq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, u x * standardNirenbergTest k h η u x) =
      -∫ x, (η x * diffQuot k h u x) ^ 2 := by
  rw [integral_mul_standardNirenbergTest_eq_local hΩ hu hu hη hηc k h hηs]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem integral_mul_standardNirenbergTest_comm_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u v η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, u x * standardNirenbergTest k h η v x) =
      ∫ x in Ω, v x * standardNirenbergTest k h η u x := by
  rw [integral_mul_standardNirenbergTest_eq_local hΩ hu hv hη hηc k h hηs,
    integral_mul_standardNirenbergTest_eq_local hΩ hv hu hη hηc k h hηs]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem neg_integral_weight_mul_standardNirenbergTest_ge_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {a u η : E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hau : MemLp (fun x => a x * u x) 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : cthickening |h| (tsupport η) ⊆ Ω)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (ha : ∀ x, η x ≠ 0 → lam ≤ translate k h a x)
    (hda : ∀ x, η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (∫ x, (η x * diffQuot k h u x)^2) -
        A^2 / (2 * lam) * (∫ x, (η x * u x)^2) ≤
      -(∫ x in Ω, a x * u x * standardNirenbergTest k h η u x) := by
  have hu0 : MemLp (Ω.indicator u) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hu
  have hau0 : MemLp (fun x => a x * Ω.indicator u x) 2 volume := by
    have ht : MemLp (Ω.indicator (fun x => a x * u x)) 2 volume :=
      (memLp_indicator_iff_restrict hΩ).mpr hau
    apply ht.ae_eq
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have ht := neg_integral_weight_mul_standardNirenbergTest_ge hu0 hau0 hη hηc k h hlam hA ha hda
  have hDq : (fun x => (η x * diffQuot k h (Ω.indicator u) x)^2) =
      fun x => (η x * diffQuot k h u x)^2 := by
    funext x
    by_cases hx : η x = 0
    · simp [hx]
    · rw [diffQuot_indicator_eq_on_cutoff k h hηs hx]
  have hU : (fun x => (η x * Ω.indicator u x)^2) = fun x => (η x * u x)^2 := by
    funext x
    by_cases hx : η x = 0
    · simp [hx]
    · have hbase : x ∈ Ω := hηs (self_subset_cthickening _ (subset_tsupport η hx))
      rw [indicator_of_mem hbase]
  rw [hDq, hU, standardNirenbergTest_indicator_eq k h hηs] at ht
  have hleft : (∫ x, a x * Ω.indicator u x * standardNirenbergTest k h η u x) =
      ∫ x in Ω, a x * u x * standardNirenbergTest k h η u x := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rwa [hleft] at ht

end DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
