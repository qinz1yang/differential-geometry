import DifferentialGeometry.Analysis.Sobolev.Tools.DiffQuotLocal
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem eLpNorm_translate_two_eq (k : Fin d) (h : ℝ) (u : E → ℝ) :
    eLpNorm (translate k h u) 2 volume = eLpNorm u 2 volume := by
  let τ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have hMP : MeasurePreserving τ volume volume := by
    change MeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1) volume volume
    exact measurePreserving_add_right volume _
  change eLpNorm (u ∘ τ) 2 volume = eLpNorm u 2 volume
  calc
    eLpNorm (u ∘ τ) 2 volume = eLpNorm u 2 (Measure.map τ volume) :=
      (τ.measurableEmbedding.eLpNorm_map_measure (g := u) (p := 2)).symm
    _ = eLpNorm u 2 volume := by rw [hMP.map_eq]

private theorem eLpNorm_diffQuot_le_inv
    (k : Fin d) (h : ℝ) {u : E → ℝ} (hu : AEStronglyMeasurable u volume) :
    eLpNorm (diffQuot k h u) 2 volume ≤
      ENNReal.ofReal (2 * |h⁻¹|) * eLpNorm u 2 volume := by
  by_cases hh : h = 0
  · simp [hh]
  have heq : diffQuot k h u = h⁻¹ • (translate k h u - u) := by
    funext x
    simp only [diffQuot_apply_of_ne k hh, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      translate, div_eq_mul_inv, mul_comm]
  have hMP : MeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1)
      volume volume := measurePreserving_add_right volume _
  have ht : AEStronglyMeasurable (translate k h u) volume :=
    hu.comp_measurePreserving hMP
  have hnorm := eLpNorm_translate_two_eq k h u
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  calc
    ENNReal.ofReal |h⁻¹| * eLpNorm (translate k h u - u) 2 volume ≤
        ENNReal.ofReal |h⁻¹| * (eLpNorm u 2 volume + eLpNorm u 2 volume) :=
      mul_le_mul' le_rfl (by simpa only [hnorm] using eLpNorm_sub_le ht hu (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = ENNReal.ofReal (2 * |h⁻¹|) * eLpNorm u 2 volume := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← two_mul]
      ring

theorem memWkp_diffQuot_one_two
    {u : E → ℝ} (hu : MemWkp 1 2 u univ) (k : Fin d) (h : ℝ) :
    MemWkp 1 2 (diffQuot k h u) univ := by
  have huLp : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  apply MemWkp.one_iff_memW1p.mpr
  refine ⟨?_, fun j => ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h huLp
  let g := chosenWeakPartial' 2 j u univ
  have hgLp : MemLp g 2 volume := by
    simpa only [Measure.restrict_univ] using chosenWeakPartial'_memLp_of_mem hu.memW1p j
  refine ⟨diffQuot k h g, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h hgLp
  · exact hasWeakPartialDeriv_diffQuot k j h
      (hu.memLp.locallyIntegrable (by norm_num))
      ((chosenWeakPartial'_memLp_of_mem hu.memW1p j).locallyIntegrable (by norm_num))
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)

theorem chosenWeakPartial'_diffQuot_ae
    {u : E → ℝ} (hu : MemWkp 1 2 u univ) (k j : Fin d) (h : ℝ) :
    chosenWeakPartial' 2 j (diffQuot k h u) univ =ᵐ[volume]
      diffQuot k h (chosenWeakPartial' 2 j u univ) := by
  have hq := memWkp_diffQuot_one_two hu k h
  have hg := chosenWeakPartial'_memLp_of_mem hu.memW1p j
  have hgLp : MemLp (chosenWeakPartial' 2 j u univ) 2 volume := by
    simpa only [Measure.restrict_univ] using hg
  have hqg : MemLp (diffQuot k h (chosenWeakPartial' 2 j u univ)) 2
      (volume.restrict univ) := by
    simpa only [Measure.restrict_univ] using memLp_diffQuot_two k h hgLp
  have heq := DeGiorgi.HasWeakPartialDeriv.ae_eq isOpen_univ
    (chosenWeakPartial'_isWeakPartial_of_mem hq.memW1p j)
    (hasWeakPartialDeriv_diffQuot k j h
      (hu.memLp.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j))
    ((chosenWeakPartial'_memLp_of_mem hq.memW1p j).locallyIntegrable (by norm_num))
    (hqg.locallyIntegrable (by norm_num))
  simpa only [Measure.restrict_univ] using heq

theorem wkpNorm_diffQuot_one_two_le
    {u : E → ℝ} (hu : MemWkp 1 2 u univ) (k : Fin d) (h : ℝ) :
    iteratedWeakSobolevNorm 1 2 (diffQuot k h u) univ ≤
      ENNReal.ofReal (2 * |h⁻¹|) * iteratedWeakSobolevNorm 1 2 u univ := by
  classical
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0, wkpNorm_succ_eq_eLpNorm_add_sum_partial 0]
  simp only [wkpNorm_zero, Measure.restrict_univ, mul_add, Finset.mul_sum]
  apply add_le_add
  · apply eLpNorm_diffQuot_le_inv
    simpa only [Measure.restrict_univ] using hu.memLp.aestronglyMeasurable
  · apply Finset.sum_le_sum
    intro j _
    rw [eLpNorm_congr_ae (chosenWeakPartial'_diffQuot_ae hu k j h)]
    apply eLpNorm_diffQuot_le_inv
    simpa only [Measure.restrict_univ] using
      (chosenWeakPartial'_memLp_of_mem hu.memW1p j).aestronglyMeasurable

theorem exists_wkpNorm_standardNirenbergTest_le
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d) (h : ℝ) {u : E → ℝ}, MemWkp 1 2 u univ →
      iteratedWeakSobolevNorm 1 2 (standardNirenbergTest k h η u) univ ≤
        ENNReal.ofReal (C * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u univ := by
  have hηsq : ContDiff ℝ (⊤ : ℕ∞) (fun x => (η x) ^ 2) := hη.pow 2
  have hηsqc : HasCompactSupport (fun x => (η x) ^ 2) := by
    exact hηc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  obtain ⟨B, hB, hBd⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hηsq hηsqc 1
  obtain ⟨K, hK, hKb⟩ := wkpNorm_smul_smooth_bounded_le_one 1 le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
    isOpen_univ hηsq hB (fun j hj x _ => hBd x j hj)
  refine ⟨4 * K, by positivity, ?_⟩
  intro k h u hu
  have hq := memWkp_diffQuot_one_two hu k h
  have hmul : MemWkp 1 2 (fun x => (η x)^2 * diffQuot k h u x) univ :=
    hq.smul_smooth_bounded 1 (by norm_num) isOpen_univ hηsq
      (fun j hj x _ => hBd x j hj)
  unfold standardNirenbergTest
  calc
    iteratedWeakSobolevNorm 1 2
        (diffQuot k (-h) (fun x => (η x)^2 * diffQuot k h u x)) univ ≤
        ENNReal.ofReal (2 * |(-h)⁻¹|) * iteratedWeakSobolevNorm 1 2
          (fun x => (η x)^2 * diffQuot k h u x) univ :=
      wkpNorm_diffQuot_one_two_le hmul k (-h)
    _ ≤ ENNReal.ofReal (2 * |(-h)⁻¹|) * (ENNReal.ofReal K *
        (ENNReal.ofReal (2 * |h⁻¹|) * iteratedWeakSobolevNorm 1 2 u univ)) :=
      mul_le_mul' le_rfl ((hKb hq).trans (mul_le_mul' le_rfl
        (wkpNorm_diffQuot_one_two_le hu k h)))
    _ = ENNReal.ofReal ((4 * K) * |h⁻¹| ^ 2) *
        iteratedWeakSobolevNorm 1 2 u univ := by
      rw [inv_neg, abs_neg]
      have hfactor : ENNReal.ofReal ((2 * |h⁻¹|) * K * (2 * |h⁻¹|)) =
          ENNReal.ofReal (2 * |h⁻¹|) * ENNReal.ofReal K * ENNReal.ofReal (2 * |h⁻¹|) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) hK.le),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * |h⁻¹|)]
      rw [show (4 * K) * |h⁻¹| ^ 2 = (2 * |h⁻¹|) * K * (2 * |h⁻¹|) by ring, hfactor]
      simp only [mul_assoc]

theorem exists_wkpNorm_standardNirenbergTest_le_local
    {Ω : Set E} (hΩ : IsOpen Ω) {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {r : ℝ} (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ r →
      ∀ {u : E → ℝ}, MemWkp 1 2 u Ω →
      iteratedWeakSobolevNorm 1 2 (standardNirenbergTest k h η u) univ ≤
        ENNReal.ofReal (C * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u Ω := by
  obtain ⟨δ, χ, _, _, hχ, hχc, _, hχone, hχs⟩ :=
    exists_smooth_cutoff_with_neighborhood (hηc.cthickening (r := r)) hΩ hηs
  obtain ⟨B, hB, hBd⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hχ hχc 1
  obtain ⟨K, hK, hKb⟩ := wkpNorm_smul_smooth_bounded_le_one 1 le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
    hΩ hχ hB (fun j hj x _ => hBd x j hj)
  obtain ⟨L, hL, hLb⟩ := exists_wkpNorm_standardNirenbergTest_le hη hηc
  refine ⟨L * K, mul_nonneg hL hK.le, ?_⟩
  intro k h hh u hu
  have hv : MemWkp 1 2 (fun x => χ x * u x) Ω :=
    hu.smul_smooth_bounded 1 (by norm_num) hΩ hχ (fun j hj x _ => hBd x j hj)
  have hvs : tsupport (fun x => χ x * u x) ⊆ Ω :=
    (tsupport_smul_subset_left χ u).trans hχs
  have hvc : HasCompactSupport (fun x => χ x * u x) := hχc.mul_right
  have hvu := hv.extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hvs hvc
  have heq : standardNirenbergTest k h η u =
      standardNirenbergTest k h η (fun x => χ x * u x) := by
    apply standardNirenbergTest_congr_of_eqOn_cthickening
    intro x hx
    have hxr := Metric.cthickening_mono hh (tsupport η) hx
    simp only [hχone x (Metric.self_subset_cthickening _ hxr), one_mul]
  rw [heq]
  calc
    iteratedWeakSobolevNorm 1 2 (standardNirenbergTest k h η (fun x => χ x * u x)) univ ≤
        ENNReal.ofReal (L * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 (fun x => χ x * u x) univ :=
      hLb k h hvu
    _ = ENNReal.ofReal (L * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 (fun x => χ x * u x) Ω := by
      rw [wkpNorm_extend_zero (by norm_num) hΩ isOpen_univ (subset_univ _) hv hvs hvc]
    _ ≤ ENNReal.ofReal (L * |h⁻¹| ^ 2) * (ENNReal.ofReal K * iteratedWeakSobolevNorm 1 2 u Ω) :=
      mul_le_mul' le_rfl (hKb hu)
    _ = ENNReal.ofReal ((L * K) * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 u Ω := by
      rw [show (L * K) * |h⁻¹| ^ 2 = (L * |h⁻¹| ^ 2) * K by ring,
        ENNReal.ofReal_mul (mul_nonneg hL (sq_nonneg _))]
      simp only [mul_assoc]

end DifferentialGeometry.Analysis.Sobolev.Euclidean


namespace DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem diffQuot_congr_ae (k : Fin d) (h : ℝ) {u v : E → ℝ}
    (huv : u =ᵐ[volume] v) : diffQuot k h u =ᵐ[volume] diffQuot k h v := by
  have hs : (fun x : E => u (x + h • EuclideanSpace.single k 1)) =ᵐ[volume]
      (fun x : E => v (x + h • EuclideanSpace.single k 1)) :=
    (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae_eq huv
  filter_upwards [huv, hs] with x hx hsx
  simp only [diffQuot, hx, hsx]

theorem standardNirenbergTest_congr_ae (k : Fin d) (h : ℝ) (η : E → ℝ) {u v : E → ℝ}
    (huv : u =ᵐ[volume] v) :
    standardNirenbergTest k h η u =ᵐ[volume] standardNirenbergTest k h η v := by
  apply diffQuot_congr_ae
  filter_upwards [diffQuot_congr_ae k h huv] with x hx
  rw [hx]

theorem standardNirenbergTest_congr_ae_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) (k : Fin d) (h : ℝ) (η : E → ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v) :
    standardNirenbergTest k h η u =ᵐ[volume] standardNirenbergTest k h η v := by
  classical
  have hind : Ω.indicator u =ᵐ[volume] Ω.indicator v := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hΩ] at huv
    filter_upwards [huv] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [indicator_of_mem hxΩ, hx hxΩ]
    · simp only [indicator_of_notMem hxΩ]
  have heq (w : E → ℝ) : standardNirenbergTest k h η w =
      standardNirenbergTest k h η (Ω.indicator w) := by
    apply standardNirenbergTest_congr_of_eqOn_cthickening
    intro x hx
    simp only [indicator_of_mem (hηs hx)]
  rw [heq u, heq v]
  exact standardNirenbergTest_congr_ae k h η hind

theorem standardNirenbergTest_add (k : Fin d) (h : ℝ) (η u v : E → ℝ) :
    standardNirenbergTest k h η (u + v) =
      standardNirenbergTest k h η u + standardNirenbergTest k h η v := by
  unfold standardNirenbergTest
  rw [diffQuot_add]
  have heq : (fun x => (η x)^2 * (diffQuot k h u + diffQuot k h v) x) =
      (fun x => (η x)^2 * diffQuot k h u x) +
        (fun x => (η x)^2 * diffQuot k h v x) := by
    funext x
    simp only [Pi.add_apply, mul_add]
  rw [heq, diffQuot_add]

theorem standardNirenbergTest_smul (k : Fin d) (h c : ℝ) (η u : E → ℝ) :
    standardNirenbergTest k h η (c • u) = c • standardNirenbergTest k h η u := by
  unfold standardNirenbergTest
  rw [diffQuot_smul]
  have heq : (fun x => (η x)^2 * (c • diffQuot k h u) x) =
      c • (fun x => (η x)^2 * diffQuot k h u x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, diffQuot_smul]

end DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest

open Metric

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq
    {Ω Ω' Ω'' : Set E} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {u g η : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω'')
    {A : ℝ} (hA : 0 ≤ A) (hηbound : ∀ x, |η x| ≤ A)
    (k : Fin d) (hweak : DeGiorgi.HasWeakPartialDeriv k g u Ω)
    {r : ℝ} (hr : 0 < r) (hroom : cthickening r (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : |h| ≤ r) :
    (∫ x, η x ^ 2 * (diffQuot k h u x) ^ 2) ≤
      A ^ 2 * (eLpNorm g 2 (volume.restrict Ω')).toReal ^ 2 := by
  have hηroom : cthickening |h| (tsupport η) ⊆ Ω :=
    (cthickening_mono hh _).trans ((cthickening_subset_of_subset r
      (hηs.trans subset_closure)).trans (hroom.trans (subset_closure.trans hΩ'Ω)))
  have hηq := memLp_cutoff_mul_diffQuot_local hΩ.measurableSet hu hη hηc k h hηroom
  have hdq := eLpNorm_diffQuot_le_eLpNorm_weakPartial_local hΩ hΩ' hΩ'' hΩ'c hΩ'Ω
    hΩ''c hu hg k hweak hr hroom hh
  have hnorm : eLpNorm (fun x => η x * diffQuot k h u x) 2 volume ≤
      ENNReal.ofReal A * eLpNorm g 2 (volume.restrict Ω') := by
    calc
      _ ≤ eLpNorm (fun x => A * Ω''.indicator (diffQuot k h u) x) 2 volume := by
        apply eLpNorm_mono_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Ω''
        · simp only [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg hA]
          exact mul_le_mul_of_nonneg_right (hηbound x) (abs_nonneg _)
        · have hzero : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hηs ht))
          simp only [hzero, zero_mul, norm_zero, norm_nonneg]
      _ = ENNReal.ofReal A * eLpNorm (diffQuot k h u) 2 (volume.restrict Ω'') := by
        change eLpNorm (A • Ω''.indicator (diffQuot k h u)) 2 volume = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hA,
          eLpNorm_indicator_eq_eLpNorm_restrict hΩ''.measurableSet]
      _ ≤ _ := mul_le_mul' le_rfl hdq
  have hg' : MemLp g 2 (volume.restrict Ω') :=
    hg.mono_measure (Measure.restrict_mono (subset_closure.trans hΩ'Ω) le_rfl)
  have hnormReal : (eLpNorm (fun x => η x * diffQuot k h u x) 2 volume).toReal ≤
      A * (eLpNorm g 2 (volume.restrict Ω')).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg'.eLpNorm_ne_top) hnorm
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] using h
  have hid : (∫ x, η x ^ 2 * (diffQuot k h u x) ^ 2) =
      (eLpNorm (fun x => η x * diffQuot k h u x) 2 volume).toReal ^ 2 := by
    let v := hηq.toLp (fun x => η x * diffQuot k h u x)
    rw [← Lp.norm_toLp _ hηq, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hηq.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [hid, ← mul_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hnormReal 2

end DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
