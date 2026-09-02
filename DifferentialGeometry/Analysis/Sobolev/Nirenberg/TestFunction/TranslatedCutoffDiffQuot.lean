import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

noncomputable def translatedCutoffSqDiffQuot
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) : EuclN → ℝ :=
  translate k (-h) (fun x => (η x)^2 * diffQuot k h u x)

omit [NeZero d] in
@[simp] lemma translatedCutoffSqDiffQuot_apply
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) (x : EuclN) :
    translatedCutoffSqDiffQuot k h η u x =
      (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) := rfl

omit [NeZero d] in
lemma translatedCutoffSqDiffQuot_apply_sub
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) (x : EuclN) :
    translatedCutoffSqDiffQuot k h η u x =
      (η (x - h • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x - h • EuclideanSpace.single k 1) := by
  simp [translatedCutoffSqDiffQuot, translate, sub_eq_add_neg, neg_smul]

omit [NeZero d] in
theorem translatedCutoffSqDiffQuot_support_subset
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) :
    Function.support (translatedCutoffSqDiffQuot k h η u) ⊆
      {x | x + (-h) • EuclideanSpace.single k 1 ∈ Function.support η} := by
  intro x hx
  change (η (x + (-h) • EuclideanSpace.single k 1))^2 *
      diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) ≠ 0 at hx
  by_contra hxη
  have hη_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 := by
    by_contra hne
    exact hxη hne
  apply hx
  have hη_sq_zero : (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 := by
    rw [hη_zero]; ring
  rw [hη_sq_zero, zero_mul]

omit [NeZero d] in
theorem translatedCutoffSqDiffQuot_tsupport_subset
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) :
    tsupport (translatedCutoffSqDiffQuot k h η u) ⊆
      {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  have htrans_cont : Continuous
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_closed_pre : IsClosed
      {x : EuclN | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} :=
    isClosed_tsupport η |>.preimage htrans_cont
  refine closure_minimal ?_ h_closed_pre
  intro x hx
  exact subset_tsupport η
    (translatedCutoffSqDiffQuot_support_subset (d := d) k h η u hx)

omit [NeZero d] in
theorem translatedCutoffSqDiffQuot_hasCompactSupport
    (k : Fin d) (h : ℝ) {η : EuclN → ℝ} (hη_cs : HasCompactSupport η)
    (u : EuclN → ℝ) :
    HasCompactSupport (translatedCutoffSqDiffQuot k h η u) := by
  set v : EuclN := (-h) • EuclideanSpace.single k 1 with hv_def
  set htrans_homeo : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight v with htrans_def
  have h_sub : tsupport (translatedCutoffSqDiffQuot k h η u) ⊆
      {x : EuclN | x + v ∈ tsupport η} :=
    translatedCutoffSqDiffQuot_tsupport_subset (d := d) k h η u
  have h_set_eq :
      {x : EuclN | x + v ∈ tsupport η} = htrans_homeo ⁻¹' (tsupport η) := by
    ext x
    simp [htrans_homeo]
  rw [h_set_eq] at h_sub
  have h_pre_eq :
      htrans_homeo ⁻¹' (tsupport η) = htrans_homeo.symm '' (tsupport η) := by
    ext x
    constructor
    · intro hx
      refine ⟨htrans_homeo x, hx, ?_⟩
      exact htrans_homeo.symm_apply_apply x
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : htrans_homeo x = y := by
        rw [← hyx, htrans_homeo.apply_symm_apply]
      rw [Set.mem_preimage, this]
      exact hy
  have h_pre_compact : IsCompact (htrans_homeo ⁻¹' (tsupport η)) := by
    rw [h_pre_eq]
    exact hη_cs.image htrans_homeo.symm.continuous
  exact h_pre_compact.of_isClosed_subset (isClosed_tsupport _) h_sub

omit [NeZero d] in
theorem translatedCutoffSqDiffQuot_sq_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η) (x : EuclN) :
    (translatedCutoffSqDiffQuot k h η u x)^2 ≤
      M_η^4 *
        (diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2 := by
  set y : EuclN := x + (-h) • EuclideanSpace.single k 1 with hy_def
  have h_unfold :
      (translatedCutoffSqDiffQuot k h η u x)^2 =
        ((η y)^2)^2 * (diffQuot k h u y)^2 := by
    rw [translatedCutoffSqDiffQuot_apply]
    ring
  rw [h_unfold]
  have h_sq_le : (η y)^2 ≤ M_η^2 := by
    have hY := hM_η y
    have h_abs_sq : (η y)^2 = |η y|^2 := by rw [sq_abs]
    rw [h_abs_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) hY 2
  have h_quartic_le : ((η y)^2)^2 ≤ M_η^4 := by
    have : ((η y)^2)^2 ≤ (M_η^2)^2 := by
      have h_sq_nn : 0 ≤ (η y)^2 := sq_nonneg _
      exact pow_le_pow_left₀ h_sq_nn h_sq_le 2
    have hM4 : (M_η^2)^2 = M_η^4 := by ring
    rw [← hM4]; exact this
  have h_dq_sq_nn : 0 ≤ (diffQuot k h u y)^2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_right h_quartic_le h_dq_sq_nn

omit [NeZero d] in
theorem aestronglyMeasurable_translatedCutoffSqDiffQuot
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    (hη : AEStronglyMeasurable η (volume : Measure EuclN))
    (hu : AEStronglyMeasurable u (volume : Measure EuclN)) :
    AEStronglyMeasurable (translatedCutoffSqDiffQuot k h η u)
      (volume : Measure EuclN) := by
  have hη_sq : AEStronglyMeasurable (fun y : EuclN => (η y)^2)
      (volume : Measure EuclN) := hη.pow 2
  have hdq : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
    aestronglyMeasurable_diffQuot (d := d) k h hu
  have hg : AEStronglyMeasurable
      (fun y : EuclN => (η y)^2 * diffQuot k h u y)
      (volume : Measure EuclN) := hη_sq.mul hdq
  have hMP : MeasurePreserving
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) volume volume :=
    measurePreserving_add_right volume _
  exact hg.comp_measurePreserving hMP

omit [NeZero d] in
private lemma lintegral_translate_diffQuot_sq
    (k : Fin d) (h : ℝ) (u : EuclN → ℝ) :
    ∫⁻ x : EuclN,
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
          : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure EuclN) =
      ∫⁻ y : EuclN,
        (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
        ∂(volume : Measure EuclN) := by
  have hMP : MeasurePreserving
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) volume volume :=
    measurePreserving_add_right volume _
  set htrans_homeo : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight ((-h) • EuclideanSpace.single k 1) with htrans_def
  have h_emb : MeasurableEmbedding htrans_homeo :=
    htrans_homeo.measurableEmbedding
  have h_fun_eq : (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) =
      htrans_homeo := by
    funext x
    simp [htrans_homeo]
  have hMP' : MeasurePreserving htrans_homeo volume volume := by
    rw [← h_fun_eq]; exact hMP
  have h_step : ∫⁻ x : EuclN,
        (‖diffQuot k h u (htrans_homeo x)‖ₑ : ℝ≥0∞) ^ (2 : ℕ) =
      ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ) :=
    hMP'.lintegral_comp_emb h_emb
      (fun y : EuclN => (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ))
  have h_congr : (fun x : EuclN =>
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞)
          ^ (2 : ℕ)) =
      (fun x : EuclN =>
        (‖diffQuot k h u (htrans_homeo x)‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) := by
    funext x
    have : x + (-h) • EuclideanSpace.single k 1 = htrans_homeo x := by
      simp [htrans_homeo]
    rw [this]
  rw [h_congr]
  exact h_step

omit [NeZero d] in
theorem eLpNorm_translatedCutoffSqDiffQuot_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (translatedCutoffSqDiffQuot k h η u) 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt_enorm : ∀ x : EuclN,
      (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) *
          (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
            : ℝ≥0∞)^(2 : ℕ) := by
    intro x
    have h_real :=
      translatedCutoffSqDiffQuot_sq_le (d := d) (u := u) k h hM_η x
    have h_lhs_eq :
        (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((translatedCutoffSqDiffQuot k h η u x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal
            ((diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM4_nn : 0 ≤ M_η^4 := by positivity
    rw [show ENNReal.ofReal (M_η^4) *
        ENNReal.ofReal
          ((diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) =
      ENNReal.ofReal (M_η^4 *
        (diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) from
        (ENNReal.ofReal_mul hM4_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  rw [h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ x : EuclN,
          (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ x : EuclN,
          (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with x using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  have h_lint_le :
      ∫⁻ x : EuclN, (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ) := by
    have h_step :
        ∫⁻ x : EuclN, (‖translatedCutoffSqDiffQuot k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ) ≤
          ∫⁻ x : EuclN,
            ENNReal.ofReal (M_η^4) *
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) := by
      refine lintegral_mono_ae ?_
      filter_upwards with x using h_pt_enorm x
    have h_const_pull :
        ∫⁻ x : EuclN,
            ENNReal.ofReal (M_η^4) *
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) =
          ENNReal.ofReal (M_η^4) *
            ∫⁻ x : EuclN,
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    rw [h_const_pull] at h_step
    rw [lintegral_translate_diffQuot_sq (d := d) k h u] at h_step
    exact h_step
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have hM4_nn : 0 ≤ M_η^4 := by positivity
  have h_mul_rpow :
      (ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN,
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M_η^4)) ^ ((1 : ℝ) / 2) *
          (∫⁻ y : EuclN,
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_mul_rpow]
  have h_sqrt_M4 :
      (ENNReal.ofReal (M_η^4)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (M_η^2) := by
    have hM2_nn : 0 ≤ M_η^2 := sq_nonneg _
    have h_M4_to_pow :
        ENNReal.ofReal (M_η^4) = (ENNReal.ofReal (M_η^2)) ^ (2 : ℕ) := by
      rw [show M_η^4 = (M_η^2)^(2 : ℕ) from by ring,
        ENNReal.ofReal_pow hM2_nn 2]
    rw [h_M4_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (M_η^2)) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M4]

omit [NeZero d] in
private lemma volume_compact_lt_top {K : Set EuclN} (hK : IsCompact K) :
    (volume : Measure EuclN) K < ∞ := hK.measure_lt_top

omit [NeZero d] in
theorem eLpNorm_translatedCutoffSqDiffQuot_restrict_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η)
    (Ω' : Set EuclN) :
    eLpNorm (translatedCutoffSqDiffQuot k h η u) 2 ((volume : Measure EuclN).restrict Ω') ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  refine le_trans ?_ (eLpNorm_translatedCutoffSqDiffQuot_le (d := d) k h hM_η)
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

omit [NeZero d] in
omit [NeZero d] in
theorem hasWeakPartialDeriv_translatedCutoffSqDiffQuot
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (translate k (-h)
        (fun y => (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y))
      (translatedCutoffSqDiffQuot k h η u) Set.univ := by
  have h_inner_wp :=
    hasWeakPartialDeriv_cutoff_sq_mul_diffQuot (d := d) k j h hη
      hu_locInt hg_j_locInt hwp
  unfold translatedCutoffSqDiffQuot
  exact hasWeakPartialDeriv_translate (d := d) k j (-h) h_inner_wp

omit [NeZero d] in
theorem hasWeakPartialDeriv_translatedCutoffSqDiffQuot_expanded
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (translate k (-h)
        (fun y =>
          (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y))
      (translatedCutoffSqDiffQuot k h η u) Set.univ := by
  have h_general :=
    hasWeakPartialDeriv_translatedCutoffSqDiffQuot (d := d) k j h hη
      hu_locInt hg_j_locInt hwp
  have h_eq :
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y) =
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y) := by
    funext y
    rw [fderiv_cutoff_sq_apply (d := d) hη j y]
  rw [h_eq] at h_general
  exact h_general

end DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
