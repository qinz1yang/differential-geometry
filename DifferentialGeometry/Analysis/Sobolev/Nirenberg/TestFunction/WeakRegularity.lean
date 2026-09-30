import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Basic
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma locallyIntegrable_continuous_mul
    {η f : EuclN → ℝ} (hη : Continuous η)
    (hf_localInt : LocallyIntegrable f (volume : Measure EuclN)) :
    LocallyIntegrable (fun x => η x * f x) (volume : Measure EuclN) := by
  rw [← locallyIntegrableOn_univ] at hf_localInt ⊢
  have hcl : IsLocallyClosed (Set.univ : Set EuclN) :=
    isClosed_univ.isLocallyClosed
  exact LocallyIntegrableOn.continuousOn_mul hf_localInt hη.continuousOn hcl

omit [NeZero d] in
private lemma locallyIntegrable_of_restrict_univ
    {f : EuclN → ℝ}
    (hf : LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ)) :
    LocallyIntegrable f (volume : Measure EuclN) := by
  rwa [Measure.restrict_univ] at hf

omit [NeZero d] in
private lemma locallyIntegrable_to_restrict_univ
    {f : EuclN → ℝ} (hf : LocallyIntegrable f (volume : Measure EuclN)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ) := by
  rwa [Measure.restrict_univ]

omit [NeZero d] in
theorem hasWeakPartialDeriv_nirenbergTestFunction
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_localInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_localInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (diffQuot k (-h)
        (fun y =>
          (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y))
      (nirenbergTestFunction k h η u) Set.univ := by
  have hη_cont : Continuous η := hη.continuous
  have hη_sq_cont : Continuous (fun y : EuclN => (η y)^2) := hη_cont.pow 2
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hpartial_η_cont : Continuous
      (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_2η_partial_cont : Continuous
      (fun y : EuclN => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη_cont).mul hpartial_η_cont
  have hu_localInt' : LocallyIntegrable u (volume : Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hu_localInt
  have hg_j_localInt' : LocallyIntegrable g_j (volume : Measure EuclN) :=
    locallyIntegrable_of_restrict_univ (d := d) hg_j_localInt
  have h_dq_u_localInt : LocallyIntegrable (diffQuot k h u)
      (volume : Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hu_localInt'
  have h_dq_g_localInt : LocallyIntegrable (diffQuot k h g_j)
      (volume : Measure EuclN) :=
    locallyIntegrable_diffQuot (d := d) k h hg_j_localInt'
  have h_F_localInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y) (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_u_localInt
  have h_F_localInt_restrict : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h u y)
      ((volume : Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_F_localInt
  have h_term1_localInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y) (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) hη_sq_cont h_dq_g_localInt
  have h_term2_localInt : LocallyIntegrable
      (fun y => 2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (volume : Measure EuclN) :=
    locallyIntegrable_continuous_mul (d := d) h_2η_partial_cont h_dq_u_localInt
  have h_partial_localInt : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      (volume : Measure EuclN) :=
    h_term1_localInt.add h_term2_localInt
  have h_partial_localInt_restrict : LocallyIntegrable
      (fun y => (η y)^2 * diffQuot k h g_j y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          diffQuot k h u y)
      ((volume : Measure EuclN).restrict Set.univ) :=
    locallyIntegrable_to_restrict_univ (d := d) h_partial_localInt
  have h_inner_wp :
      DeGiorgi.HasWeakPartialDeriv (d := d) j
        (fun y => (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y)
        (fun y => (η y)^2 * diffQuot k h u y) Set.univ :=
    hasWeakPartialDeriv_cutoff_sq_mul_diffQuot (d := d) k j h hη
      hu_localInt hg_j_localInt hwp
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
    rw [fderiv_fun_pow 2 (hη_diff y)]
    rw [smul_apply]
    have h1 : (η y) ^ ((2 : ℕ) - 1) = η y := by norm_num
    rw [h1]
    have h_two : ((2 : ℕ) • η y) = 2 * η y := by
      rw [two_smul]; ring
    rw [h_two, smul_eq_mul]
  rw [h_eq] at h_inner_wp
  unfold nirenbergTestFunction
  exact hasWeakPartialDeriv_diffQuot (d := d) k j (-h)
    h_F_localInt_restrict h_partial_localInt_restrict h_inner_wp

omit [NeZero d] in
private lemma eLpNorm_const_mul
    (c : ℝ) (f : EuclN → ℝ) :
    eLpNorm (fun x => c * f x) 2 (volume : Measure EuclN) =
      ENNReal.ofReal |c| * eLpNorm f 2 (volume : Measure EuclN) := by
  have h_eq : (fun x => c * f x) = c • f := by
    funext x; rw [Pi.smul_apply, smul_eq_mul]
  rw [h_eq]
  rw [eLpNorm_const_smul c f]
  simp [Real.enorm_eq_ofReal_abs]

omit [NeZero d] in
private lemma eLpNorm_translate_eq (k : Fin d) (h : ℝ) (F : EuclN → ℝ) :
    eLpNorm (translate k h F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact measurePreserving_add_right volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq : translate k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show eLpNorm F 2 (volume : Measure EuclN) =
      eLpNorm F 2 (Measure.map τ volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

omit [NeZero d] in
private lemma eLpNorm_diffQuot_neg_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ} :
    eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_eq : diffQuot k (-h) F =
      fun x => (-h)⁻¹ * (translate k (-h) F x - F x) := by
    funext x
    rw [diffQuot_apply_of_ne (d := d) k hnh F x]
    change (F (x + (-h) • EuclideanSpace.single k 1) - F x) / (-h) =
      (-h)⁻¹ * (F (x + (-h) • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq2 : (fun x => (-h)⁻¹ * (translate k (-h) F x - F x)) =
      fun x => (-h)⁻¹ * ((translate k (-h) F - F) x) := by
    funext x; simp [Pi.sub_apply]
  rw [h_eq2, eLpNorm_const_mul (-h)⁻¹ (translate k (-h) F - F)]
  have h_minkowski : eLpNorm (translate k (-h) F - F) 2
      (volume : Measure EuclN) ≤
        eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) +
          eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_τF_eq : eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_translate_eq (d := d) k (-h) F
  rw [h_τF_eq] at h_minkowski
  have h_step : eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN) ≤
      2 * eLpNorm F 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |(-h)⁻¹| = |h|⁻¹ := by
    rw [abs_inv, abs_neg]
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |(-h)⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  rw [h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ * (2 * eLpNorm F 2 (volume : Measure EuclN)) := by
        gcongr
    _ = 2 / ENNReal.ofReal |h| * eLpNorm F 2 (volume : Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

omit [NeZero d] in
private lemma eLpNorm_eta_sq_diffQuot_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η)
    (hf : AEStronglyMeasurable (fun y => (η y) ^ 2 * diffQuot k h u y)
      (volume : Measure EuclN)) :
    eLpNorm (fun y => (η y)^2 * diffQuot k h u y) 2
        (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf ?_ 2
  filter_upwards [] with y
  rw [norm_mul, Real.norm_eq_abs ((η y)^2), abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hbound : |η y| ≤ |M_η| := by
    rw [abs_of_nonneg hM_η_nn]
    exact hM_η y
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (η y)) hbound 2

omit [NeZero d] in
theorem eLpNorm_nirenbergTestFunction_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {η u : EuclN → ℝ}
    (hη_cont : Continuous η)
    (hu_aesm : AEStronglyMeasurable u (volume : Measure EuclN))
    {M_η : ℝ} (hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (nirenbergTestFunction k h η u) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  set F : EuclN → ℝ := fun y => (η y)^2 * diffQuot k h u y with hF_def
  have hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN) := by
    rw [hF_def]
    have h1 : AEStronglyMeasurable (fun y : EuclN => (η y)^2)
        (volume : Measure EuclN) :=
      (hη_cont.pow 2).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
      aestronglyMeasurable_diffQuot (d := d) k h hu_aesm
    exact h1.mul h2
  have h_step_A : eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_diffQuot_neg_le (d := d) (F := F) k hh
  have h_step_B : eLpNorm F 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
    rw [hF_def]
    exact eLpNorm_eta_sq_diffQuot_le (d := d) k h hM_η_nn hM_η hF_aesm
  have h_lhs_unfold : nirenbergTestFunction k h η u = diffQuot k (-h) F := rfl
  rw [h_lhs_unfold]
  calc eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN)
      ≤ (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := h_step_A
    _ ≤ (2 / ENNReal.ofReal |h|) *
          (ENNReal.ofReal (M_η^2) *
            eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN)) := by
          gcongr
    _ = (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
        rw [mul_assoc]

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
