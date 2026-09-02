import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open Filter Function Set intervalIntegral
open scoped ENNReal Topology InnerProductSpace
open MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

noncomputable section

private theorem intervalIntegral_absolutelyContinuousOnInterval
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ → X} {a b c : ℝ} (h : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have ht : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        _ _)
  have ht' := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp ht
  refine squeeze_zero' ?_ ?_ ht'
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [comp_apply, s]
  have hdisj : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ))
      in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hdisj] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
        (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
          (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm, norm_neg]
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc
  · intro i hi
    unfold IntegrableOn
    have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
      (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set h.def'.norm hsubset |>.integrable

private theorem absolutelyContinuousOnInterval_norm_sq
    {X : Type*} [SeminormedAddCommGroup X] {f : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ‖f t‖ ^ 2) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hC0 : 0 ≤ C := (norm_nonneg (f a)).trans (hC a left_mem_uIcc)
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  let g : (ℕ × (ℕ → ℝ × ℝ)) → ℝ := fun E ↦
    (2 * C) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
  refine squeeze_zero' (g := g) ?_ ?_ ?_
  · filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  · have hdisj : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
        E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
      eventually_inf_principal.mpr (by simp)
    filter_upwards [hdisj] with (n, I) hnI
    refine (Finset.sum_le_sum fun i hi ↦ ?_).trans_eq (Finset.mul_sum _ _ _).symm
    rw [Real.dist_eq]
    have hx := hC (I i).1 ((hnI.left i hi).1)
    have hy := hC (I i).2 ((hnI.left i hi).2)
    calc
      |‖f (I i).1‖ ^ 2 - ‖f (I i).2‖ ^ 2| =
          |‖f (I i).1‖ - ‖f (I i).2‖| *
            (‖f (I i).1‖ + ‖f (I i).2‖) := by
              rw [sq_sub_sq, abs_mul,
                abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
              exact mul_comm _ _
      _ ≤ dist (f (I i).1) (f (I i).2) * (2 * C) := by
        rw [dist_eq_norm]
        gcongr
        · exact abs_norm_sub_norm_le _ _
        · linarith
      _ = (2 * C) * dist (f (I i).1) (f (I i).2) := mul_comm _ _
  · simpa using
      ((tendsto_const_nhds : Tendsto
          (fun _ : ℕ × (ℕ → ℝ × ℝ) ↦ 2 * C)
          (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
            𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 (2 * C))).mul hf : Tendsto
        (fun E ↦ (2 * C) * ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 ((2 * C) * 0)))

namespace timeH1

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
variable {T : ℝ}

section Normed

variable [NormedSpace ℝ X]

omit [CompleteSpace X] in
theorem absolutelyContinuousOnInterval_toFun (u : timeH1 X T) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval u.toFun 0 T := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hprim : AbsolutelyContinuousOnInterval
      (fun t ↦ ∫ s in (0 : ℝ)..t, u.deriv s) 0 T :=
    intervalIntegral_absolutelyContinuousOnInterval
      (u.intervalIntegrable_deriv h0 hTmem) left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ u.init) 0 T :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  change AbsolutelyContinuousOnInterval
    (fun t ↦ u.init + ∫ s in (0 : ℝ)..t, u.deriv s) 0 T
  exact hconst.add hprim

end Normed

section Hilbert

variable [InnerProductSpace ℝ X]

theorem norm_sq_sub_norm_sq_eq_two_intervalIntegral
    (u : timeH1 X T) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ‖u.toFun b‖ ^ 2 - ‖u.toFun a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (u.toFun t) (u.deriv t) := by
  have hT : 0 ≤ T := ha.1.trans ha.2
  have hu : AbsolutelyContinuousOnInterval u.toFun a b :=
    (u.absolutelyContinuousOnInterval_toFun hT).mono (by
      simpa only [uIcc_of_le hT] using uIcc_subset_Icc ha hb)
  have hsq := AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (absolutelyContinuousOnInterval_norm_sq hu)
  have hderiv : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      _root_.deriv (fun s ↦ ‖u.toFun s‖ ^ 2) t =
        2 * inner ℝ (u.toFun t) (u.deriv t) := by
    have hae : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) T →
        HasDerivWithinAt u.toFun (u.deriv t) (Icc (0 : ℝ) T) t := by
      rw [← ae_restrict_iff' measurableSet_Icc]
      simpa only [timeMeasure] using u.ae_hasDerivWithinAt_toFun
    have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ (0 : ℝ) :=
      Measure.ae_ne volume 0
    have hneT : ∀ᵐ t : ℝ ∂volume, t ≠ T :=
      Measure.ae_ne volume T
    filter_upwards [hae, hne0, hneT] with t ht htne0 htneT htab
    have htIcc : t ∈ Icc (0 : ℝ) T :=
      uIcc_subset_Icc ha hb (uIoc_subset_uIcc htab)
    have htIoo : t ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_ne htIcc.1 (Ne.symm htne0), lt_of_le_of_ne htIcc.2 htneT⟩
    have hnhds : Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
    exact ((ht htIcc).hasDerivAt hnhds).norm_sq.deriv
  rw [← hsq, intervalIntegral.integral_congr_ae hderiv]

theorem norm_sq_sub_norm_sq_eq_two_inner (u : timeH1 X T) (hT : 0 ≤ T) :
    ‖u.toFun T‖ ^ 2 - ‖u.toFun 0‖ ^ 2 =
      2 * inner ℝ u.toFunL2 u.deriv := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [u.norm_sq_sub_norm_sq_eq_two_intervalIntegral h0 hTmem,
    intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_const_mul, TimeSobolev.inner_def]
  congr 1
  apply MeasureTheory.integral_congr_ae
  have hae := TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
  change _ =ᵐ[volume.restrict (Icc (0 : ℝ) T)] _ at hae
  filter_upwards [hae] with t ht
  change inner ℝ (u.toFun t) (u.deriv t) =
    inner ℝ (TimeSobolev.ofContinuousOn u.continuousOn_toFun t) (u.deriv t)
  rw [ht]

end Hilbert

end timeH1

end

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
