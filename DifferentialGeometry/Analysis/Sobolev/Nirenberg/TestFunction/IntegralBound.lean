import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Basic
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound

noncomputable section

open MeasureTheory Filter
open DifferentialGeometry.Analysis.Sobolev

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma memLp_diffQuot
    (k : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : MemLp v 2 (volume : Measure E)) :
    MemLp (diffQuot k h v) 2 (volume : Measure E) := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact MemLp.zero
  · have h_eq : diffQuot k h v =
        fun x => h⁻¹ * translate k h v x + (-h⁻¹) * v x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh v x]
      change (v (x + h • EuclideanSpace.single k 1) - v x) / h =
        h⁻¹ * v (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * v x
      field_simp
      ring
    rw [h_eq]
    have h_translate : MemLp (translate k h v) 2 (volume : Measure E) :=
      memLp_translate (d := d) (p := 2) k h hv
    have h1 : MemLp (fun x : E => h⁻¹ * translate k h v x) 2
        (volume : Measure E) := by
      have hfun : (fun x : E => h⁻¹ * translate k h v x) =
          h⁻¹ • translate k h v := by
        funext x
        rw [Pi.smul_apply, smul_eq_mul]
      rw [hfun]
      exact h_translate.const_smul h⁻¹
    have h2 : MemLp (fun x : E => (-h⁻¹) * v x) 2
        (volume : Measure E) := by
      have hfun : (fun x : E => (-h⁻¹) * v x) = (-h⁻¹) • v := by
        funext x
        rw [Pi.smul_apply, smul_eq_mul]
      rw [hfun]
      exact hv.const_smul (-h⁻¹)
    exact h1.add h2

omit [NeZero d] in
private lemma integral_indicator_mul
    {u : E → ℝ} (k : Fin d) (h : ℝ) (η : E → ℝ) (c : ℝ) :
    ∫ x, c * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 ∂(volume : Measure E) =
      c * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by
  rw [show (fun x : E => c *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) =
      fun x : E => c * (Set.indicator (tsupport η)
        (fun y : E => (diffQuot k h u y)^2) x) from by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        ring]
  rw [integral_const_mul,
    MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]

omit [NeZero d] in
private lemma cutoff_derivative_sq_le
    {η u g : E → ℝ} (N : ℝ)
    (k : Fin d) (h : ℝ)
    (hη_sq_le_one : ∀ x, (η x) ^ 2 ≤ 1)
    (hderiv : ∀ x,
      |(fderiv ℝ (fun z => (η z) ^ 2) x) (EuclideanSpace.single k 1)| ≤ 2 * N) :
    ∀ x : E,
      ((η x)^2 * diffQuot k h g x +
        (fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1) *
          diffQuot k h u x)^2 ≤
        8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2 +
        2 * (η x)^2 * (diffQuot k h g x)^2 := by
  intro x
  set T1 : ℝ := (η x)^2 * diffQuot k h g x with hT1_def
  set T2 : ℝ :=
    (fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1) *
      diffQuot k h u x with hT2_def
  have h_sq_sum : (T1 + T2)^2 ≤ 2 * T1^2 + 2 * T2^2 := by
    nlinarith [sq_nonneg (T1 - T2)]
  refine h_sq_sum.trans ?_
  have hT1 : 2 * T1^2 ≤ 2 * (η x)^2 * (diffQuot k h g x)^2 := by
    have hη_four : (η x)^4 ≤ (η x)^2 := by
      nlinarith [sq_nonneg (η x), hη_sq_le_one x]
    calc
      2 * T1^2 = 2 * ((η x)^4 * (diffQuot k h g x)^2) := by
        rw [hT1_def]
        ring
      _ ≤ 2 * ((η x)^2 * (diffQuot k h g x)^2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hη_four (sq_nonneg _)) (by norm_num)
      _ = 2 * (η x)^2 * (diffQuot k h g x)^2 := by ring
  have hT2 : 2 * T2^2 ≤
      8 * N^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
    rw [hT2_def]
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx]
      have hsquare :
          ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 ≤
            4 * N^2 := by
        have habs_sq := pow_le_pow_left₀
          (abs_nonneg
            ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)))
          (hderiv x) 2
        rw [sq_abs] at habs_sq
        nlinarith [habs_sq]
      calc
        2 * (((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1) *
              diffQuot k h u x)^2)
            = 2 * (((fderiv ℝ (fun z => (η z)^2) x)
                (EuclideanSpace.single k 1))^2 * (diffQuot k h u x)^2) := by ring
        _ ≤ 2 * ((4 * N^2) * (diffQuot k h u x)^2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)) (by norm_num)
        _ = 8 * N^2 * 1 * (diffQuot k h u x)^2 := by ring
    · rw [Set.indicator_of_notMem hx]
      have heq : (fun y : E => (η y)^2) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        refine eventually_of_mem ((isClosed_tsupport η).isOpen_compl.mem_nhds hx) ?_
        intro y hy
        change (η y)^2 = 0
        rw [image_eq_zero_of_notMem_tsupport hy]
        norm_num
      have hfderiv : fderiv ℝ (fun y : E => (η y)^2) x =
          fderiv ℝ (fun _ : E => (0 : ℝ)) x :=
        Filter.EventuallyEq.fderiv_eq heq
      rw [hfderiv]
      simp
  calc
    2 * T1^2 + 2 * T2^2 ≤
        2 * (η x)^2 * (diffQuot k h g x)^2 +
          8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 := add_le_add hT1 hT2
    _ = 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2 +
        2 * (η x)^2 * (diffQuot k h g x)^2 := by ring

omit [NeZero d] in
theorem integral_sq_nirenbergTestFunction_le
    {u g : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hg_l2 : MemLp g 2 (volume : Measure E))
    (k : Fin d)
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) k g u Set.univ)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_bound : ∀ x, |η x| ≤ 1)
    {N : ℝ} (h_fderiv_η : ∀ x : E,
      |(fderiv ℝ η x) (EuclideanSpace.single k 1)| ≤ N)
    (h : ℝ) :
    ∫ x, (nirenbergTestFunction k h η u x)^2 ∂(volume : Measure E) ≤
      8 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
      2 * ∫ x, (η x)^2 * (diffQuot k h g x)^2
        ∂(volume : Measure E) := by
  by_cases hh : h = 0
  · subst h
    simp [nirenbergTestFunction]
  have hu_locInt :
      LocallyIntegrable u ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ]
    exact hu_l2.locallyIntegrable (by norm_num)
  have hg_locInt :
      LocallyIntegrable g ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ]
    exact hg_l2.locallyIntegrable (by norm_num)
  set F : E → ℝ := fun y => (η y)^2 * diffQuot k h u y with hF_def
  set G : E → ℝ := fun y =>
    (η y)^2 * diffQuot k h g y +
      (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1) *
        diffQuot k h u y with hG_def
  have hF_wp : DeGiorgi.HasWeakPartialDeriv (d := d) k G F Set.univ := by
    rw [hF_def, hG_def]
    exact hasWeakPartialDeriv_cutoff_sq_mul_diffQuot
      (d := d) k k h hη hu_locInt hg_locInt hwp
  have hη_sq_le_one : ∀ x, (η x)^2 ≤ 1 := fun x =>
    (sq_le_one_iff_abs_le_one (η x)).mpr (hη_bound x)
  have hN : 0 ≤ N :=
    (abs_nonneg ((fderiv ℝ η 0) (EuclideanSpace.single k 1))).trans (h_fderiv_η 0)
  have hη_sq_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => (η y)^2) :=
    hη.pow 2
  have hη_sq_cont : Continuous (fun y : E => (η y)^2) :=
    hη_sq_smooth.continuous
  have hderiv_cont : Continuous (fun y : E =>
      (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) :=
    (hη_sq_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_bound : ∀ y : E,
      |(fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)| ≤
        2 * N := by
    intro y
    rw [fderiv_cutoff_sq_apply hη, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hcutoff : 2 * |η y| ≤ 2 := by linarith [hη_bound y]
    exact mul_le_mul hcutoff (h_fderiv_η y) (abs_nonneg _) (by norm_num)
  have h_dq_u_l2 : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot (d := d) k h hu_l2
  have h_dq_g_l2 : MemLp (diffQuot k h g) 2 (volume : Measure E) :=
    memLp_diffQuot (d := d) k h hg_l2
  have hF_l2 : MemLp F 2 (volume : Measure E) := by
    have hmeas : AEStronglyMeasurable F (volume : Measure E) := by
      rw [hF_def]
      exact hη_sq_cont.aestronglyMeasurable.mul h_dq_u_l2.aestronglyMeasurable
    refine MemLp.mono h_dq_u_l2 hmeas ?_
    filter_upwards with x
    rw [hF_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (diffQuot k h u x), sq_nonneg (η x), hη_sq_le_one x]
  have hG_l2 : MemLp G 2 (volume : Measure E) := by
    have hT1 : MemLp (fun y : E => (η y)^2 * diffQuot k h g y) 2
        (volume : Measure E) := by
      refine MemLp.mono h_dq_g_l2
        (hη_sq_cont.aestronglyMeasurable.mul h_dq_g_l2.aestronglyMeasurable) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (diffQuot k h g x), sq_nonneg (η x), hη_sq_le_one x]
    have hT2 : MemLp (fun y : E =>
        (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1) *
          diffQuot k h u y) 2 (volume : Measure E) := by
      refine MemLp.mono (h_dq_u_l2.const_mul (2 * N))
        (hderiv_cont.aestronglyMeasurable.mul h_dq_u_l2.aestronglyMeasurable) ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (mul_nonneg (by norm_num) hN)]
      exact mul_le_mul_of_nonneg_right (hderiv_bound x) (abs_nonneg _)
    rw [hG_def]
    exact hT1.add hT2
  set Ω'' : Set E := Metric.thickening (|h| + 1) (tsupport η) with hΩ_def
  have h_radius : 0 < |h| + 1 := by positivity
  have hΩ_meas : MeasurableSet Ω'' := by
    rw [hΩ_def]
    exact Metric.isOpen_thickening.measurableSet
  have hΩ_compact : IsCompact (closure Ω'') := by
    have hsub : closure Ω'' ⊆ Metric.cthickening (|h| + 1) (tsupport η) := by
      rw [hΩ_def]
      exact Metric.closure_thickening_subset_cthickening _ _
    exact hη_supp.cthickening.of_isClosed_subset isClosed_closure hsub
  have h_outer :
      ∫ x in Ω'', (diffQuot k (-h) F x)^2 ∂(volume : Measure E) ≤
        ∫ x, (G x)^2 ∂(volume : Measure E) := by
    have h_energy := integral_sq_diffQuot_le_integral_sq_weakPartial_meas
      (d := d) hF_l2 hG_l2 k hF_wp MeasurableSet.univ hΩ_meas hΩ_compact
      (abs_pos.mpr (neg_ne_zero.mpr hh)) (fun _ _ => trivial)
      (neg_ne_zero.mpr hh) (le_refl |-h|)
    simpa only [Measure.restrict_univ] using h_energy
  have h_support : tsupport (nirenbergTestFunction k h η u) ⊆ Ω'' := by
    refine (tsupport_nirenbergTestFunction_subset (d := d) η u k h).trans ?_
    rw [hΩ_def]
    exact Metric.cthickening_subset_thickening' h_radius (by linarith) _
  have h_test_int :
      ∫ x, (nirenbergTestFunction k h η u x)^2 ∂(volume : Measure E) =
        ∫ x in Ω'', (diffQuot k (-h) F x)^2 ∂(volume : Measure E) := by
    have hfun : (fun x : E => (nirenbergTestFunction k h η u x)^2) =
        fun x : E => (diffQuot k (-h) F x)^2 := by
      funext x
      rw [hF_def]
      rfl
    rw [hfun]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    have hzero : nirenbergTestFunction k h η u x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hxt => hx (h_support hxt))
    have hx_eq := congrFun hfun x
    rw [← hx_eq, hzero]
    ring
  rw [h_test_int]
  refine h_outer.trans ?_
  have hpoint : ∀ x : E, (G x)^2 ≤
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 +
      2 * (η x)^2 * (diffQuot k h g x)^2 := by
    intro x
    rw [hG_def]
    exact cutoff_derivative_sq_le (d := d) N k h hη_sq_le_one hderiv_bound x
  have h_t1_int : Integrable (fun x : E =>
      8 * N^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume := by
    have hbase := (h_dq_u_l2.integrable_sq.indicator
      (isClosed_tsupport η).measurableSet).const_mul (8 * N^2)
    rw [show (fun x : E =>
          8 * N^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) =
        fun x : E => 8 * N^2 *
          (Set.indicator (tsupport η) (fun y : E => (diffQuot k h u y)^2) x) from by
        funext x
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          ring]
    exact hbase
  have h_eta_dq_g_l2 : MemLp (fun x : E => η x * diffQuot k h g x) 2
      (volume : Measure E) := by
    refine MemLp.mono h_dq_g_l2
      (hη.continuous.aestronglyMeasurable.mul h_dq_g_l2.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (diffQuot k h g x), hη_bound x]
  have h_t2_int : Integrable
      (fun x : E => 2 * (η x)^2 * (diffQuot k h g x)^2) volume := by
    rw [show (fun x : E => 2 * (η x)^2 * (diffQuot k h g x)^2) =
        fun x : E => 2 * (η x * diffQuot k h g x)^2 from by
      funext x
      ring]
    exact h_eta_dq_g_l2.integrable_sq.const_mul 2
  refine (integral_mono hG_l2.integrable_sq (h_t1_int.add h_t2_int) hpoint).trans ?_
  change (∫ x : E,
      8 * N^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2 +
        2 * (η x)^2 * (diffQuot k h g x)^2 ∂(volume : Measure E)) ≤ _
  rw [integral_add h_t1_int h_t2_int]
  rw [integral_indicator_mul (d := d) k h η (8 * N^2) (u := u)]
  rw [show (fun x : E => 2 * (η x)^2 * (diffQuot k h g x)^2) =
      fun x : E => 2 * ((η x)^2 * (diffQuot k h g x)^2) from by
      funext x
      ring]
  rw [integral_const_mul]

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
