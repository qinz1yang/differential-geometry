import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.C1Gluing
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Density
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Tent

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set intervalIntegral
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

theorem deriv_ae_of_eqOn [NormedSpace ℝ X]
    {T : ℝ} (hT : 0 < T) (u : timeH1 X T)
    (f : ℝ → X) (hf : ContDiff ℝ 1 f)
    (heq : EqOn u.toFun f (Icc (0 : ℝ) T)) :
    u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hmem] with t hu ht
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have huniq := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt htIcc
  have hfAt : HasDerivAt f (_root_.deriv f t) t :=
    ((hf.differentiable (by norm_num)) t).hasDerivAt
  calc
    u.deriv t = derivWithin u.toFun (Icc (0 : ℝ) T) t :=
      (hu.derivWithin huniq).symm
    _ = derivWithin f (Icc (0 : ℝ) T) t :=
      derivWithin_congr heq (heq htIcc)
    _ = _root_.deriv f t :=
      hfAt.hasDerivWithinAt.derivWithin huniq

section Hilbert

variable [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

theorem exists_tent_c1 {T c : ℝ} (hc : 0 < c) (hcT : c < T) (z : X) :
    ∃ v : ℕ → timeH1 X T, ∃ f : ℕ → ℝ → X,
      (∀ n, ContDiffOn ℝ 1 (f n) (Icc (0 : ℝ) T)) ∧
        (∀ n, EqOn (v n).toFun (f n) (Icc (0 : ℝ) T)) ∧
        (∀ n, f n 0 = 0) ∧ (∀ n, f n c = z) ∧
        (∀ n, f n T = 0) ∧
        Tendsto v atTop (𝓝 (timeH1.tent T c z)) ∧
        Tendsto (fun n => (v n).deriv) atTop
          (𝓝 (timeH1.tent T c z).deriv) := by
  classical
  let u : timeH1 X T := timeH1.tent T c z
  let uL := timeH1.slice u 0 c (by positivity) hcT.le
  let uR : timeH1 X (T - c) := timeH1.slice u c T hc.le le_rfl
  obtain ⟨wL, fL, hfL, hLf, hL0, hLc, hLg0, hLgc, hwL, hwLd⟩ :=
    exists_flat_dense (by simpa only [sub_zero] using hc) uL
  obtain ⟨wR, fR, hfR, hRf, hR0, hRT, hRg0, hRgT, hwR, hwRd⟩ :=
    exists_flat_dense (sub_pos.mpr hcT) uR
  have huL0 : uL.toFun 0 = 0 := by
    dsimp only [uL]
    rw [timeH1.slice_toFun u 0 c (by positivity) hcT.le
      (show (0 : ℝ) ∈ Icc (0 : ℝ) (c - 0) by constructor <;> simp [hc.le])]
    simp only [zero_add, u, timeH1.tent_init, timeH1.toFun_zero]
  have huLc : uL.toFun (c - 0) = z := by
    dsimp only [uL]
    rw [timeH1.slice_toFun u 0 c (by positivity) hcT.le
      (show c - 0 ∈ Icc (0 : ℝ) (c - 0) by constructor <;> simp [hc.le])]
    have harg : (0 : ℝ) + (c - 0) = c := by ring
    rw [harg]
    exact timeH1.tent_node z hc hcT
  have huR0 : uR.toFun 0 = z := by
    rw [timeH1.slice_toFun u c T hc.le le_rfl
      (show (0 : ℝ) ∈ Icc (0 : ℝ) (T - c) by
        constructor <;> simp [sub_nonneg.mpr hcT.le])]
    simpa only [add_zero, u] using timeH1.tent_node z hc hcT
  have huRT : uR.toFun (T - c) = 0 := by
    rw [timeH1.slice_toFun u c T hc.le le_rfl
      (show T - c ∈ Icc (0 : ℝ) (T - c) by
        constructor <;> simp [sub_nonneg.mpr hcT.le])]
    have harg : c + (T - c) = T := by ring
    rw [harg]
    exact timeH1.tent_end z hc hcT
  have hL0' : ∀ n, fL n 0 = 0 := fun n => (hL0 n).trans huL0
  have hLc' : ∀ n, fL n c = z := by
    intro n
    simpa only [sub_zero] using (hLc n).trans huLc
  have hR0' : ∀ n, fR n 0 = z := fun n => (hR0 n).trans huR0
  have hRT' : ∀ n, fR n (T - c) = 0 := fun n => (hRT n).trans huRT
  have hLgc' : ∀ n, fL n =ᶠ[𝓝 c] fun _ => z := by
    intro n
    simpa only [sub_zero] using
      (hLgc n).trans (Eventually.of_forall fun _ => huLc)
  have hRg0' : ∀ n, fR n =ᶠ[𝓝 (0 : ℝ)] fun _ => z := fun n =>
    (hRg0 n).trans (Eventually.of_forall fun _ => huR0)
  let f : ℕ → ℝ → X := fun n t =>
    Set.piecewise (Iic c) (fL n) (fun s => fR n (s - c)) t
  have hshift : Tendsto (fun t : ℝ => t - c) (𝓝 c) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t - c) (𝓝 c) (𝓝 (c - c)) :=
      (tendsto_id.sub_const c)
    simpa only [sub_self] using h
  have hRshift : ∀ n, (fun t => fR n (t - c)) =ᶠ[𝓝 c] fun _ => z :=
    fun n => (hRg0' n).comp_tendsto hshift
  have hfgerm : ∀ n, f n =ᶠ[𝓝 c] fun _ => z := by
    intro n
    filter_upwards [hLgc' n, hRshift n] with t hlt hrt
    by_cases htc : t ≤ c
    · simpa only [f, Set.piecewise, if_pos (mem_Iic.mpr htc)] using hlt
    · have hnot : t ∉ Iic c := by simpa only [mem_Iic] using htc
      simpa only [f, Set.piecewise, if_neg hnot] using hrt
  have hf_left : ∀ n, ContDiffOn ℝ 1 (f n) (Icc (0 : ℝ) c) := by
    intro n
    apply (hfL n).contDiffOn.congr
    intro t ht
    simp only [f, Set.piecewise, if_pos (mem_Iic.mpr ht.2)]
  have hf_right : ∀ n, ContDiffOn ℝ 1 (f n) (Icc c T) := by
    intro n
    have hcomp : ContDiff ℝ 1 (fun t : ℝ => fR n (t - c)) :=
      (hfR n).comp (contDiff_id.sub contDiff_const)
    apply hcomp.contDiffOn.congr
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hct
    · simp only [f, Set.piecewise, if_pos (mem_Iic.mpr le_rfl), sub_self,
        hLc' n, hR0' n]
    · simp only [f, Set.piecewise,
        if_neg (show t ∉ Iic c from not_le.mpr hct)]
  have hfC1 : ∀ n, ContDiffOn ℝ 1 (f n) (Icc (0 : ℝ) T) := by
    intro n
    apply contDiffOn_Icc_join hc hcT (hf_left n) (hf_right n)
    have hzero : HasDerivAt (f n) 0 c :=
      (hasDerivAt_const (x := c) z).congr_of_eventuallyEq (hfgerm n)
    have hLuniq := (uniqueDiffOn_Icc hc).uniqueDiffWithinAt
      (show c ∈ Icc (0 : ℝ) c from ⟨hc.le, le_rfl⟩)
    have hRuniq := (uniqueDiffOn_Icc hcT).uniqueDiffWithinAt
      (show c ∈ Icc c T from ⟨le_rfl, hcT.le⟩)
    rw [hzero.hasDerivWithinAt.derivWithin hLuniq,
      hzero.hasDerivWithinAt.derivWithin hRuniq]
  let v : ℕ → timeH1 X T := fun n =>
    timeH1.ofContDiffOn (hc.le.trans hcT.le) (f n) (hfC1 n)
  have hvf : ∀ n, EqOn (v n).toFun (f n) (Icc (0 : ℝ) T) := fun n =>
    timeH1.toFun_ofContDiffOn (hc.le.trans hcT.le) (f n) (hfC1 n)
  have hf0 : ∀ n, f n 0 = 0 := by
    intro n
    simp only [f, Set.piecewise, if_pos (mem_Iic.mpr hc.le), hL0' n]
  have hfc : ∀ n, f n c = z := by
    intro n
    simp only [f, Set.piecewise, if_pos (mem_Iic.mpr le_rfl), hLc' n]
  have hfT : ∀ n, f n T = 0 := by
    intro n
    simp only [f, Set.piecewise,
      if_neg (show T ∉ Iic c from not_le.mpr hcT), hRT' n]
  have hdf_left : ∀ n t, t ≤ c → _root_.deriv (f n) t = _root_.deriv (fL n) t := by
    intro n t htc
    by_cases hlt : t < c
    · apply EventuallyEq.deriv_eq
      filter_upwards [Iio_mem_nhds hlt] with s hs
      have hsc : s < c := by simpa only [mem_Iio] using hs
      simp only [f, Set.piecewise, if_pos (mem_Iic.mpr hsc.le)]
    · have htc' : t = c := le_antisymm htc (le_of_not_gt hlt)
      subst t
      exact EventuallyEq.deriv_eq ((hfgerm n).trans (hLgc' n).symm)
  have hdf_right : ∀ n t, c ≤ t →
      _root_.deriv (f n) t = _root_.deriv (fun s => fR n (s - c)) t := by
    intro n t hct
    rcases hct.eq_or_lt with rfl | hlt
    · exact EventuallyEq.deriv_eq ((hfgerm n).trans (hRshift n).symm)
    · apply EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds hlt] with s hs
      have hcs : c < s := by simpa only [mem_Ioi] using hs
      have hnot : s ∉ Iic c := by simpa only [mem_Iic] using (not_le.mpr hcs)
      simp only [f, Set.piecewise, if_neg hnot]
  have hder_comp : ∀ n t, _root_.deriv (fun s => fR n (s - c)) t =
      _root_.deriv (fR n) (t - c) := by
    intro n t
    have hsub : HasDerivAt (fun s : ℝ => s - c) 1 t :=
      hasDerivAt_id t |>.sub_const c
    exact (((hfR n).differentiable (by norm_num) (t - c)).hasFDerivAt
      |>.comp_hasDerivAt t hsub).deriv
  have huLder : uL.deriv =ᵐ[timeMeasure (c - 0)] fun _ => c⁻¹ • z := by
    have hs := timeH1.slice_deriv u 0 c (by positivity) hcT.le
    have ht := timeH1.tent_deriv_left z hcT
    rw [restrict_Ioo_eq_restrict_Icc] at ht
    have ht' : u.deriv =ᵐ[timeMeasure (c - 0)] fun _ => c⁻¹ • z := by
      simpa only [u, sub_zero, timeMeasure] using ht
    filter_upwards [hs, ht'] with t hst htt
    rw [hst]
    simpa only [zero_add] using htt
  have huRder : uR.deriv =ᵐ[timeMeasure (T - c)]
      fun _ => -(T - c)⁻¹ • z := by
    have hs := timeH1.slice_deriv u c T hc.le le_rfl
    have ht := timeH1.tent_deriv_right (T := T) z hc
    rw [restrict_Ioo_eq_restrict_Icc] at ht
    have hmp : MeasurePreserving (fun t : ℝ => t + c) (timeMeasure (T - c))
        (volume.restrict (Icc c T)) := by
      have h := (measurePreserving_add_right volume c).restrict_image_emb
        (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
        (Icc (0 : ℝ) (T - c))
      simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel] using h
    have ht' := hmp.quasiMeasurePreserving.ae_eq_comp ht
    filter_upwards [hs, ht'] with t hst htt
    rw [hst]
    simpa only [Function.comp_apply, u, add_comm] using htt
  have hwLrep : ∀ n, wL n |>.deriv =ᵐ[timeMeasure (c - 0)]
      _root_.deriv (fL n) :=
    fun n => deriv_ae_of_eqOn (by simpa only [sub_zero] using hc)
      (wL n) (fL n) (hfL n) (hLf n)
  have hwRrep : ∀ n, wR n |>.deriv =ᵐ[timeMeasure (T - c)] _root_.deriv (fR n) :=
    fun n => deriv_ae_of_eqOn (sub_pos.mpr hcT) (wR n) (fR n) (hfR n) (hRf n)
  have hLsq : ∀ n, ‖(wL n).deriv - uL.deriv‖ ^ 2 =
      ∫ t in (0 : ℝ)..c, ‖_root_.deriv (fL n) t - c⁻¹ • z‖ ^ 2 := by
    intro n
    conv_rhs => rw [← sub_zero c]
    rw [norm_sq_eq_integral]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by simpa only [sub_zero] using hc.le)]
    apply intervalIntegral.integral_congr_ae_restrict
    have hpoint : ∀ᵐ t ∂timeMeasure (c - 0),
        ‖((wL n).deriv - uL.deriv) t‖ ^ 2 =
          ‖_root_.deriv (fL n) t - (c - 0)⁻¹ • z‖ ^ 2 := by
      filter_upwards [Lp.coeFn_sub (wL n).deriv uL.deriv, hwLrep n, huLder]
      with t hsub hw hu
      rw [hsub]
      change ‖(wL n).deriv t - uL.deriv t‖ ^ 2 = _
      rw [hw, hu]
      simp only [sub_zero]
    rw [uIoc_of_le (by simpa only [sub_zero] using hc.le),
      restrict_Ioc_eq_restrict_Icc]
    unfold timeMeasure at hpoint
    filter_upwards [hpoint] with t ht
    exact ht
  have hRsq : ∀ n, ‖(wR n).deriv - uR.deriv‖ ^ 2 =
      ∫ t in (0 : ℝ)..(T - c),
        ‖_root_.deriv (fR n) t - (-(T - c)⁻¹ • z)‖ ^ 2 := by
    intro n
    rw [norm_sq_eq_integral, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (sub_nonneg.mpr hcT.le)]
    apply intervalIntegral.integral_congr_ae_restrict
    have hpoint : ∀ᵐ t ∂timeMeasure (T - c),
        ‖((wR n).deriv - uR.deriv) t‖ ^ 2 =
          ‖_root_.deriv (fR n) t - (-(T - c)⁻¹ • z)‖ ^ 2 := by
      filter_upwards [Lp.coeFn_sub (wR n).deriv uR.deriv, hwRrep n, huRder]
      with t hsub hw hu
      rw [hsub]
      change ‖(wR n).deriv t - uR.deriv t‖ ^ 2 = _
      rw [hw, hu]
    rw [uIoc_of_le (sub_nonneg.mpr hcT.le), restrict_Ioc_eq_restrict_Icc]
    unfold timeMeasure at hpoint
    filter_upwards [hpoint] with t ht
    exact ht
  have hvsq : ∀ n, ‖(v n).deriv - u.deriv‖ ^ 2 =
      ‖(wL n).deriv - uL.deriv‖ ^ 2 +
        ‖(wR n).deriv - uR.deriv‖ ^ 2 := by
    intro n
    have hvder := timeH1.deriv_ofContDiffOn (hc.le.trans hcT.le) (f n) (hfC1 n)
    have hsub := Lp.coeFn_sub (v n).deriv u.deriv
    have hutL := timeH1.tent_deriv_left z hcT
    rw [restrict_Ioo_eq_restrict_Icc] at hutL
    have hutR := timeH1.tent_deriv_right (T := T) z hc
    rw [restrict_Ioo_eq_restrict_Icc] at hutR
    have hutL' : u.deriv =ᵐ[volume.restrict (uIoc (0 : ℝ) c)]
        fun _ => c⁻¹ • z := by
      simpa only [u, uIoc_of_le hc.le, restrict_Ioc_eq_restrict_Icc] using hutL
    have hutR' : u.deriv =ᵐ[volume.restrict (uIoc c T)]
        fun _ => -(T - c)⁻¹ • z := by
      simpa only [u, uIoc_of_le hcT.le, restrict_Ioc_eq_restrict_Icc] using hutR
    have hfull : IntervalIntegrable
        (fun t => ‖((v n).deriv - u.deriv) t‖ ^ 2) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hc.le.trans hcT.le)]
      exact (Lp.memLp ((v n).deriv - u.deriv)).integrable_norm_pow (by norm_num)
    rw [norm_sq_eq_integral, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hc.le.trans hcT.le),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hfull.mono_set (show uIcc (0 : ℝ) c ⊆ uIcc (0 : ℝ) T by
          simpa only [uIcc_of_le hc.le, uIcc_of_le (hc.le.trans hcT.le)] using
            (Icc_subset_Icc le_rfl hcT.le)))
        (hfull.mono_set (show uIcc c T ⊆ uIcc (0 : ℝ) T by
          simpa only [uIcc_of_le hcT.le, uIcc_of_le (hc.le.trans hcT.le)] using
            (Icc_subset_Icc hc.le le_rfl))), hLsq n, hRsq n]
    congr 1
    · apply intervalIntegral.integral_congr_ae_restrict
      have hle : volume.restrict (uIoc (0 : ℝ) c) ≤ timeMeasure T := by
        rw [uIoc_of_le hc.le, restrict_Ioc_eq_restrict_Icc]
        unfold timeMeasure
        exact Measure.restrict_mono (Icc_subset_Icc le_rfl hcT.le) le_rfl
      filter_upwards [hsub.filter_mono (ae_mono hle),
        hvder.filter_mono (ae_mono hle), hutL',
        ae_restrict_mem measurableSet_uIoc]
        with t hst hvt hut ht
      have ht' : t ∈ Ioc (0 : ℝ) c := by
        simpa only [uIoc_of_le hc.le] using ht
      have hvt' : (v n).deriv t = _root_.deriv (f n) t := by
        simpa only [v] using hvt
      rw [hst]
      change ‖(v n).deriv t - u.deriv t‖ ^ 2 = _
      rw [hvt', hut, hdf_left n t ht'.2]
    · have hraw : (∫ t in c..T, ‖_root_.deriv (f n) t -
          (-(T - c)⁻¹ • z)‖ ^ 2) =
          ∫ t in c..T, ‖_root_.deriv (fR n) (t - c) -
            (-(T - c)⁻¹ • z)‖ ^ 2 := by
        apply intervalIntegral.integral_congr_ae_restrict
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
        have ht' : t ∈ Ioc c T := by
          simpa only [uIoc_of_le hcT.le] using ht
        rw [hdf_right n t ht'.1.le, hder_comp]
      have hle : volume.restrict (uIoc c T) ≤ timeMeasure T := by
        rw [uIoc_of_le hcT.le, restrict_Ioc_eq_restrict_Icc]
        unfold timeMeasure
        exact Measure.restrict_mono (Icc_subset_Icc hc.le le_rfl) le_rfl
      calc
        (∫ t in c..T, ‖((v n).deriv - u.deriv) t‖ ^ 2) =
            ∫ t in c..T, ‖_root_.deriv (f n) t -
              (-(T - c)⁻¹ • z)‖ ^ 2 := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hsub.filter_mono (ae_mono hle),
            hvder.filter_mono (ae_mono hle), hutR']
            with t hst hvt hut
          have hvt' : (v n).deriv t = _root_.deriv (f n) t := by
            simpa only [v] using hvt
          rw [hst]
          change ‖(v n).deriv t - u.deriv t‖ ^ 2 = _
          rw [hvt', hut]
        _ = ∫ t in c..T, ‖_root_.deriv (fR n) (t - c) -
              (-(T - c)⁻¹ • z)‖ ^ 2 := hraw
        _ = ∫ t in (0 : ℝ)..(T - c),
              ‖_root_.deriv (fR n) t - (-(T - c)⁻¹ • z)‖ ^ 2 := by
          simpa only [sub_self] using
            (intervalIntegral.integral_comp_sub_right
              (fun t => ‖_root_.deriv (fR n) t - (-(T - c)⁻¹ • z)‖ ^ 2)
              (a := c) (b := T) c)
  have hvD : Tendsto (fun n => (v n).deriv) atTop (𝓝 u.deriv) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hLnorm : Tendsto (fun n => ‖(wL n).deriv - uL.deriv‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hwLd
    have hRnorm : Tendsto (fun n => ‖(wR n).deriv - uR.deriv‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hwRd
    have hsq : Tendsto (fun n => ‖(v n).deriv - u.deriv‖ ^ 2) atTop (𝓝 0) := by
      have hsum := hLnorm.pow 2 |>.add (hRnorm.pow 2)
      norm_num at hsum
      simpa only [hvsq] using hsum
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  have hvinit : ∀ n, (v n).init = u.init := by
    intro n
    simp only [v, timeH1.ofContDiffOn, timeH1.init_mk, hf0 n, u,
      timeH1.tent_init]
  have hv : Tendsto v atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnormD : Tendsto (fun n => ‖(v n).deriv - u.deriv‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hvD
    have hnorm : ∀ n, ‖v n - u‖ = ‖(v n).deriv - u.deriv‖ := by
      intro n
      have hsquare := timeH1.norm_sq_eq (v n - u)
      change ‖v n - u‖ ^ 2 = ‖(v n).init - u.init‖ ^ 2 +
        ‖(v n).deriv - u.deriv‖ ^ 2 at hsquare
      rw [hvinit n, sub_self, norm_zero] at hsquare
      norm_num at hsquare
      nlinarith [norm_nonneg (v n - u), norm_nonneg ((v n).deriv - u.deriv)]
    simpa only [hnorm] using hnormD
  simpa only [u] using ⟨v, f, hfC1, hvf, hf0, hfc, hfT, hv, hvD⟩

end Hilbert

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
