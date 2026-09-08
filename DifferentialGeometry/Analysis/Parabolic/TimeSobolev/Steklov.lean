import DifferentialGeometry.Analysis.Integration.Lp.Steklov
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_timeH1_steklovAverage
    {f : ℝ → X} (hf : MemLp f 2 volume) (h T : ℝ) :
    ∃ w : timeH1 X T,
      (∀ t ∈ Icc (0 : ℝ) T, w.toFun t = steklovAverage h f t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => h⁻¹ • (f (t + h) - f t)) := by
  have hshift : MemLp (fun t => f (t + h)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have hd : MemLp (fun t => h⁻¹ • (f (t + h) - f t)) 2 (timeMeasure T) :=
    ((hshift.sub hf).const_smul h⁻¹).restrict (Icc (0 : ℝ) T)
  let w : timeH1 X T := timeH1.mk (steklovAverage h f 0) (hd.toLp _)
  have hwderiv : w.deriv =ᵐ[timeMeasure T] (fun t => h⁻¹ • (f (t + h) - f t)) :=
    hd.coeFn_toLp
  refine ⟨w, ?_, hwderiv⟩
  intro t ht
  have hfint (a b : ℝ) : IntervalIntegrable f volume a b :=
    ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hsint (a b : ℝ) : IntervalIntegrable (fun s => f (s + h)) volume a b :=
    ((hshift.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hid : (∫ s in (0 : ℝ)..t, w.deriv s) =
      ∫ s in (0 : ℝ)..t, h⁻¹ • (f (s + h) - f s) := by
    apply intervalIntegral.integral_congr_ae
    apply ae_imp_of_ae_restrict
    exact hwderiv.filter_mono (ae_mono (Measure.restrict_mono
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)) le_rfl))
  rw [timeH1.toFun_apply, hid, intervalIntegral.integral_smul,
    intervalIntegral.integral_sub (hsint 0 t) (hfint 0 t),
    intervalIntegral.integral_comp_add_right]
  change steklovAverage h f 0 + h⁻¹ • ((∫ s in 0 + h..t + h, f s) -
    ∫ s in (0 : ℝ)..t, f s) = steklovAverage h f t
  unfold steklovAverage
  rw [zero_add, ← smul_add]
  congr 1
  rw [← add_sub_assoc, intervalIntegral.integral_add_adjacent_intervals
    (hfint 0 h) (hfint h (t + h))]
  exact intervalIntegral.integral_interval_sub_left (hfint 0 (t + h)) (hfint 0 t)

theorem exists_timeH1_steklovAverage_timeL2
    {T : ℝ} (u : timeL2 X T) (h : ℝ) :
    ∃ w : timeH1 X T,
      (∀ t ∈ Icc (0 : ℝ) T,
        w.toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => h⁻¹ •
        ((Icc (0 : ℝ) T).indicator u (t + h) - (Icc (0 : ℝ) T).indicator u t)) := by
  have hu : MemLp ((Icc (0 : ℝ) T).indicator (fun t => u t)) 2 volume :=
    (memLp_indicator_iff_restrict (f := fun t => u t) measurableSet_Icc).mpr (Lp.memLp u)
  exact exists_timeH1_steklovAverage hu h T

theorem steklovAverage_compLpL_timeL2 {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) {T : ℝ} (u : timeL2 X T) (h t : ℝ) :
    steklovAverage h ((Icc (0 : ℝ) T).indicator (L.compLpL 2 (timeMeasure T) u)) t =
      L (steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) := by
  have hu : MemLp ((Icc (0 : ℝ) T).indicator (fun s => u s)) 2 volume :=
    (memLp_indicator_iff_restrict (f := fun s => u s) measurableSet_Icc).mpr (Lp.memLp u)
  have hL : ((Icc (0 : ℝ) T).indicator (L.compLpL 2 (timeMeasure T) u)) =ᵐ[volume]
      fun s => L ((Icc (0 : ℝ) T).indicator u s) := by
    have heq := L.coeFn_compLpL u
    change (L.compLpL 2 (timeMeasure T) u : ℝ → Y) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      (fun s => L (u s)) at heq
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at heq
    filter_upwards [heq] with s hs
    by_cases hsm : s ∈ Icc (0 : ℝ) T
    · simpa only [indicator_of_mem hsm] using hs hsm
    · simp only [indicator_of_notMem hsm, map_zero]
  rw [steklovAverage_congr_ae hL h t]
  exact steklovAverage_comp_continuousLinearMap L
    ((hu.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem steklovAverage_indicator_Icc_right_eq_zero
    (f : ℝ → X) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    steklovAverage h ((Icc (0 : ℝ) T).indicator f) T = 0 := by
  unfold steklovAverage
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hh)]
  have hzero : (∫ s in Ioc T (T + h), (Icc (0 : ℝ) T).indicator f s) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
      indicator_of_notMem (fun hmem => (not_le.mpr hs.1) hmem.2) f
  rw [hzero, smul_zero]

theorem exists_timeH1_steklovAverage_timeL2_terminal_zero
    {T : ℝ} (hT : 0 ≤ T) (u : timeL2 X T) {h : ℝ} (hh : 0 ≤ h) :
    ∃ w : timeH1 X T,
      (∀ t ∈ Icc (0 : ℝ) T,
        w.toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t => h⁻¹ •
        ((Icc (0 : ℝ) T).indicator u (t + h) - (Icc (0 : ℝ) T).indicator u t)) ∧
      w.toFun T = 0 := by
  obtain ⟨w, hw, hwd⟩ := exists_timeH1_steklovAverage_timeL2 u h
  exact ⟨w, hw, hwd, (hw T ⟨hT, le_rfl⟩).trans
    (steklovAverage_indicator_Icc_right_eq_zero u T hh)⟩

theorem ae_hasDerivWithinAt_steklovAverage [CompleteSpace X]
    {f : ℝ → X} (hf : MemLp f 2 volume) (h T : ℝ) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivWithinAt (steklovAverage h f) (h⁻¹ • (f (t + h) - f t)) (Icc (0 : ℝ) T) t := by
  obtain ⟨w, hw, hwd⟩ := exists_timeH1_steklovAverage hf h T
  filter_upwards [w.ae_hasDerivWithinAt_toFun, hwd, ae_restrict_mem measurableSet_Icc]
    with t ht hd htmem
  rw [hd] at ht
  exact ht.congr (fun s hs => (hw s hs).symm) (hw t htmem).symm

theorem ae_tendsto_steklovAverage [CompleteSpace X]
    {f : ℝ → X} (hf : LocallyIntegrable f volume) :
    ∀ᵐ t, Tendsto (fun h => steklovAverage h f t) (𝓝[≠] 0) (𝓝 (f t)) := by
  have hfint (a b : ℝ) : IntervalIntegrable f volume a b :=
    (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  filter_upwards [locallyIntegrable_ae_hasDerivAt_integral hf] with t ht
  have hlim := (ht 0).tendsto_slope_zero
  simpa only [intervalIntegral.integral_interval_sub_left
    (hfint 0 (t + _)) (hfint 0 t), steklovAverage] using hlim

theorem ae_tendsto_steklovAverage_timeL2 [CompleteSpace X]
    {T : ℝ} (u : timeL2 X T) :
    ∀ᵐ t ∂timeMeasure T,
      Tendsto (fun h => steklovAverage h ((Icc (0 : ℝ) T).indicator u) t)
        (𝓝[≠] 0) (𝓝 (u t)) := by
  have hu : MemLp ((Icc (0 : ℝ) T).indicator (fun t => u t)) 2 volume :=
    (memLp_indicator_iff_restrict (f := fun t => u t) measurableSet_Icc).mpr (Lp.memLp u)
  have hlim := ae_restrict_of_ae (s := Icc (0 : ℝ) T)
    (ae_tendsto_steklovAverage (hu.locallyIntegrable (by norm_num)))
  filter_upwards [hlim, ae_restrict_mem measurableSet_Icc] with t ht htmem
  simpa only [indicator_of_mem htmem] using ht

theorem exists_timeH1_cutoff_steklovAverage_timeL2 [CompleteSpace X]
    {T : ℝ}
    (hT : 0 ≤ T) (u : timeL2 X T) (h : ℝ) {ζ : ℝ → ℝ}
    (hζ : ContDiffOn ℝ 1 ζ (Icc (0 : ℝ) T)) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    ∃ w : timeH1 X T,
      w.init = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        w.toFun t = ζ t • steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) ∧
      w.deriv =ᵐ[timeMeasure T] (fun t =>
        _root_.deriv ζ t • steklovAverage h ((Icc (0 : ℝ) T).indicator u) t +
          ζ t • (h⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + h) -
            (Icc (0 : ℝ) T).indicator u t))) ∧
      w.toFun T = 0 := by
  obtain ⟨v, hv, hvd⟩ := exists_timeH1_steklovAverage_timeL2 u h
  let z := timeH1.ofContDiffOn hT ζ hζ
  have hz : ∀ t ∈ Icc (0 : ℝ) T, z.toFun t = ζ t := timeH1.toFun_ofContDiffOn hT ζ hζ
  have hzd : z.deriv =ᵐ[timeMeasure T] _root_.deriv ζ := timeH1.deriv_ofContDiffOn hT ζ hζ
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_smul z v
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rw [hwi]
    change ζ 0 • v.init = 0
    rw [hζ0, zero_smul]
  · intro t ht
    rw [hw t ht, hz t ht, hv t ht]
  · filter_upwards [hwd, hzd, hvd, ae_restrict_mem measurableSet_Icc] with t hwt hzt hvdt ht
    rw [hwt, hzt, hvdt, hz t ht, hv t ht]
  · rw [hw T ⟨hT, le_rfl⟩, hz T ⟨hT, le_rfl⟩, hζT, zero_smul]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] {T : ℝ}

def timeL2.zeroExtension (u : timeL2 X T) : Lp X 2 (volume : Measure ℝ) :=
  ((memLp_indicator_iff_restrict (f := fun t => u t) measurableSet_Icc).mpr
    (Lp.memLp u)).toLp _

theorem timeL2.coeFn_zeroExtension (u : timeL2 X T) :
    u.zeroExtension =ᵐ[volume] (Icc (0 : ℝ) T).indicator u := MemLp.coeFn_toLp _

@[simp] theorem timeL2.norm_zeroExtension (u : timeL2 X T) :
    ‖u.zeroExtension‖ = ‖u‖ := by
  rw [timeL2.zeroExtension, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  rfl

variable [NormedSpace ℝ X]

@[simp] theorem timeL2.restrict_zeroExtension (u : timeL2 X T) :
    LpToLpRestrictCLM ℝ X ℝ volume 2 (Icc (0 : ℝ) T) u.zeroExtension = u := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Icc (0 : ℝ) T) u.zeroExtension,
    ae_restrict_of_ae u.coeFn_zeroExtension, ae_restrict_mem measurableSet_Icc] with t h₁ h₂ ht
  rw [h₁, h₂, indicator_of_mem ht]
  rfl

def timeL2.steklovAverage (h : ℝ) (u : timeL2 X T) : timeL2 X T :=
  LpToLpRestrictCLM ℝ X ℝ volume 2 (Icc (0 : ℝ) T) (Lp.steklovAverage h u.zeroExtension)

theorem timeL2.norm_steklovAverage_le (h : ℝ) (u : timeL2 X T) :
    ‖u.steklovAverage h‖ ≤ ‖u‖ := by
  calc
    ‖u.steklovAverage h‖ ≤ ‖Lp.steklovAverage h u.zeroExtension‖ :=
      norm_Lp_toLp_restrict_le _ _
    _ ≤ ‖u.zeroExtension‖ := Lp.norm_steklovAverage_le h _
    _ = ‖u‖ := u.norm_zeroExtension

variable [CompleteSpace X]

theorem timeL2.tendsto_steklovAverage (u : timeL2 X T) :
    Tendsto (fun h => u.steklovAverage h) (𝓝[≠] 0) (𝓝 u) := by
  have hc := (LpToLpRestrictCLM ℝ X ℝ volume 2 (Icc (0 : ℝ) T)).continuous.tendsto u.zeroExtension
  have h := hc.comp (Lp.tendsto_steklovAverage u.zeroExtension)
  rw [u.restrict_zeroExtension] at h
  exact h

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {T : ℝ}

theorem timeL2.coeFn_steklovAverage (h : ℝ) (u : timeL2 X T) :
    u.steklovAverage h =ᵐ[timeMeasure T]
      fun t => DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage h ((Icc (0 : ℝ) T).indicator u) t := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Icc (0 : ℝ) T)
    (Lp.steklovAverage h u.zeroExtension),
    ae_restrict_of_ae (Lp.coeFn_steklovAverage h u.zeroExtension)] with t hrestrict havg
  change (LpToLpRestrictCLM ℝ X ℝ volume 2 (Icc (0 : ℝ) T)
    (Lp.steklovAverage h u.zeroExtension)) t = _
  rw [hrestrict, havg]
  exact steklovAverage_congr_ae u.coeFn_zeroExtension h t

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {T h : ℝ}

theorem timeH1.toFunL2_eq_steklovAverage (u : timeL2 X T) (w : timeH1 X T)
    (hw : ∀ t ∈ Icc (0 : ℝ) T,
      w.toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) :
    w.toFunL2 = u.steklovAverage h := by
  apply Lp.ext
  filter_upwards [coeFn_ofContinuousOn w.continuousOn_toFun,
    timeL2.coeFn_steklovAverage h u, ae_restrict_mem measurableSet_Icc] with t hwt hut ht
  exact hwt.trans ((hw t ht).trans hut.symm)

theorem timeH1.norm_toFunL2_le_of_steklovAverage (u : timeL2 X T) (w : timeH1 X T)
    (hw : ∀ t ∈ Icc (0 : ℝ) T,
      w.toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) :
    ‖w.toFunL2‖ ≤ ‖u‖ := by
  rw [w.toFunL2_eq_steklovAverage u hw]
  exact u.norm_steklovAverage_le h

theorem tendsto_toFunL2_steklovAverage (u : timeL2 X T) (w : ℝ → timeH1 X T)
    (hw : ∀ h t, t ∈ Icc (0 : ℝ) T →
      (w h).toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) :
    Tendsto (fun h => (w h).toFunL2) (𝓝[≠] 0) (𝓝 u) := by
  have heq : (fun h => (w h).toFunL2) = (fun h => u.steklovAverage h) :=
    funext fun h => (w h).toFunL2_eq_steklovAverage u (hw h)
  rw [heq]
  exact u.tendsto_steklovAverage

theorem exists_timeH1_steklovAverage_timeL2_tendsto (u : timeL2 X T) :
    ∃ w : ℝ → timeH1 X T,
      (∀ h t, t ∈ Icc (0 : ℝ) T →
        (w h).toFun t = steklovAverage h ((Icc (0 : ℝ) T).indicator u) t) ∧
      (∀ h, (w h).deriv =ᵐ[timeMeasure T] (fun t => h⁻¹ •
        ((Icc (0 : ℝ) T).indicator u (t + h) - (Icc (0 : ℝ) T).indicator u t))) ∧
      (∀ h, ‖(w h).toFunL2‖ ≤ ‖u‖) ∧
      Tendsto (fun h => (w h).toFunL2) (𝓝[≠] 0) (𝓝 u) := by
  choose w hw hwd using exists_timeH1_steklovAverage_timeL2 u
  exact ⟨w, hw, hwd, fun h => (w h).norm_toFunL2_le_of_steklovAverage u (hw h),
    tendsto_toFunL2_steklovAverage u w hw⟩

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
