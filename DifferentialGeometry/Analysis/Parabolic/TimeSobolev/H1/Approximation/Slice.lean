import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T a b : ℝ}

private theorem shift_preserving (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => t + a) (timeMeasure (b - a))
      (volume.restrict (Icc a b)) := by
  have h := (measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
  simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel] using h

namespace timeL2

def slice (f : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    timeL2 X (b - a) := by
  have hset : Icc a b ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hle : volume.restrict (Icc a b) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hset le_rfl
  have hf : MemLp (fun t : ℝ => f t) 2 (volume.restrict (Icc a b)) :=
    (Lp.memLp f).mono_measure hle
  exact (hf.comp_measurePreserving (shift_preserving a b)).toLp (fun t => f (t + a))

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem slice_coe (f : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    slice f a b ha hbT =ᵐ[timeMeasure (b - a)] fun t => f (t + a) := by
  unfold slice
  exact MemLp.coeFn_toLp _

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem slice_add (f g : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    slice (f + g) a b ha hbT = slice f a b ha hbT + slice g a b ha hbT := by
  apply Lp.ext
  filter_upwards [slice_coe (f + g) a b ha hbT, slice_coe f a b ha hbT,
    slice_coe g a b ha hbT, Lp.coeFn_add (slice f a b ha hbT) (slice g a b ha hbT),
    ae_add_right_timeMeasure ha hbT (Lp.coeFn_add f g)] with t hfg hf hg hadd hshift
  simpa only [hfg, hadd, hf, hg, Pi.add_apply] using hshift


omit [CompleteSpace X] in
theorem slice_compLpL {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (f : timeL2 X T)
    (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    slice (L.compLpL 2 (timeMeasure T) f) a b ha hbT =
      L.compLpL 2 (timeMeasure (b - a)) (slice f a b ha hbT) := by
  apply Lp.ext
  filter_upwards [slice_coe (L.compLpL 2 (timeMeasure T) f) a b ha hbT,
    L.coeFn_compLpL (p := 2) (μ := timeMeasure (b - a)) (slice f a b ha hbT),
    slice_coe f a b ha hbT,
    ae_add_right_timeMeasure ha hbT (L.coeFn_compLpL (p := 2) (μ := timeMeasure T) f)]
    with t hslice hL hf hshift
  simpa only [hslice, hL, hf] using hshift


end timeL2

namespace timeH1

def slice (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    timeH1 X (b - a) :=
  mk (u.toFun a) (timeL2.slice u.deriv a b ha hbT)

omit [CompleteSpace X] in
theorem slice_deriv (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    (slice u a b ha hbT).deriv =ᵐ[timeMeasure (b - a)] fun t => u.deriv (a + t) := by
  filter_upwards [timeL2.slice_coe u.deriv a b ha hbT] with t ht
  simpa only [slice, deriv_mk, add_comm] using ht

omit [CompleteSpace X] in
theorem slice_toFun (u : timeH1 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (b - a)) :
    (slice u a b ha hbT).toFun t = u.toFun (a + t) := by
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) (b - a) := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
  have hrestr :
      (fun s : ℝ => (timeL2.slice u.deriv a b ha hbT) s)
        =ᵐ[volume.restrict (uIoc (0 : ℝ) t)] fun s => u.deriv (s + a) :=
    (timeL2.slice_coe u.deriv a b ha hbT).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hint :
      (∫ s in (0 : ℝ)..t, (timeL2.slice u.deriv a b ha hbT) s)
        = ∫ s in (0 : ℝ)..t, u.deriv (s + a) :=
    intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict hrestr)
  have haT : a ≤ T := by linarith [ht.1, ht.2]
  have hat_mem : t + a ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have hdiff := u.toFun_sub_toFun (t₀ := a) (t₁ := t + a) ⟨ha, haT⟩ hat_mem
  change u.toFun a + ∫ s in (0 : ℝ)..t, (timeL2.slice u.deriv a b ha hbT) s = _
  rw [hint]
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  rw [← hdiff]
  abel_nf

omit [CompleteSpace X] in
theorem slice_toFunL2 (u : timeH1 X T) (c d : ℝ) (hc : 0 ≤ c) (hdT : d ≤ T) :
    (u.slice c d hc hdT).toFunL2 = timeL2.slice u.toFunL2 c d hc hdT := by
  apply Lp.ext
  have hI : Icc c d ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨hc.trans ht.1, ht.2.trans hdT⟩
  have hrep := (measurePreserving_add_right_timeMeasure_restrict hI).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (coeFn_ofContinuousOn u.continuousOn_toFun))
  filter_upwards [coeFn_ofContinuousOn (u.slice c d hc hdT).continuousOn_toFun,
    timeL2.slice_coe u.toFunL2 c d hc hdT, hrep,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t hs hf hu ht
  change (u.slice c d hc hdT).toFunL2 t = (u.slice c d hc hdT).toFun t at hs
  change u.toFunL2 (c + t) = u.toFun (c + t) at hu
  rw [hs, hf, add_comm t c, hu, slice_toFun u c d hc hdT ht]


end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeL2.norm_slice_eq {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} (f : timeL2 X T) (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    ‖timeL2.slice f a b ha hbT‖ =
      (eLpNorm f 2 (volume.restrict (Icc a b))).toReal := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hshift := measurePreserving_add_right_timeMeasure_restrict hsub
  have hmeas := ((Lp.memLp f).restrict (Icc a b)).aestronglyMeasurable
  have hnorm : eLpNorm (fun t => f (t + a)) 2 (timeMeasure (b - a)) =
      eLpNorm f 2 (volume.restrict (Icc a b)) := by
    have h := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hmeas hshift
    rw [timeMeasure_restrict_Icc_eq_volume_restrict_Icc hsub] at h
    simpa only [Function.comp_def, add_comm] using h
  rw [Lp.norm_def, eLpNorm_congr_ae (timeL2.slice_coe f a b ha hbT), hnorm]

theorem timeL2.norm_slice_toLp_eq {X : Type*} [NormedAddCommGroup X]
    {T : ℝ} {f : ℝ → X} (hf : MemLp f 2 (timeMeasure T))
    (a b : ℝ) (ha : 0 ≤ a) (hbT : b ≤ T) :
    ‖timeL2.slice (hf.toLp f) a b ha hbT‖ =
      (eLpNorm f 2 (volume.restrict (Icc a b))).toReal := by
  rw [timeL2.norm_slice_eq]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  have hsub : Icc a b ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨ha.trans ht.1, ht.2.trans hbT⟩
  exact hf.coeFn_toLp.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

theorem aestronglyMeasurable_add_timeMeasure
    {X : Type*} [TopologicalSpace X] {T c d : ℝ} {f : ℝ → X}
    (hf : AEStronglyMeasurable f (timeMeasure T)) (hc : 0 ≤ c) (hd : d ≤ T) :
    AEStronglyMeasurable (fun t => f (t + c)) (timeMeasure (d - c)) := by
  have hI : Icc c d ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨hc.trans ht.1, ht.2.trans hd⟩
  have h := (hf.restrict (s := Icc c d)).comp_quasiMeasurePreserving
    (measurePreserving_add_right_timeMeasure_restrict hI).quasiMeasurePreserving
  simpa only [Function.comp_def, add_comm c] using h

theorem memLp_add_timeMeasure
    {X : Type*} [TopologicalSpace X] [ContinuousENorm X]
    {p : ℝ≥0∞} {T c d : ℝ} {f : ℝ → X}
    (hf : MemLp f p (timeMeasure T)) (hc : 0 ≤ c) (hd : d ≤ T) :
    MemLp (fun t => f (t + c)) p (timeMeasure (d - c)) := by
  have hI : Icc c d ⊆ Icc (0 : ℝ) T :=
    fun _ ht => ⟨hc.trans ht.1, ht.2.trans hd⟩
  have h := (hf.restrict (Icc c d)).comp_measurePreserving
    (measurePreserving_add_right_timeMeasure_restrict hI)
  simpa only [Function.comp_def, add_comm c] using h

theorem timeL2.toLp_add_eq_slice
    {X : Type*} [NormedAddCommGroup X] {T c d : ℝ} {f : ℝ → X}
    (hf : MemLp f 2 (timeMeasure T)) (hc : 0 ≤ c) (hd : d ≤ T) :
    (memLp_add_timeMeasure hf hc hd).toLp (fun t => f (t + c)) =
      timeL2.slice (hf.toLp f) c d hc hd := by
  apply Lp.ext
  filter_upwards [(memLp_add_timeMeasure hf hc hd).coeFn_toLp,
    timeL2.slice_coe (hf.toLp f) c d hc hd,
    ae_add_right_timeMeasure hc hd hf.coeFn_toLp] with t ht hs hf'
  exact ht.trans (hf'.symm.trans hs.symm)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
