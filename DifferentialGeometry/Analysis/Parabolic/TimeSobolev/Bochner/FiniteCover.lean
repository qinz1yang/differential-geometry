import DifferentialGeometry.Analysis.Integration.Lp.FiniteCover
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeMeasureRestrict
import Mathlib.MeasureTheory.Group.MeasurableEquiv

noncomputable section

open Set MeasureTheory Filter

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem measurePreserving_sub_timeMeasure_restrict
    {T c d : ℝ} (hI : Icc c d ⊆ Icc (0 : ℝ) T) :
    MeasurePreserving (fun t : ℝ => t - c)
      ((timeMeasure T).restrict (Icc c d)) (timeMeasure (d - c)) := by
  have hf : MeasurePreserving (MeasurableEquiv.addLeft c)
      (timeMeasure (d - c)) ((timeMeasure T).restrict (Icc c d)) :=
    measurePreserving_add_right_timeMeasure_restrict hI
  simpa only [MeasurableEquiv.symm_addLeft, MeasurableEquiv.coe_addLeft,
    sub_eq_add_neg, add_comm] using MeasurePreserving.symm (MeasurableEquiv.addLeft c) hf

namespace timeL2

variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Finite ι]

theorem exists_lift_of_finite_slices
    {T : ℝ} (J : X →L[ℝ] Y) (hJ : Function.Injective J) (F : timeL2 Y T)
    (c d : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hdT : ∀ i, d i ≤ T)
    (hcover : ∀ᵐ t ∂timeMeasure T, t ∈ ⋃ i, Icc (c i) (d i))
    (v : ∀ i, timeL2 X (d i - c i))
    (hv : ∀ i, J.compLpL 2 (timeMeasure (d i - c i)) (v i) =
      slice F (c i) (d i) (hc i) (hdT i)) :
    ∃ FH : timeL2 X T, J.compLpL 2 (timeMeasure T) FH = F ∧
      ∀ i, slice FH (c i) (d i) (hc i) (hdT i) = v i := by
  have hI (i : ι) : Icc (c i) (d i) ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨(hc i).trans ht.1, ht.2.trans (hdT i)⟩
  let w (i : ι) : Lp X 2 ((timeMeasure T).restrict (Icc (c i) (d i))) :=
    Lp.compMeasurePreserving (fun t : ℝ => t - c i)
      (measurePreserving_sub_timeMeasure_restrict (hI i)) (v i)
  have hw (i : ι) : (fun t => w i t) =ᵐ[(timeMeasure T).restrict (Icc (c i) (d i))]
      fun t => v i (t - c i) :=
    Lp.coeFn_compMeasurePreserving (v i)
      (measurePreserving_sub_timeMeasure_restrict (hI i))
  have hproj (i : ι) : (fun t => J (w i t))
      =ᵐ[(timeMeasure T).restrict (Icc (c i) (d i))] fun t => F t := by
    have hlocal : (fun s => J (v i s)) =ᵐ[timeMeasure (d i - c i)]
        fun s => F (s + c i) := by
      have h := J.coeFn_compLpL (p := 2) (μ := timeMeasure (d i - c i)) (v i)
      rw [hv i] at h
      exact h.symm.trans (slice_coe F (c i) (d i) (hc i) (hdT i))
    have hpull := (measurePreserving_sub_timeMeasure_restrict (hI i)).quasiMeasurePreserving.ae_eq
      hlocal
    filter_upwards [hw i, hpull] with t hwt hpt
    simpa only [Function.comp_apply, sub_add_cancel, hwt] using hpt
  obtain ⟨FH, hFH, hFHlocal⟩ := exists_lp_lift_of_finite_ae_cover hJ
    (fun i => Icc (c i) (d i)) (fun _ => measurableSet_Icc) hcover w hproj
  refine ⟨FH, ?_, ?_⟩
  · apply Lp.ext
    exact (J.coeFn_compLpL (p := 2) (μ := timeMeasure T) FH).trans hFH
  · intro i
    have hlocal : (fun t => FH t)
        =ᵐ[(timeMeasure T).restrict (Icc (c i) (d i))]
          fun t => v i (t - c i) := (hFHlocal i).trans (hw i)
    have hshift :=
      (measurePreserving_add_right_timeMeasure_restrict (hI i)).quasiMeasurePreserving.ae_eq hlocal
    apply Lp.ext
    filter_upwards [slice_coe FH (c i) (d i) (hc i) (hdT i), hshift] with t hslice htranslated
    simpa only [Function.comp_apply, add_comm (c i), add_sub_cancel_right, hslice]
      using htranslated

end timeL2

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
