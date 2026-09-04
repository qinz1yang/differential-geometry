import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [CompleteSpace X]

private def tentSlope (T c : Real) (z : X) : Real → X :=
  Set.piecewise (Iic c) (fun _ ↦ c⁻¹ • z)
    (fun _ ↦ -(T - c)⁻¹ • z)

omit [CompleteSpace X] in
private theorem tentSlope_mem (T c : Real) (z : X) :
    MemLp (tentSlope T c z) 2 (timeMeasure T) := by
  exact MemLp.piecewise measurableSet_Iic (memLp_const _)
    (memLp_const _)

namespace timeH1

noncomputable def tent (T c : Real) (z : X) : timeH1 X T :=
  mk 0 ((tentSlope_mem T c z).toLp (tentSlope T c z))

omit [CompleteSpace X] in
theorem tent_deriv (T c : Real) (z : X) :
    (tent T c z).deriv =ᵐ[timeMeasure T] tentSlope T c z := by
  exact (tentSlope_mem T c z).coeFn_toLp

omit [CompleteSpace X] in
@[simp] theorem tent_init (T c : Real) (z : X) :
    (tent T c z).init = 0 := rfl

omit [CompleteSpace X] in
theorem tent_deriv_left {T c : Real} (z : X) (hcT : c < T) :
    (tent T c z).deriv =ᵐ[volume.restrict (Ioo (0 : Real) c)]
      fun _ ↦ c⁻¹ • z := by
  have hsub : Ioo (0 : Real) c ⊆ Icc (0 : Real) T := by
    intro t ht
    exact ⟨ht.1.le, ht.2.le.trans hcT.le⟩
  have hle : volume.restrict (Ioo (0 : Real) c) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have h := (tent_deriv T c z).filter_mono (ae_mono hle)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht htc
  rw [ht]
  exact (Iic c).piecewise_eq_of_mem _ _
    (show t ∈ Iic c from htc.2.le)

omit [CompleteSpace X] in
theorem tent_deriv_right {T c : Real} (z : X) (hc : 0 < c) :
    (tent T c z).deriv =ᵐ[volume.restrict (Ioo c T)]
      fun _ ↦ -(T - c)⁻¹ • z := by
  have hsub : Ioo c T ⊆ Icc (0 : Real) T := by
    intro t ht
    exact ⟨hc.le.trans ht.1.le, ht.2.le⟩
  have hle : volume.restrict (Ioo c T) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have h := (tent_deriv T c z).filter_mono (ae_mono hle)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht htc
  rw [ht]
  exact (Iic c).piecewise_eq_of_notMem _ _
    (show t ∉ Iic c from not_le.mpr htc.1)

theorem tent_toFun_left {T c t : Real} (z : X) (hcT : c < T)
    (ht : t ∈ Icc (0 : Real) c) :
    (tent T c z).toFun t = (t / c) • z := by
  have hsub : uIoc (0 : Real) t ⊆ Icc (0 : Real) T := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, (hs.2.trans ht.2).trans hcT.le⟩
  have hle : volume.restrict (uIoc (0 : Real) t) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have hder := (tent_deriv T c z).filter_mono (ae_mono hle)
  have hint : (∫ s in (0 : Real)..t, (tent T c z).deriv s) =
      ∫ _ in (0 : Real)..t, c⁻¹ • z := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hder, ae_restrict_mem measurableSet_uIoc] with s hs hst
    rw [hs]
    have hsc : s ≤ c := by
      rw [uIoc_of_le ht.1] at hst
      exact hst.2.trans ht.2
    exact (Iic c).piecewise_eq_of_mem _ _
      (show s ∈ Iic c from hsc)
  rw [toFun_apply, tent_init, hint, intervalIntegral.integral_const,
    zero_add, sub_zero, smul_smul, div_eq_mul_inv]

theorem tent_node {T c : Real} (z : X) (hc : 0 < c) (hcT : c < T) :
    (tent T c z).toFun c = z := by
  rw [tent_toFun_left z hcT ⟨hc.le, le_rfl⟩, div_self hc.ne', one_smul]

theorem tent_toFun_right {T c t : Real} (z : X) (hc : 0 < c) (hcT : c < T)
    (ht : t ∈ Icc c T) :
    (tent T c z).toFun t = ((T - t) / (T - c)) • z := by
  have hc_mem : c ∈ Icc (0 : Real) T := ⟨hc.le, hcT.le⟩
  have ht_mem : t ∈ Icc (0 : Real) T := ⟨hc.le.trans ht.1, ht.2⟩
  have hsub : uIoc c t ⊆ Icc (0 : Real) T := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    exact ⟨hc.le.trans hs.1.le, hs.2.trans ht.2⟩
  have hle : volume.restrict (uIoc c t) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have hder := (tent_deriv T c z).filter_mono (ae_mono hle)
  have hint : (∫ s in c..t, (tent T c z).deriv s) =
      ∫ _ in c..t, -(T - c)⁻¹ • z := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hder, ae_restrict_mem measurableSet_uIoc] with s hs hst
    rw [hs]
    have hcs : c < s := by
      rw [uIoc_of_le ht.1] at hst
      exact hst.1
    exact (Iic c).piecewise_eq_of_notMem _ _
      (show s ∉ Iic c from not_le.mpr hcs)
  have hdiff := (tent T c z).toFun_sub_toFun hc_mem ht_mem
  rw [tent_node z hc hcT, hint, intervalIntegral.integral_const] at hdiff
  have hut : (tent T c z).toFun t =
      z + (t - c) • (-(T - c)⁻¹ • z) :=
    sub_eq_iff_eq_add'.mp hdiff
  rw [hut, smul_smul]
  have hcoef : 1 + (t - c) * (-(T - c)⁻¹) =
      (T - t) / (T - c) := by
    have hTc : T - c ≠ 0 := sub_ne_zero.mpr hcT.ne'
    field_simp [hTc]
    ring
  calc
    z + ((t - c) * (-(T - c)⁻¹)) • z =
        (1 + (t - c) * (-(T - c)⁻¹)) • z := by
      rw [add_smul, one_smul]
    _ = ((T - t) / (T - c)) • z := by rw [hcoef]

theorem tent_end {T c : Real} (z : X) (hc : 0 < c) (hcT : c < T) :
    (tent T c z).toFun T = 0 := by
  rw [tent_toFun_right z hc hcT ⟨hcT.le, le_rfl⟩, sub_self, zero_div,
    zero_smul]

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
