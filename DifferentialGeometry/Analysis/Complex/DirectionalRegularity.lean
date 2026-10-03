import DifferentialGeometry.Analysis.Complex.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod

namespace Homeomorph

private theorem horizontal_line_curve (h : ℂ → ℂ) (x y : ℝ) :
    (fun t : ℝ => h ((⟨x, y⟩ : ℂ) + t • (1 : ℂ))) =
      (fun t : ℝ => h (⟨x + t, y⟩ : ℂ)) := by
  funext t
  congr 1
  apply Complex.ext <;> simp

private theorem lineDifferentiableAt_horizontal_iff (h : ℂ → ℂ) (x y : ℝ) :
    LineDifferentiableAt ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) ↔
      DifferentiableAt ℝ (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x := by
  rw [LineDifferentiableAt, horizontal_line_curve]
  simpa only [add_zero] using
    (differentiableAt_comp_add_left (𝕜 := ℝ)
      (f := fun t : ℝ => h (⟨t, y⟩ : ℂ)) (x := (0 : ℝ)) x)

private theorem lineDeriv_horizontal (h : ℂ → ℂ) (x y : ℝ) :
    lineDeriv ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) =
      deriv (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x := by
  rw [lineDeriv, horizontal_line_curve]
  simpa only [add_zero] using
    (deriv_comp_const_add (fun t : ℝ => h (⟨t, y⟩ : ℂ)) x 0)

private theorem measurableSet_horizontal_regular (h : ℂ ≃ₜ ℂ) (a b c d : ℝ) :
    MeasurableSet {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} := by
  have hd : MeasurableSet {z : ℂ | LineDifferentiableAt ℝ h z (1 : ℂ)} :=
    measurableSet_lineDifferentiableAt h.continuous
  have hn : MeasurableSet {z : ℂ | lineDeriv ℝ h z (1 : ℂ) ≠ 0} :=
    ((measurable_lineDeriv h.continuous) (measurableSet_singleton (0 : ℂ))).compl
  exact (isOpen_Ioo.measurableSet.preimage Complex.continuous_re.measurable).inter
    ((isOpen_Ioo.measurableSet.preimage Complex.continuous_im.measurable).inter (hd.inter hn))

theorem volume_pos_lineDeriv_ne_zero_horizontal
    (h : ℂ ≃ₜ ℂ) (κ : ℝ)
    (hdisks : ∀ z : ℂ, ∀ r : ℝ, 0 < r → ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h z) ρ ⊆ h '' Metric.ball z r ∧
      h '' Metric.closedBall z r ⊆ Metric.closedBall (h z) R ∧ R ≤ κ * ρ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    0 < MeasureTheory.volume {z : ℂ | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
      LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0} := by
  let S : Set ℂ := {z | z.re ∈ Set.Ioo a b ∧ z.im ∈ Set.Ioo c d ∧
    LineDifferentiableAt ℝ h z (1 : ℂ) ∧ lineDeriv ℝ h z (1 : ℂ) ≠ 0}
  have hS : MeasurableSet S := measurableSet_horizontal_regular h a b c d
  by_contra hnpos
  have hzero : MeasureTheory.volume S = 0 := le_antisymm (le_of_not_gt hnpos) bot_le
  let ψ : ℝ × ℝ → ℂ := fun p => ⟨p.2, p.1⟩
  have hψ : MeasureTheory.MeasurePreserving ψ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume := by
    exact (MeasureTheory.MeasurePreserving.symm Complex.measurableEquivRealProd
      Complex.volume_preserving_equiv_real_prod).comp MeasureTheory.Measure.measurePreserving_swap
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      (ψ ⁻¹' S) = 0 := (hψ.measure_preimage hS.nullMeasurableSet).trans hzero
  have hsections := MeasureTheory.Measure.measure_ae_null_of_prod_null hprod
  have hgood : ∀ᵐ y : ℝ ∂MeasureTheory.volume.restrict (Set.Ioo c d),
      AbsolutelyContinuousOnInterval (fun x : ℝ => h (⟨x, y⟩ : ℂ)) a b ∧
        MeasureTheory.volume ((fun x : ℝ => (⟨x, y⟩ : ℂ)) ⁻¹' S) = 0 := by
    filter_upwards [h.ae_absolutelyContinuousOnInterval_horizontal κ hdisks a b c d,
      MeasureTheory.ae_restrict_of_ae hsections] with y hy hnull
    exact ⟨hy, hnull⟩
  have hheightpos : MeasureTheory.volume (Set.Ioo c d) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)).ne'
  obtain ⟨y, hycd, hyAC, hyzero⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hheightpos hgood
  let g (x : ℝ) := h (⟨x, y⟩ : ℂ)
  have hdiff := hyAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hnot : ∀ᵐ x : ℝ ∂MeasureTheory.volume, (⟨x, y⟩ : ℂ) ∉ S :=
    (MeasureTheory.measure_eq_zero_iff_ae_notMem).mp hyzero
  have hae0 : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ∈ Set.uIcc a b → HasDerivAt g 0 x := by
    have hna : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ a := by simp [MeasureTheory.ae_iff]
    have hnb : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ b := by simp [MeasureTheory.ae_iff]
    filter_upwards [hdiff, hnot, hna, hnb] with x hdx hns hxa hxb
    intro hx
    have hxIcc : x ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab.le] using hx
    have hxIoo : x ∈ Set.Ioo a b :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxa), lt_of_le_of_ne hxIcc.2 hxb⟩
    have hdx' : DifferentiableAt ℝ g x := hdx hx
    have hline : LineDifferentiableAt ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) :=
      (lineDifferentiableAt_horizontal_iff h x y).mpr hdx'
    have hder : lineDeriv ℝ h (⟨x, y⟩ : ℂ) (1 : ℂ) = 0 := by
      by_contra hne
      exact hns ⟨hxIoo, hycd, hline, hne⟩
    have hgzero : deriv g x = 0 := by
      rw [← lineDeriv_horizontal h x y]
      exact hder
    rw [← hgzero]
    exact hdx'.hasDerivAt
  obtain ⟨w, hw⟩ := hyAC.const_of_ae_hasDerivAt_zero hae0
  have heq : h (⟨a, y⟩ : ℂ) = h (⟨b, y⟩ : ℂ) :=
    (hw a (Set.left_mem_uIcc)).trans (hw b (Set.right_mem_uIcc)).symm
  have hab' : a = b := congrArg Complex.re (h.injective heq)
  exact hab.ne hab'

end Homeomorph
