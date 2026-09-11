import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory

theorem tendsto_integral_of_tendsto_lintegral_pos_neg
    {ι X : Type*} [MeasurableSpace X] {l : Filter ι}
    {μs : ι → Measure X} {μ : Measure X} {F : ι → X → ℝ} {f : X → ℝ}
    (hF : ∀ᶠ i in l, AEStronglyMeasurable (F i) (μs i))
    (hf : Integrable f μ)
    (hpos : Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (F i x) ∂μs i) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)))
    (hneg : Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (-F i x) ∂μs i) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (-f x) ∂μ))) :
    Tendsto (fun i => ∫ x, F i x ∂μs i) l (𝓝 (∫ x, f x ∂μ)) := by
  have hpfin := hf.lintegral_lt_top.ne
  have hnfin := hf.neg.lintegral_lt_top.ne
  have hint : ∀ᶠ i in l, Integrable (F i) (μs i) := by
    filter_upwards [hF, hpos.eventually_ne hpfin, hneg.eventually_ne hnfin] with i hi hp hn
    have hpInt := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp_aemeasurable hi.aemeasurable) hp
    have hnInt := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp_aemeasurable hi.neg.aemeasurable) hn
    convert hpInt.sub hnInt using 1
    ext x
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, ENNReal.toReal_ofReal',
      max_zero_sub_max_neg_zero_eq_self]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  apply Tendsto.congr' (hint.mono fun i hi =>
    (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm)
  exact ((ENNReal.tendsto_toReal hpfin).comp hpos).sub
    ((ENNReal.tendsto_toReal hnfin).comp hneg)

end MeasureTheory
