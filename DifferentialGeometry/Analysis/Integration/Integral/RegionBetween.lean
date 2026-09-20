import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

namespace MeasureTheory

theorem integral_regionBetween_eq_integral_intervalIntegral
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure α} [SFinite μ]
    {a b : α → ℝ} {s : Set α} (ha : Measurable a) (hb : Measurable b)
    (hs : MeasurableSet s) (hab : ∀ x ∈ s, a x ≤ b x)
    {F : α × ℝ → V} (hF : IntegrableOn F (regionBetween a b s) (μ.prod volume)) :
    (∫ p in regionBetween a b s, F p ∂μ.prod volume) =
      ∫ x in s, (∫ y in a x..b x, F (x, y)) ∂μ := by
  have hset := measurableSet_regionBetween ha hb hs
  rw [← integral_indicator hset, integral_prod _ ((integrable_indicator_iff hset).mpr hF),
    ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    have heq : (fun y => (regionBetween a b s).indicator F (x, y)) =
        (Ioo (a x) (b x)).indicator (fun y => F (x, y)) := by
      funext y
      by_cases hy : y ∈ Ioo (a x) (b x)
      · rw [Set.indicator_of_mem (show (x, y) ∈ regionBetween a b s from ⟨hx, hy⟩),
          Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ regionBetween a b s from fun h => hy h.2),
          Set.indicator_of_notMem hy]
    rw [heq, integral_indicator measurableSet_Ioo, setIntegral_congr_set Ioo_ae_eq_Ioc,
      intervalIntegral.integral_of_le (hab x hx)]
  · rw [Set.indicator_of_notMem hx]
    have heq : (fun y => (regionBetween a b s).indicator F (x, y)) = fun _ => 0 := by
      funext y
      apply Set.indicator_of_notMem
      exact fun hy => hx hy.1
    rw [heq, integral_zero]

end MeasureTheory
