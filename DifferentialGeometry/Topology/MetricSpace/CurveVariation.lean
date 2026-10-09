import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Order.LiminfLimsup

open Set Filter
open scoped Topology ENNReal NNReal

namespace Metric

theorem eVariationOn_le_liminf_of_pointwise
    {α X ι : Type*} [LinearOrder α] [PseudoEMetricSpace X]
    {l : Filter ι} [l.NeBot] {f : ι → α → X} {g : α → X} {s : Set α}
    (h : ∀ x ∈ s, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    eVariationOn g s ≤ liminf (fun i => eVariationOn (f i) s) l := by
  exact (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr (fun _ hv => eVariationOn.lowerSemicontinuous_aux h hv)

theorem eVariationOn_Icc_le_of_lipschitzOnWith
    {X : Type*} [PseudoEMetricSpace X] {f : ℝ → X} {a b : ℝ} {K : ℝ≥0}
    (h : LipschitzOnWith K f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  have hcomp := h.comp_eVariationOn_le (g := id) (s := Icc a b) (fun _ hx => hx)
  simpa only [Function.comp_id, eVariationOn_id_Icc] using hcomp

end Metric
