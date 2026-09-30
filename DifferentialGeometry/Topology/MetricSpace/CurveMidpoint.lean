import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

namespace Metric

open Set
open scoped ENNReal

variable {X : Type*} [MetricSpace X]

theorem edist_add_edist_le_eVariationOn (c : unitInterval → X) (t : unitInterval) :
    edist (c 0) (c t) + edist (c t) (c 1) ≤ eVariationOn c univ := by
  have hleft := eVariationOn.edist_le c (s := Icc (0 : unitInterval) t)
    (show (0 : unitInterval) ∈ Icc 0 t from ⟨le_rfl, unitInterval.nonneg'⟩)
    (show t ∈ Icc 0 t from ⟨unitInterval.nonneg', le_rfl⟩)
  have hright := eVariationOn.edist_le c (s := Icc t (1 : unitInterval))
    (show t ∈ Icc t 1 from ⟨le_rfl, unitInterval.le_one'⟩)
    (show (1 : unitInterval) ∈ Icc t 1 from ⟨unitInterval.le_one', le_rfl⟩)
  have hsum := eVariationOn.Icc_add_Icc c (s := univ) (unitInterval.nonneg') (unitInterval.le_one') (mem_univ t)
  have hall : Icc (0 : unitInterval) 1 = univ := by
    ext s
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
  simp only [univ_inter, hall] at hsum
  exact (add_le_add hleft hright).trans_eq hsum

theorem exists_approximate_midpoint_of_curve {a b : X} {h : ℝ} (hh : 0 < h)
    (c : unitInterval → X) (hc : Continuous c) (ha : c 0 = a) (hb : c 1 = b)
    (hlen : eVariationOn c univ < ENNReal.ofReal (dist a b + 2 * h)) :
    ∃ z : X, dist a z < dist a b / 2 + h ∧ dist b z < dist a b / 2 + h := by
  obtain ⟨t, ht⟩ := intermediate_value_univ₂
    (a := (0 : unitInterval)) (b := (1 : unitInterval))
    (continuous_const.dist hc : Continuous fun s => dist a (c s))
    (continuous_const.dist hc : Continuous fun s => dist b (c s))
    (by simp [ha]) (by simp [hb])
  have hbound := (edist_add_edist_le_eVariationOn c t).trans_lt hlen
  rw [ha, hb, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (by linarith [dist_nonneg (x := a) (y := b)])).mp hbound
  rw [dist_comm (c t) b] at hreal
  exact ⟨c t, by linarith, by linarith⟩

theorem approximate_midpoints_of_arbitrarily_short_curves
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) :
    ∀ a b : X, ∀ h : ℝ, 0 < h →
      ∃ z : X, dist a z ≤ dist a b / 2 + h ∧ dist b z ≤ dist a b / 2 + h := by
  intro a b h hh
  obtain ⟨c, hc, ha, hb, hlen⟩ := hcurves a b (2 * h) (by linarith)
  obtain ⟨z, haz, hbz⟩ := exists_approximate_midpoint_of_curve hh c hc ha hb hlen
  exact ⟨z, haz.le, hbz.le⟩

end Metric
