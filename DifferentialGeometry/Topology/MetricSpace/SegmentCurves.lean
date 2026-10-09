import DifferentialGeometry.Topology.MetricSpace.CurveVariation
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LipschitzWith

variable {X : Type*} [MetricSpace X]

theorem eVariationOn_unitInterval_le {K : ℝ≥0} {f : unitInterval → X} (hLip : LipschitzWith K f) :
    eVariationOn f univ ≤ (K : ℝ≥0∞) := by
  classical
  let g : ℝ → X := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then f ⟨t, ht⟩ else f 0
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t = f ⟨t, ht⟩ := by
    simp only [g, dite_eq_left ht]
  have hgLip : LipschitzOnWith K g (Icc (0 : ℝ) 1) := by
    intro s hs t ht
    rw [hg s hs, hg t ht]
    exact hLip ⟨s, hs⟩ ⟨t, ht⟩
  have hgVar : eVariationOn g (Icc (0 : ℝ) 1) ≤ (K : ℝ≥0∞) := by
    simpa only [sub_zero, ENNReal.ofReal_one, mul_one] using
      Metric.eVariationOn_Icc_le_of_lipschitzOnWith hgLip
  have hh := eVariationOn.comp_le_of_monotoneOn g
    (fun t : unitInterval => (t : ℝ))
    (show MonotoneOn (fun t : unitInterval => (t : ℝ)) univ from fun s _ t _ hst => hst)
    (show MapsTo (fun t : unitInterval => (t : ℝ)) univ (Icc (0 : ℝ) 1) from fun t _ => t.property)
  have heq : g ∘ (fun t : unitInterval => (t : ℝ)) = f := by
    funext t
    exact hg t t.property
  rw [heq] at hh
  exact hh.trans hgVar

end LipschitzWith

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem arbitrarily_short_curves_of_metric_segments
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t) :
    ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η) := by
  intro x y η hη
  obtain ⟨f, hf, hf0, hf1, hdist⟩ := hsegments x y
  have hLip : LipschitzWith (nndist x y) f := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact (hdist s t).le
  refine ⟨f, hf, hf0, hf1, hLip.eVariationOn_unitInterval_le.trans_lt ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos dist_nonneg hη)).mpr (by simpa using hη)

end Metric
