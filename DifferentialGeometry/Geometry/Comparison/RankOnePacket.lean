import DifferentialGeometry.Topology.MetricSpace.AlmostRadialPoint
import DifferentialGeometry.Geometry.Comparison.BalancedMidpoint
import DifferentialGeometry.Geometry.Comparison.PairedPacket

set_option autoImplicit false

open Set Metric Real

namespace Metric

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_nearby_point_of_arbitrarily_short_curves
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    (p : X) {ε : ℝ} (hε : 0 < ε) : ∃ y : X, 0 < dist p y ∧ dist p y < ε := by
  obtain ⟨u, hup⟩ := exists_ne p
  have hD : 0 < dist p u := dist_pos.mpr hup.symm
  let t := min (ε/2) (dist p u/2)
  have ht : 0 < t := lt_min (half_pos hε) (half_pos hD)
  obtain ⟨c, hc, hc0, hc1, _⟩ := hcurves p u 1 zero_lt_one
  obtain ⟨s, hs, _⟩ := exists_first_dist_eq_of_continuous_curve c hc hc0 ht.le
    (by rw [hc1]; exact (min_le_right _ _).trans (half_le_self hD.le))
  exact ⟨c s, hs ▸ ht, hs ▸ ((min_le_left _ _).trans_lt (half_lt_self hε))⟩

end Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_rank_one_packet_in_open_set
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {O : Set X} (hO : IsOpen O) (hne : O.Nonempty) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ x ∈ O, ∃ y ∈ O, ∃ z ∈ O, 0 < dist x y ∧
      PairedComparisonPacket β {z} (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hO x hx
  obtain ⟨y, hL, hLsmall⟩ := exists_nearby_point_of_arbitrarily_short_curves hcurves x
    (lt_min zero_lt_one (half_pos hρ))
  have hL1 : dist x y < 1 := hLsmall.trans_le (min_le_left _ _)
  have hLρ : dist x y < ρ/2 := hLsmall.trans_le (min_le_right _ _)
  have hy : y ∈ O := hball (by rw [mem_ball, dist_comm]; linarith)
  obtain ⟨_, z, _, _, hs, hs', hang⟩ :=
    exists_balanced_midpoint_with_comparison_angle hcurves x y hL hL1.le hβ hβ1
  have hz : z ∈ O := by
    apply hball
    rw [mem_ball, dist_comm]
    have h := hs.trans_le hs'
    linarith
  refine ⟨x, hx, y, hy, z, hz, hL, ?_⟩
  constructor
  · intro p hp i
    have hpz : p = z := mem_singleton_iff.mp hp
    subst p
    exact hang
  · intro p hp i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

end DifferentialGeometry.Geometry.Comparison.Toponogov
