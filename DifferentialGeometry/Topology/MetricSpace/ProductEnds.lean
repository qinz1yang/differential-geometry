import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace Metric

theorem connectedComponentIn_compl_prod_eq_of_unbounded
    {Y : Type*} [MetricSpace Y] [PreconnectedSpace Y]
    (hY : ¬ Bornology.IsBounded (univ : Set Y))
    {K : Set (ℝ × Y)} (hK : Bornology.IsBounded K) {a b : ℝ × Y}
    (ha : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hb : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b)) :
    connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  classical
  let y₀ := a.2
  obtain ⟨R, hR, hKR⟩ := hK.subset_ball_lt 0 (0, y₀)
  have hKbound (x : ℝ × Y) (hx : x ∈ K) : |x.1| < R ∧ dist x.2 y₀ < R := by
    simpa [Prod.dist_eq, Real.dist_eq, max_lt_iff] using hKR hx
  have hfar : ∃ y : Y, R < dist y y₀ := by
    by_contra! h
    exact hY (isBounded_closedBall.subset (fun y _ => h y))
  obtain ⟨z, hz⟩ := hfar
  have hhor (t : ℝ) (ht : R < |t|) (y₁ y₂ : Y) :
      connectedComponentIn Kᶜ (t, y₁) = connectedComponentIn Kᶜ (t, y₂) := by
    have hconn : IsPreconnected (range (fun y : Y => (t, y))) :=
      isPreconnected_range (continuous_const.prodMk continuous_id)
    have hsub : range (fun y : Y => (t, y)) ⊆ Kᶜ := by
      rintro _ ⟨y, rfl⟩ hk
      exact (not_lt_of_ge ht.le) (hKbound (t, y) hk).1
    exact connectedComponentIn_eq
      ((hconn.subset_connectedComponentIn ⟨y₁, rfl⟩ hsub) ⟨y₂, rfl⟩)
  have hver (y : Y) (hy : R < dist y y₀) (s t : ℝ) :
      connectedComponentIn Kᶜ (s, y) = connectedComponentIn Kᶜ (t, y) := by
    have hconn : IsPreconnected (range (fun t : ℝ => (t, y))) :=
      isPreconnected_range (continuous_id.prodMk continuous_const)
    have hsub : range (fun t : ℝ => (t, y)) ⊆ Kᶜ := by
      rintro _ ⟨t, rfl⟩ hk
      exact (not_lt_of_ge hy.le) (hKbound (t, y) hk).2
    exact connectedComponentIn_eq
      ((hconn.subset_connectedComponentIn ⟨s, rfl⟩ hsub) ⟨t, rfl⟩)
  have hext (x : ℝ × Y) (hx : R < dist x (0, y₀)) :
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ (R + 1, z) := by
    have hx' : R < |x.1| ∨ R < dist x.2 y₀ := by
      simpa [Prod.dist_eq, Real.dist_eq, lt_max_iff] using hx
    rcases hx' with ht | hy
    · exact (hhor x.1 ht x.2 z).trans (hver z hz x.1 (R + 1))
    · exact (hver x.2 hy x.1 (R + 1)).trans
        (hhor (R + 1) (by rw [abs_of_pos (by linarith : 0 < R + 1)]; linarith) x.2 z)
  have hcomponent (x : ℝ × Y)
      (hx : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ (R + 1, z) := by
    have hex : ∃ y ∈ connectedComponentIn Kᶜ x, R < dist y (0, y₀) := by
      by_contra! h
      exact hx (isBounded_closedBall.subset h)
    obtain ⟨y, hy, hyR⟩ := hex
    exact (connectedComponentIn_eq hy).trans (hext y hyR)
  exact (hcomponent a ha).trans (hcomponent b hb).symm

end Metric
