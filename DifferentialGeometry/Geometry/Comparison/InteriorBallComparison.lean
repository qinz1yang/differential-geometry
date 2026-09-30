import DifferentialGeometry.Geometry.Comparison.RegionFourPoint
import DifferentialGeometry.Geometry.Comparison.InteriorBufferComparison

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_ball_of_complete_buffer
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {o : X} {L R : ℝ} (hR : 0 < R) (hcomplete : IsComplete (closedBall o L))
    (hbuffer : 81 * R ≤ L) : fourPointComparison κ (ball o R) := by
  apply fourPointComparison_of_endpoint_hinges (T := 4 * R) hκ
  · intro x hx y hy
    obtain ⟨σ, hσ, hσ0, hσ1, _⟩ :=
      exists_isometric_segment_in_ball_of_recentered_complete_buffer
        hcurves hR hcomplete (by rw [dist_self]; linarith) hx hy
    exact ⟨σ, hσ, hσ0, hσ1⟩
  · intro z hz
    exact hlocal z
  · intro p hp
    have hc : IsComplete (closedBall p (80 * R)) :=
      isComplete_closedBall_of_add_dist_le hcomplete (by
        have hd : dist p o < R := hp
        linarith)
    have ht := endpointHingeComparison_of_complete_interior_buffer hκ hcurves hlocal hc
    convert ht using 1; ring
  · intro x hx a ha b hb
    have hxa := dist_triangle x o a
    have hxb := dist_triangle x o b
    rw [dist_comm o a] at hxa
    rw [dist_comm o b] at hxb
    have hx' : dist x o < R := hx
    have ha' : dist a o < R := ha
    have hb' : dist b o < R := hb
    linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
