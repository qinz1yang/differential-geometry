import DifferentialGeometry.Geometry.Comparison.HingeDirections
import DifferentialGeometry.Topology.MetricSpace.PerimeterBufferSegment

set_option autoImplicit false

open Set Metric Filter Topology

namespace Metric

open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_consistent_endpoint_representatives_of_eight_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball p (8 * R))] :
    ∃ σ : ∀ x y : ball p R, x.val ≠ y.val → GeodesicRepresentative x.val,
      (∀ x y hxy, (σ x y hxy).length = dist x.val y.val ∧
        (σ x y hxy).path (dist x.val y.val) = y.val ∧
        ∀ t ∈ Icc (0 : ℝ) (dist x.val y.val), (σ x y hxy).path t ∈ ball p (2 * R)) ∧
      ∀ (x a y : ball p R) (ha : x.val ≠ a.val) (hy : x.val ≠ y.val)
        (hA : HasAnglesAt x.val),
        letI : HasAnglesAt x.val := hA
        ∃ H : MinimizingHinge a.val y.val,
          H.center = x.val ∧
          (∀ t : ℝ, IccExtend dist_nonneg H.left t = (σ x a ha).path t) ∧
          (∀ t : ℝ, IccExtend dist_nonneg H.right t = (σ x y hy).path t) ∧
          ∀ κ : ℝ, 0 ≤ κ →
            H.germAngle κ = dist (σ x y hy).direction (σ x a ha).direction := by
  classical
  have hsegments (x y : ball p R) :
      ∃ γ : Icc (0 : ℝ) (dist x.val y.val) → X, Isometry γ ∧
        γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x.val ∧
        γ ⟨dist x.val y.val, ⟨dist_nonneg, le_rfl⟩⟩ = y.val ∧
        ∀ t, γ t ∈ ball p (2 * R) := by
    have hperim : (dist x.val p + dist y.val p + dist x.val y.val) / 2 < 2 * R := by
      have hx : dist x.val p < R := x.property
      have hy : dist y.val p < R := y.property
      have hd := dist_triangle x.val p y.val
      rw [dist_comm p y.val] at hd
      linarith
    obtain ⟨γ, hγ, hγ0, hγ1, hmem⟩ :=
      exists_isometric_segment_in_closedBall_of_half_perimeter_lt hcurves p
        (L := 8 * R) isClosed_closedBall.isComplete (hperim.trans (by linarith))
    refine ⟨γ, hγ, hγ0, hγ1, fun t => ?_⟩
    exact lt_of_le_of_lt (hmem t) hperim
  choose γ hγ hγ0 hγ1 hγmem using hsegments
  let σ : ∀ x y : ball p R, x.val ≠ y.val → GeodesicRepresentative x.val :=
    fun x y hxy =>
      { length := dist x.val y.val
        length_pos := dist_pos.mpr hxy
        curve := γ x y
        isometry := hγ x y
        start := hγ0 x y }
  refine ⟨σ, ?_, ?_⟩
  · intro x y hxy
    refine ⟨rfl, ?_, ?_⟩
    · rw [(σ x y hxy).path_of_mem ⟨dist_nonneg, le_rfl⟩]
      exact hγ1 x y
    · intro t ht
      rw [(σ x y hxy).path_of_mem ht]
      exact hγmem x y _
  · intro x a y ha hy hA
    let : HasAnglesAt x.val := hA
    let H : MinimizingHinge a.val y.val :=
      { center := x.val
        left := γ x a
        right := γ x y
        left_isometry := hγ x a
        right_isometry := hγ x y
        left_zero := hγ0 x a
        right_zero := hγ0 x y
        left_end := hγ1 x a
        right_end := hγ1 x y }
    refine ⟨H, rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    intro κ hκ
    have heq := H.germAngle_eq_dist_directions hκ (dist_pos.mpr ha) (dist_pos.mpr hy)
    change H.germAngle κ = dist (σ x a ha).direction (σ x y hy).direction at heq
    exact heq.trans (dist_comm _ _)

end Metric
