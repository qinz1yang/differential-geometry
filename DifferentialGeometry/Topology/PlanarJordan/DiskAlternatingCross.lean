import DifferentialGeometry.Topology.PlanarJordan.AlternatingCross
import DifferentialGeometry.Topology.LevelSet.Disk.StrictLevels

section

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem not_alternating_cross_of_disk_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {u : Plane → ℝ}
    (hu : ContinuousOn u (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, u x = x 0)
    (hmax : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, u x ≤ c) → ∀ x ∈ Ω, u x ≤ c)
    (hmin : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ u x) → ∀ x ∈ Ω, c ≤ u x)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε : ℝ} (hε : 0 < ε)
    (hsource : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source)
    (himage : MapsTo e (Icc (-ε) ε ×ˢ Icc (-ε) ε) (ball (0 : Plane) R))
    (hpositive : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → u (e (0, 0)) < u (e (t, 0)))
    (hnegative : ∀ t ∈ Icc (-ε) ε, t ≠ 0 → u (e (0, t)) < u (e (0, 0))) : False := by
  have hpos := DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle
    hR hu hboundary hmax (u (e (0, 0)))
  have hneg := DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle
    hR hu hboundary hmin (u (e (0, 0)))
  exact not_alternating_cross_of_preconnected_strict_levels isOpen_ball
    (hu.mono ball_subset_closedBall) hpos hneg e hε hsource himage rfl hpositive hnegative

end DifferentialGeometry.Topology.PlanarJordan

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem exists_closed_cross_box_in_source_and_open_image
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (h0 : ((0 : ℝ), (0 : ℝ)) ∈ e.source) {D : Set Plane} (hD : IsOpen D)
    (himage : e (0, 0) ∈ D) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧
      Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ e.source ∧ MapsTo e (Icc (-ε) ε ×ˢ Icc (-ε) ε) D := by
  have he : ContinuousAt e (0 : ℝ × ℝ) := e.continuousOn.continuousAt (e.open_source.mem_nhds h0)
  have hnb : e.source ∩ e ⁻¹' D ∈ 𝓝 (0 : ℝ × ℝ) :=
    inter_mem (e.open_source.mem_nhds h0) (he.preimage_mem_nhds (hD.mem_nhds himage))
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnb
  let ε := min r η
  have hε : 0 < ε := lt_min hr hη
  have hbox : Icc (-ε) ε ×ˢ Icc (-ε) ε ⊆ closedBall (0 : ℝ × ℝ) r := by
    intro p hp
    rw [mem_closedBall, Prod.dist_eq]
    change max (dist p.1 0) (dist p.2 0) ≤ r
    rw [dist_zero_right, dist_zero_right, max_le_iff]
    exact ⟨(abs_le.mpr hp.1).trans (min_le_left _ _),
      (abs_le.mpr hp.2).trans (min_le_left _ _)⟩
  exact ⟨ε, hε, min_le_right _ _, fun p hp => (hrsub (hbox hp)).1,
    fun p hp => (hrsub (hbox hp)).2⟩

theorem not_local_alternating_cross_of_disk_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {u : Plane → ℝ}
    (hu : ContinuousOn u (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, u x = x 0)
    (hmax : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, u x ≤ c) → ∀ x ∈ Ω, u x ≤ c)
    (hmin : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ u x) → ∀ x ∈ Ω, c ≤ u x)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (hsource : ((0 : ℝ), (0 : ℝ)) ∈ e.source) (hcenter : e (0, 0) ∈ ball (0 : Plane) R)
    {η : ℝ} (hη : 0 < η)
    (hpositive : ∀ t : ℝ, 0 < |t| → |t| < η → u (e (0, 0)) < u (e (t, 0)))
    (hnegative : ∀ t : ℝ, 0 < |t| → |t| < η → u (e (0, t)) < u (e (0, 0))) : False := by
  obtain ⟨ε, hε, hεη, hbox, hmap⟩ := exists_closed_cross_box_in_source_and_open_image
    e hsource isOpen_ball hcenter (half_pos hη)
  apply not_alternating_cross_of_disk_maximum_minimum_principle hR hu hboundary hmax hmin
    e hε hbox hmap
  · intro t ht ht0
    exact hpositive t (abs_pos.mpr ht0) ((abs_le.mpr ht).trans_lt (hεη.trans_lt (half_lt_self hη)))
  · intro t ht ht0
    exact hnegative t (abs_pos.mpr ht0) ((abs_le.mpr ht).trans_lt (hεη.trans_lt (half_lt_self hη)))

end DifferentialGeometry.Topology.PlanarJordan

end

end
