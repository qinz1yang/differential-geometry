/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPlaneChart
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_halfspace_chart_of_ball_pair
    {P Q D : Set E3} (hP : IsPLBall 3 P) (hQ : IsPLBall 3 Q)
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : P ∩ Q = D) (hDP : D ⊆ frontier P) (hDQ : D ⊆ frontier Q) :
    ∃ e : OpenPartialHomeomorph E3 (Plane × ℝ),
      D \ r '' stdSimplexBoundary 2 ⊆ e.source ∧ e.source ⊆ interior (P ∪ Q) ∧
      (∀ x ∈ e.source, x ∈ P ↔ 0 ≤ (e x).2) ∧
      (∀ x ∈ e.source, x ∈ Q ↔ (e x).2 ≤ 0) ∧
      ∀ x ∈ e.source, x ∈ D ↔ (e x).2 = 0 := by
  obtain ⟨c, hDc, -, -, -, hcfr, hcP⟩ :=
    hP.exists_openPartialHomeomorph_boundary_disk_plane ⟨r, hr⟩ hDP isOpen_univ (subset_univ D)
  let e := c.restr (interior (P ∪ Q))
  have hes : e.source = c.source ∩ interior (P ∪ Q) :=
    c.restr_source' _ isOpen_interior
  have hsource : D \ r '' stdSimplexBoundary 2 ⊆ e.source := by
    intro x hx
    rw [hes]
    exact ⟨hDc hx.1, sdiff_subset_interior_union_of_inter_eq hP hQ hr hmeet hDP hDQ hx⟩
  have hPside (x : E3) (hx : x ∈ e.source) : x ∈ P ↔ 0 ≤ (e x).2 :=
    hcP x ((hes ▸ hx).1)
  have hQside (x : E3) (hx : x ∈ e.source) : x ∈ Q ↔ (e x).2 ≤ 0 := by
    have hx' := hes ▸ hx
    constructor
    · intro hxQ
      by_contra hpos
      have hxP : x ∈ P := (hcP x hx'.1).mpr (le_of_lt (lt_of_not_ge hpos))
      have hz : (e x).2 = 0 := (hcfr x hx'.1).mp (hDP (hmeet ▸ ⟨hxP, hxQ⟩))
      exact hpos (le_of_eq hz)
    · intro hle
      by_cases hxP : x ∈ P
      · have hz : (c x).2 = 0 := le_antisymm hle ((hcP x hx'.1).mp hxP)
        have hxfr := (hcfr x hx'.1).mpr hz
        by_contra hxQ
        apply hxfr.2
        refine interior_maximal (t := interior (P ∪ Q) ∩ Qᶜ) (fun y hy => ?_)
          (isOpen_interior.inter hQ.isPolyhedron.isClosed.isOpen_compl) ⟨hx'.2, hxQ⟩
        exact (interior_subset hy.1).resolve_right hy.2
      · exact (interior_subset hx'.2).resolve_left hxP
  refine ⟨e, hsource, fun _ hx => (hes ▸ hx).2, hPside, hQside, ?_⟩
  intro x hx
  rw [← hmeet, mem_inter_iff, hPside x hx, hQside x hx]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
