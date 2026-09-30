/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem IsTube.exists_centered_splitDisk_parametrization
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) :
    ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D e) ∧
      r '' stdSimplexBoundary 2 = Dbd e ∧
      r (stdCenter 1) = e.centroid ℝ id := by
  obtain ⟨r, hr, hrbd⟩ := ht.splitCell e he hcard
  have hcD : e.centroid ℝ id ∈ D e ∩ K.space := by
    rw [ht.splitMidpoint he hcard]
    exact mem_singleton _
  have hcN : e.centroid ℝ id ∈ interior N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood) hcD.2
  have hcnot : e.centroid ℝ id ∉ Dbd e := by
    intro hcbd
    have hcfr : e.centroid ℝ id ∈ frontier N :=
      ((ht.splitProper e he hcard).symm.subset hcbd).2
    exact disjoint_left.mp disjoint_interior_frontier hcN hcfr
  have hcopen : e.centroid ℝ id ∈ r '' openSimplex (stdVertices 1) := by
    rw [hr.image_openSimplex_stdVertices, ← hrbd]
    exact ⟨hcD.1, hcnot⟩
  obtain ⟨f, hf, hfc⟩ := hr.exists_stdCenter_eq_of_mem_image_openSimplex hcopen
  exact ⟨f, hf, (hf.image_stdSimplexBoundary_congr hr).trans hrbd.symm, hfc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
