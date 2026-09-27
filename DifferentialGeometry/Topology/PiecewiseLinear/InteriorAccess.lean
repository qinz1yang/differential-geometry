/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifoldWithBoundary.exists_openSegment_subset_interior {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ K.space) :
    ∃ q ∈ interior K.space, openSegment ℝ p q ⊆ interior K.space := by
  obtain ⟨s, hs, hps⟩ := K.mem_space_iff.mp hp
  obtain ⟨t, ht, hst, hcard⟩ := hK.exists_face_superset_card_eq hs
  have hT := isPLBall_convexHull_of_affineIndependent t (K.indep ht) hcard
  obtain ⟨q, hq⟩ := hT.interior_nonempty
  have hsub := interior_mono (K.convexHull_subset_space ht)
  refine ⟨q, hsub hq, ?_⟩
  exact ((convex_convexHull ℝ _).openSegment_self_interior_subset_interior
    (convexHull_mono (Finset.coe_subset.mpr hst) hps) hq).trans hsub

theorem IsPLBall.exists_openSegment_subset_interior {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hD : IsPLBall (n + 1) D)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ D) :
    ∃ q ∈ interior D, openSegment ℝ p q ⊆ interior D := by
  obtain ⟨K, hfin, hKD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  have hK : IsPLBall (n + 1) K.space := hKD.symm ▸ hD
  simpa only [hKD] using hK.isCombinatorialManifoldWithBoundary.exists_openSegment_subset_interior
    (hKD.symm ▸ hp)

theorem IsPLBall.polyAccessible_interior {D : Set Schoenflies.Plane} (hD : IsPLBall 2 D)
    {p : Schoenflies.Plane} (hp : p ∈ D) : Schoenflies.PolyAccessible (interior D) p := by
  obtain ⟨q, hq, hseg⟩ := hD.exists_openSegment_subset_interior hp
  exact Schoenflies.PolyAccessible.of_openSegment hq hseg

theorem IsPLBall.exists_isCrosscut {D : Set Schoenflies.Plane} (hD : IsPLBall 2 D)
    {p q : Schoenflies.Plane} (hp : p ∈ frontier D) (hq : q ∈ frontier D) (hpq : p ≠ q) :
    ∃ A : Set Schoenflies.Plane, Schoenflies.IsCrosscut (frontier D) A p q := by
  have hfront : frontier D ⊆ D := hD.isPolyhedron.isClosed.frontier_subset
  obtain ⟨A, hpoly, harc, hint⟩ := Schoenflies.exists_simple_arc_of_polyAccessible
    isOpen_interior hD.isConnected_interior.isPreconnected hpq
    (hD.polyAccessible_interior (hfront hp)) (hD.polyAccessible_interior (hfront hq))
  refine ⟨A, isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier,
    harc, hpoly, hp, hq, ?_⟩
  rwa [← hD.interior_eq_inside_frontier]

end DifferentialGeometry.Topology.PiecewiseLinear
