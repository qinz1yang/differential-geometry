/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isPLCirclePositive_frontier_iff_of_subdisk
    {P D : Set Plane} (hP : IsPLBall 2 P) (hD : IsPLBall 2 D) (hDP : D ⊆ P)
    {f : Plane → Plane} (hf : IsPLHomeomorphOn f P P) (hfD : f '' D = D) :
    IsPLCirclePositive (frontier D) f ↔ IsPLCirclePositive (frontier P) f := by
  have hg : IsPLHomeomorphOn f D D := by
    have h := hf.restrict hD.isPolyhedron hDP
    rwa [hfD] at h
  have hPf : f '' frontier P = frontier P :=
    hf.image_frontier rfl hP.isPolyhedron.isClosed hP.isPolyhedron.isClosed
  have hDf : f '' frontier D = frontier D :=
    hg.image_frontier rfl hD.isPolyhedron.isClosed hD.isPolyhedron.isClosed
  have hPs : BijOn f (frontier P) (frontier P) :=
    ⟨fun _ hx => hPf ▸ mem_image_of_mem f hx,
      hf.bijOn.injOn.mono hP.isPolyhedron.isClosed.frontier_subset, hPf.ge⟩
  have hDs : BijOn f (frontier D) (frontier D) :=
    ⟨fun _ hx => hDf ▸ mem_image_of_mem f hx,
      hg.bijOn.injOn.mono hD.isPolyhedron.isClosed.frontier_subset, hDf.ge⟩
  have hPB : MapsTo f (interior P) (interior P) :=
    fun _ hx => (hf.image_interior rfl) ▸ mem_image_of_mem f hx
  have hDB : MapsTo f (interior D) (interior D) :=
    fun _ hx => (hg.image_interior rfl) ▸ mem_image_of_mem f hx
  obtain ⟨x, hx⟩ := hD.interior_nonempty
  have hxP : x ∈ interior P := interior_mono hDP hx
  have hinner := isPLCirclePositive_frontier_iff_orientationParity_eq_zero hD
    hg.isPiecewiseAffineOn.continuousOn hg.bijOn.injOn hDB hDs hx
  have houter := isPLCirclePositive_frontier_iff_orientationParity_eq_zero hP
    hf.isPiecewiseAffineOn.continuousOn hf.bijOn.injOn hPB hPs hxP
  have hsame := embeddingOrientationParity_congr isOpen_interior isOpen_interior
    (hg.isPiecewiseAffineOn.continuousOn.mono interior_subset) (hg.bijOn.injOn.mono interior_subset)
    (hf.isPiecewiseAffineOn.continuousOn.mono interior_subset) (hf.bijOn.injOn.mono interior_subset)
    hx hxP Filter.EventuallyEq.rfl
  rw [hinner, houter, hsame]

end DifferentialGeometry.Topology.PiecewiseLinear
