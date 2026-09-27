/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsPLCellOn.isConnected_boundary_sdiff_of_isPLCellOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {V S D J : Set M} (hV : IsPLCellOn 3 V S) (hD : IsPLCellOn 2 D J) (hDS : D ⊆ S) :
    IsConnected (S \ D) := by
  obtain ⟨P, p, u, hp, hu, hVeq, hSeq⟩ := hV
  have hP : IsPLBall 3 P := ⟨p, hp⟩
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hS : S = u '' frontier P := by
    rw [hSeq, IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hp]
  have hDP : D ⊆ u '' P := by
    rw [← hVeq]
    exact hDS.trans (show S ⊆ V from by rw [hVeq, hS]; exact image_mono hfrP)
  obtain ⟨Q, r, v, hr, hv, hDeq, -⟩ := hD
  let g := Function.invFunOn u P ∘ v
  have hvP : MapsTo v Q (u '' P) := fun z hz =>
    (hDP (by rw [hDeq]; exact mem_image_of_mem v hz))
  have hcancel : ∀ z ∈ Q, u (g z) = v z := fun z hz =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 (hvP hz)
  have hgpl : IsPiecewiseAffineOn g Q := isPLOn_iff_isPiecewiseAffineOn.mp
    (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hv.isPLOn hvP)
  have hginj : InjOn g Q := by
    intro x hx y hy hxy
    exact hv.injOn hx hy ((hcancel x hx).symm.trans
      ((congrArg u hxy).trans (hcancel y hy)))
  have hg : IsPLHomeomorphOn g Q (g '' Q) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      (IsPLBall.isPolyhedron ⟨r, hr⟩) hgpl hginj.bijOn_image
  have hG : IsPLBall 2 (g '' Q) := ⟨g ∘ r, hr.trans hg⟩
  have hGfr : g '' Q ⊆ frontier P := by
    rintro _ ⟨z, hz, rfl⟩
    have hvS := hDS (by rw [hDeq]; exact mem_image_of_mem v hz)
    rw [hS] at hvS
    obtain ⟨a, ha, hav⟩ := hvS
    change Function.invFunOn u P (v z) ∈ frontier P
    rw [← hav, hu.injOn.leftInvOn_invFunOn (hfrP ha)]
    exact ha
  have huG : u '' (g '' Q) = D := by
    rw [hDeq, image_image]
    exact image_congr hcancel
  have hconn := hP.isPLSphere_frontier.isConnected_sdiff_of_isPLBall_two hG hGfr
  have himage : u '' (frontier P \ g '' Q) = S \ D := by
    rw [(hu.injOn.mono hfrP).image_sdiff_subset hGfr, ← hS, huG]
  rw [← himage]
  exact hconn.image u (hu.continuousOn.mono (sdiff_subset.trans hfrP))

end DifferentialGeometry.Topology.PiecewiseLinear
