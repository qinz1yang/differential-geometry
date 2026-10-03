import DifferentialGeometry.Topology.PiecewiseLinear.CoveringLift
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn
import Mathlib.Topology.Homeomorph.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section

universe u

theorem IsPLCellOn.isConnected {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) :
    IsConnected S := by
  obtain ⟨P, r, v, hr, hv, rfl, -⟩ := hS
  have hP : IsConnected P := by
    have h1 : IsConnected (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) :=
      (Convexity.StdSimplex.convex_coordinateSet ℝ _).isConnected ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (d + 1))⟩
    have h2 := h1.image r hr.isPiecewiseAffineOn.continuousOn
    rwa [hr.bijOn.image_eq] at h2
  exact hP.image v hv.continuousOn

end

theorem IsPLCellOn.simplyConnectedSpace {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {D B : Set M}
    (hD : IsPLCellOn d D B) : SimplyConnectedSpace D := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hD
  have hP : IsPLBall d P := ⟨r, hr⟩
  let _ := hP.simplyConnectedSpace
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP.isPolyhedron.isCompact
  let e := Equiv.Set.imageOfInjOn u P hu.injOn
  have he : Continuous e := hu.continuousOn.domRestrict.subtype_mk _
  let φ : P ≃ₜ u '' P := he.homeoOfEquivCompactToT2
  exact φ.symm.toHomotopyEquiv.simplyConnectedSpace

end DifferentialGeometry.Topology.PiecewiseLinear
