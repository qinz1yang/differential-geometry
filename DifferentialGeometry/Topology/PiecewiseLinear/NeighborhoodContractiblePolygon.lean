/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonNullhomotopy

/-! Regular neighborhoods of nullhomotopic polygonal circles are solid tori. -/

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isCombinatorialSolidTorus_derivedNeighborhood_of_nullhomotopic_cycle
    (K P : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite P.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hPK : P.faces ⊆ K.faces)
    (hP : IsCombinatorialManifold 1 P) {v : P.vertices}
    (γ : (SimplicialComplex.edgeGraph P).Walk v v) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = Set.univ)
    (hnull : (pathToCircle (walkPath (γ.map (edgeGraphHom hPK)))).Nullhomotopic) :
    IsCombinatorialSolidTorus (derivedNeighborhood K P).space := by
  have hconn := (isPathConnected_space_of_spanning_cycle hP γ hcyc hspan).isConnected
  have hnull' : (pathToCircle ((walkPath γ).map (spaceInclusion hPK).continuous)).Nullhomotopic :=
    by rwa [walkPath_map] at hnull
  have hor := isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon
    hPK hK hP hconn
    (map_homotopic_refl_of_nullhomotopic_spanning_cycle hP γ hcyc hspan
      (spaceInclusion hPK) hnull')
  exact isCombinatorialSolidTorus_derivedNeighborhood_of_isOrientable K P hK hPK hP hconn hor

end DifferentialGeometry.Topology.PiecewiseLinear
