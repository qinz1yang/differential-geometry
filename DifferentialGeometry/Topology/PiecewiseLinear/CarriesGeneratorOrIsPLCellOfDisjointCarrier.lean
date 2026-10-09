/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier
    {S K G : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCombinatorialSolidTorus S)
    (hK : IsPLSphere 1 K) (hKS : K ⊆ frontier S) (hKgen : CarriesFundamentalGroupOnto K S)
    (hG : IsPLSphere 1 G) (hGS : G ⊆ frontier S) (hGK : Disjoint G K) :
    CarriesFundamentalGroupOnto G S ∨
      ∃ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
          G = r '' stdSimplexBoundary 2 := by
  by_cases hsep : IsPreconnected (frontier S \ G)
  · exact Or.inl (hS.carriesFundamentalGroupOnto_of_isPreconnected_sdiff hK hKS hKgen hG hGS hGK
      hsep)
  · exact Or.inr
      (hS.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hG hGS hsep)

end DifferentialGeometry.Topology.PiecewiseLinear
