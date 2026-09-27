/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusHurewiczOne
import DifferentialGeometry.Topology.PiecewiseLinear.TorusTracePrimitiveHomology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem CarriesFirstHomologyOnto.carriesFundamentalGroupOnto_of_isTopologicalSolidTorus
    {G S : Set E3} (hH : CarriesFirstHomologyOnto G S)
    (hS : IsTopologicalSolidTorus S) (hG : IsPathConnected G) :
    CarriesFundamentalGroupOnto G S := by
  refine ⟨hH.1, fun hGS x γ => ?_⟩
  let i : C(G, S) := ⟨inclusion hGS, continuous_inclusion hGS⟩
  let _ : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hG
  obtain ⟨a, ha⟩ := hH.2 hGS (hurewiczOne (i x) γ).toAdd
  obtain ⟨β, hβ⟩ := hurewiczOne_surjective x (Multiplicative.ofAdd a)
  refine ⟨β, hS.hurewiczOne_injective (i x) ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hurewiczOne_map, hβ]
  exact ha

theorem IsTopologicalSolidTorus.nonempty_fundamentalGroup_equiv_int
    {S : Set E3} (hS : IsTopologicalSolidTorus S) (x : S) :
    Nonempty (FundamentalGroup S x ≃* Multiplicative ℤ) := by
  let _ : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hS.isPathConnected
  obtain ⟨eH⟩ := hS.nonempty_integralSingularHomology_one_equiv_int
  let e : FundamentalGroup S x ≃* Multiplicative (integralSingularHomology 1 S) :=
    MulEquiv.ofBijective (hurewiczOne x)
      ⟨hS.hurewiczOne_injective x, hurewiczOne_surjective x⟩
  exact ⟨e.trans eH.toAddEquiv.toMultiplicative⟩

end DifferentialGeometry.Topology.PiecewiseLinear
