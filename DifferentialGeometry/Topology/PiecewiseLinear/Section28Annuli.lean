/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem moise286 : Moise286 := by
  classical
  intro S hS n G hn hG hGS hdisj hess x hx
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G hn hG hGS hdisj hess
  have hG_eq : G = fun i => f '' (J ×ˢ {q i}) := funext hfamily
  rw [hG_eq] at hx ⊢
  obtain ⟨i, j, hij, ρ, hρ, hzero, hone⟩ :=
    exists_annulus_parametrization_of_product_circle_cut hJ hQ hf hn q hq hinj hx
  exact ⟨i, j, hij, J, ρ, hJ, hρ, hzero, hone⟩

end DifferentialGeometry.Topology.PiecewiseLinear
