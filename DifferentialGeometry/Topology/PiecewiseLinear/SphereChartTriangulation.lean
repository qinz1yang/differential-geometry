/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SphereCompactReduction
import DifferentialGeometry.Topology.PiecewiseLinear.PartialChartSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarRectTriangulation

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Topology.PlanarJordan

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold (𝓡 2) ∞ S]

theorem exists_finite_chart_triangulation_sphere
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ g : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S, g p = h p ∧
      ∃ a : PartialDiffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) Plane ∞,
        a.source = {p}ᶜ ∧ a.target = univ ∧ ∃ R > 0,
          IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g
            (a.symm '' planeOpenRect (-R) R (-R) R)ᶜ ∧
          ∃ K : Geometry.SimplicialComplex ℝ Plane,
            K.faces.Finite ∧ K.space = planeRect (-R) R (-R) R ∧
            ∀ s ∈ K.faces, ∃ y : S,
              g '' (a.symm '' (⋃ v ∈ s, closedStar K v)) ⊆
                (extChartAtPartialDiffeomorph (𝓡 2) ∞ y).source := by
  obtain ⟨g, hgp, a, has, hat, R, hR, hlocal⟩ :=
    h.exists_smooth_outside_rectangle_sphere p
  obtain ⟨K, hfinite, hspace⟩ := exists_simplicialComplex_planeRect (-R) R (-R) R
  let _ : Finite K.faces := hfinite.to_subtype
  let e := a.symm.toOpenPartialHomeomorph.trans g.toOpenPartialHomeomorph
  have hKe : K.space ⊆ e.source := by
    intro v _
    exact ⟨by change v ∈ a.target; rw [hat]; trivial, trivial⟩
  obtain ⟨L, hL, hLfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_chart_preimages K e hKe
  refine ⟨g, hgp, a, has, hat, R, hR, hlocal, L, hLfinite, hL.space_eq.trans hspace, ?_⟩
  intro s hs
  obtain ⟨y, -, hy⟩ := hstars s hs
  refine ⟨y, ?_⟩
  rintro z ⟨x, ⟨v, hv, rfl⟩, rfl⟩
  exact hy ⟨v, hv, rfl⟩

end Homeomorph
