/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceTriangulationSmoothing
import DifferentialGeometry.Topology.PiecewiseLinear.SphereChartTriangulation

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Topology.PlanarJordan

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold (𝓡 2) ∞ S]

theorem exists_diffeomorph_sphere_eq_at
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ D : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S, D p = h p := by
  classical
  obtain ⟨g, hgp, a, has, hat, R, hR, hlocal, K, hfinite, hspace, hstars⟩ :=
    h.exists_finite_chart_triangulation_sphere p
  let _ : Finite K.faces := hfinite.to_subtype
  choose y hy using fun s : K.faces => hstars s.val s.property
  let b (s : K.faces) := extChartAtPartialDiffeomorph (𝓡 2) ∞ (y s)
  have hb (s : K.faces) : g '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source := by
    apply Subset.trans (image_mono (image_mono ?_)) (hy s)
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces s.property
    intro x hx
    exact mem_iUnion₂.mpr ⟨v, hv, mem_iUnion₂.mpr
      ⟨s.val, ⟨s.property, subset_convexHull ℝ _ hv⟩, hx⟩⟩
  have hconv : Convex ℝ K.space := by
    rw [hspace]
    exact (isHPolytope_planeRect (-R) R (-R) R).convex
  have hKa : K.space ⊆ a.target := by rw [hat]; exact subset_univ _
  have hinterior : interior K.space = planeOpenRect (-R) R (-R) R := by
    rw [hspace, interior_planeRect (by linarith) (by linarith)]
  obtain ⟨D, hD⟩ := g.exists_diffeomorph_of_planar_triangulation a K hconv hKa b hb
    (by simpa only [hinterior] using hlocal)
  refine ⟨D, (hD ?_).trans hgp⟩
  rintro ⟨v, hv, hvp⟩
  have hp : p ∈ a.source := hvp ▸ a.map_target (hKa (interior_subset hv))
  simp only [has, mem_compl_iff, mem_singleton_iff, not_true_eq_false] at hp

theorem nonempty_diffeomorph_sphere
    (h : S ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S) := by
  let p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨D, -⟩ := h.symm.exists_diffeomorph_sphere_eq_at p
  exact ⟨D⟩

end Homeomorph
