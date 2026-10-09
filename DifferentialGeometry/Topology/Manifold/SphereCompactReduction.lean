/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfacePointSmoothing
import DifferentialGeometry.Topology.Manifold.PuncturedSphereChart
import DifferentialGeometry.Topology.PlanarJordan.PlanarArcSmoothing

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
  [IsManifold 𝓘(ℝ, Plane) ∞ S]

theorem exists_smooth_outside_rectangle_sphere
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S)
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ g : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ S, g p = h p ∧
      ∃ a : PartialDiffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) Plane ∞,
        a.source = {p}ᶜ ∧ a.target = univ ∧ ∃ R > 0,
          IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g
            (a.symm ''
              DifferentialGeometry.Topology.PlanarJordan.planeOpenRect (-R) R (-R) R)ᶜ := by
  obtain ⟨_, -, -, g, -, hgp, hglocal, -⟩ :=
    h.exists_smooth_at isOpen_univ (mem_univ p)
  obtain ⟨φ, hpφ, hφ⟩ := hglocal
  obtain ⟨a, has, hat⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_smooth_punctured_sphere_chart 2 p
  let C := φ.sourceᶜ
  have hC : IsCompact C := φ.open_source.isClosed_compl.isCompact
  have hCa : C ⊆ a.source := by
    intro x hx
    rw [has]
    intro hxp
    have hxp' : x = p := hxp
    exact hx (hxp'.symm ▸ hpφ)
  have hD : IsCompact (a '' C) :=
    hC.image_of_continuousOn (a.toOpenPartialHomeomorph.continuousOn.mono hCa)
  obtain ⟨R, hR, hDR⟩ := hD.isBounded.subset_ball_lt 0 (0 : Plane)
  have hball : ball (0 : Plane) R ⊆
      DifferentialGeometry.Topology.PlanarJordan.planeOpenRect (-R) R (-R) R := by
    intro v hv
    have h0 := (DifferentialGeometry.Topology.PlanarJordan.planeAbsSub_le_dist v 0 0).trans_lt
      (mem_ball.mp hv)
    have h1 := (DifferentialGeometry.Topology.PlanarJordan.planeAbsSub_le_dist v 0 1).trans_lt
      (mem_ball.mp hv)
    simp only [PiLp.zero_apply, sub_zero, abs_lt] at h0 h1
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  refine ⟨g, hgp, a, has, hat, R, hR, ?_⟩
  intro x
  have hxφ : (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∈ φ.source := by
    by_contra hx
    exact x.property ⟨a x, hball (hDR ⟨x, hx, rfl⟩), a.left_inv (hCa hx)⟩
  exact ⟨φ, hxφ, hφ⟩

end Homeomorph
