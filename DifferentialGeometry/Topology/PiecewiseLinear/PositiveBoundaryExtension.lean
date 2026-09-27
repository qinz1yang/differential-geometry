/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCollarExtension
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_positive_boundary_extension_fixing_compact
    {D K : Set Plane} {δ : Plane → Plane} (hD : IsPLBall 2 D)
    (hK : IsCompact K) (hKD : K ⊆ interior D)
    (hδ : IsPLHomeomorphOn δ (frontier D) (frontier D))
    (hpos : IsPLCirclePositive (frontier D) δ) :
    ∃ H : Plane → Plane, IsPLHomeomorphOn H D D ∧
      EqOn H δ (frontier D) ∧ EqOn H id K := by
  obtain ⟨r, hr⟩ := id hD
  have hUK : Kᶜ ∈ 𝓝ˢ[D] (r '' stdSimplexBoundary 2) := by
    rw [hr.image_stdSimplexBoundary]
    exact mem_nhdsSetWithin.mpr
      ⟨Kᶜ, hK.isClosed.isOpen_compl, fun x hx hxK => hx.2 (hKD hxK), inter_subset_left⟩
  obtain ⟨A, B, ρ, -, hB, hAK, hcover, hρ, hfix, hmeet, -, -⟩ :=
    hr.exists_disk_boundary_collar hUK
  rw [hr.image_stdSimplexBoundary] at hρ hfix hmeet
  have hKB : K ⊆ B := by
    intro x hx
    have hxD : x ∈ D := interior_subset (hKD hx)
    rw [hcover] at hxD
    exact hxD.resolve_right (fun hxA => hAK hxA hx)
  obtain ⟨H, hH, hHB, -, hHδ, -⟩ := exists_isPLHomeomorphOn_of_circle_collars
    (S := fun _ : Unit => frontier D) (A := fun _ : Unit => A)
    (ρ := fun _ : Unit => ρ) (u := fun _ : Unit => δ)
    (fun _ => hD.isPLSphere_frontier) hB.isPolyhedron (fun _ => hρ)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (fun _ => hmeet.subset) (fun _ => hδ) (fun _ => hpos)
  have hHD : IsPLHomeomorphOn H D D := by
    simpa only [iUnion_const, ← hcover] using hH
  refine ⟨H, hHD, ?_, hHB.mono hKB⟩
  intro x hx
  have heq := hHδ () x hx
  rwa [hfix x hx, hfix (δ x) (hδ.bijOn.mapsTo hx)] at heq

end DifferentialGeometry.Topology.PiecewiseLinear
