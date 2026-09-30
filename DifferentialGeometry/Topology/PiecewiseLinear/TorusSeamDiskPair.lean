/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialSolidTorus.subset_closure_interior {X : Set E3}
    (hX : IsCombinatorialSolidTorus X) : X ⊆ closure (interior X) := by
  obtain ⟨-, n, -, C, -, hcover, hball, -⟩ := hX
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
  have hsub : (C i).space ⊆ X := (subset_iUnion (fun j => (C j).space) i).trans hcover.subset
  apply closure_mono (interior_mono hsub)
  rw [(hball i).closure_interior_of_finrank (by simp)]
  exact hxi

theorem exists_disk_pair_of_crossing_torus_seam {X T Δ U : Set E3}
    (hX : IsCombinatorialSolidTorus X) (hT : IsPLTorus T)
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hΔX : Δ ⊆ frontier X) (hmeet : Δ ∩ T = r '' stdSimplexBoundary 2)
    (hU : IsOpen U) (hΔU : Δ ⊆ U)
    (htrace : U ∩ T ∩ frontier X ⊆ r '' stdSimplexBoundary 2)
    (hcross : ∀ x ∈ r '' stdSimplexBoundary 2, HasPLCrossingAt T (frontier X) x) :
    ∃ (D₁ D₂ : Set E3) (q₁ q₂ : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      Δ ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧ Δ ⊆ D₂ \ q₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = Δ ∧ D₁ ∩ frontier X = Δ ∧ D₂ ⊆ frontier X ∧
      D₁ \ Δ ⊆ T \ interior X ∧
      D₁ ∪ D₂ ⊆ (frontier X ∪ (T \ interior X)) ∩ U ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[frontier X ∪ (T \ interior X)] Δ := by
  let J := r '' stdSimplexBoundary 2
  let L := T \ interior X
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJΔ : J ⊆ Δ := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hJT : J ⊆ T := hmeet.symm.subset.trans inter_subset_right
  have hJfr : J ⊆ frontier X := hJΔ.trans hΔX
  obtain ⟨x, hxJ⟩ := hJ.nonempty
  have hcollar : HasPLCircleCollar L J := by
    refine ⟨hJ, ?_⟩
    intro V hV hJV
    obtain ⟨W, ρ, hρ, hρ0, hW, hnear, -⟩ := hT.exists_exterior_collar_of_crossing
      hJ hJT hJfr hX.isPolyhedron.isClosed (hU.inter hV)
      (fun y hy => ⟨hΔU (hJΔ hy), hJV hy⟩)
      (fun y hy => htrace ⟨⟨hy.1.1.1, hy.1.2⟩, hy.2⟩) hxJ (hcross x hxJ)
      (hX.subset_closure_interior (hX.isPolyhedron.isClosed.frontier_subset (hJfr hxJ)))
    exact ⟨W, ρ, hρ, hρ0, fun y hy => ⟨(hW hy).1, (hW hy).2.2⟩, hnear⟩
  have hΔL : Δ ∩ L = J := Subset.antisymm
    (fun y hy => hmeet.subset ⟨hy.1, hy.2.1⟩)
    (fun y hy => ⟨hJΔ hy, hJT hy, (hJfr hy).2⟩)
  exact exists_disk_pair_of_circle_collar hX.isPLTorus_frontier
    (hT.1.isClosed.sdiff isOpen_interior) hr hΔX hΔL hcollar hU hΔU
    (fun y hy => htrace ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
