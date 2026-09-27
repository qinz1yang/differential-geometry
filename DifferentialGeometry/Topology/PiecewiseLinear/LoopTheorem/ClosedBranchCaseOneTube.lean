/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSurfaceProducer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Classical in
theorem exists_isSourceTrackedBranchTube (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B : Set L.space)
      (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch),
      ¬hD.singularSet.IsBoundaryBranch c →
      ∀ (J Q C : Set (EuclideanSpace ℝ (Fin 2)))
        (τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2))
        (sheet : EuclideanSpace ℝ (Fin 2) → OpenPartialHomeomorph L.space (ℝ × ℝ × ℝ)),
        IsPLSphere 1 J → hD.IsMarkedBranchCollar c J Q C τ ρ sheet →
        ∃ (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (_ : Finite Pc.faces)
          (N : Geometry.SimplicialComplex ℝ E) (_ : Finite N.faces) (φ : (ℝ × ℝ) × ℝ → E)
          (u : ℝ × ℝ → ℝ × ℝ) (r : Fin 4 → ℝ × ℝ),
          IsSourceTrackedBranchTube hD c Subtype.val L J ρ N Pc φ u r := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B hD c hc J Q C τ ρ sheet hJ hmc
  obtain ⟨Pc, hPc, N, hN, φ, u, htube⟩ :=
    exists_isSourceTrackedBranchTube_of_sourceCollar L hL hD hc hJ hmc.1 hmc.2.1
  exact ⟨Pc, hPc, N, hN, φ, u, fourSpokeModelLeaf, htube⟩

end DifferentialGeometry.Topology.PiecewiseLinear
