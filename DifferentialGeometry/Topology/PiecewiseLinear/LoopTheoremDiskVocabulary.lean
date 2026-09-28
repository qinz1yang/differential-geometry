/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def IsLoopTheoremDisk (Kimg N' BdX Δ : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
    IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ interior N' \ Kimg ∧
    Δ ∩ BdX = r '' stdSimplexBoundary 2 ∧
    ∃ hb : r '' stdSimplexBoundary 2 ⊆ BdX,
      ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
        C(r '' stdSimplexBoundary 2, BdX)).Nullhomotopic

def HasNoHandleLoopTheoremDisk (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ v ∈ K.vertices, ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
    IsLoopTheoremDisk (h '' K.space) N' (frontier X) Δ → ¬ Δ ⊆ Cpp v

end DifferentialGeometry.Topology.PiecewiseLinear
