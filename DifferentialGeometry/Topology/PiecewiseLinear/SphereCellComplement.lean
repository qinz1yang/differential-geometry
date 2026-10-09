/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_subset_of_inter_closure_sdiff_subset {X : Type*} [TopologicalSpace X]
    {S A Ab B Bb : Set X} (hAS : A ⊆ S) (hA : A ⊆ closure (A \ Ab))
    (hB : B ∩ closure (S \ B) ⊆ Bb) (hAB : A ∩ B ⊆ Ab) : A ∩ B ⊆ Bb := by
  rintro y ⟨hyA, hyB⟩
  by_contra hyb
  have hyc : y ∈ (closure (S \ B))ᶜ := fun h => hyb (hB ⟨hyB, h⟩)
  obtain ⟨z, hzU, hzA, hzAb⟩ := mem_closure_iff_nhds.mp (hA hyA) _
    (isClosed_closure.isOpen_compl.mem_nhds hyc)
  have hzB : z ∈ B := by
    by_contra hzB
    exact hzU (subset_closure ⟨hAS hzA, hzB⟩)
  exact hzAb (hAB ⟨hzA, hzB⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary_one {S D : Set E}
    (hS : IsPLSphere 1 S) {r : (Fin 2 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) D) (hDS : D ⊆ S) :
    D ∩ closure (S \ D) = r '' stdSimplexBoundary 1 := by
  classical
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  rw [← hKS] at hS hDS ⊢
  exact IsCombinatorialManifold.inter_closure_sdiff_eq_image_stdSimplexBoundary (n := 0) K
    (IsPLSphere.isCombinatorialManifold (n := 0) hS) hr hDS

end DifferentialGeometry.Topology.PiecewiseLinear
