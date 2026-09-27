/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ M] [IsManifold (𝓡 2) ∞ N]

theorem exists_isSubdivision_closedStars_subset_paired_charts
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ξ : K.space ≃ₜ M) (h : M ≃ₜ N) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∃ x : M,
        ξ '' (((↑) : K.space → E) ⁻¹' (⋃ v ∈ s, closedStar R v)) ⊆
          (extChartAtPartialDiffeomorph (𝓡 2) ∞ x).source ∧
        h '' (ξ '' (((↑) : K.space → E) ⁻¹' (⋃ v ∈ s, closedStar R v))) ⊆
          (extChartAtPartialDiffeomorph (𝓡 2) ∞ (h x)).source := by
  let A : M → Set M := fun x => (extChartAtPartialDiffeomorph (𝓡 2) ∞ x).source
  let B : M → Set N := fun x => (extChartAtPartialDiffeomorph (𝓡 2) ∞ (h x)).source
  let U : M → Set E := fun x => ((↑) : K.space → E) '' (ξ ⁻¹' (A x ∩ h ⁻¹' B x))
  have hU (x : M) : IsOpen (((↑) : K.space → E) ⁻¹' U x) := by
    change IsOpen (((↑) : K.space → E) ⁻¹'
      (((↑) : K.space → E) '' (ξ ⁻¹' (A x ∩ h ⁻¹' B x))))
    rw [preimage_image_eq _ Subtype.val_injective]
    exact ((extChartAtPartialDiffeomorph (𝓡 2) ∞ x).open_source.inter
      ((extChartAtPartialDiffeomorph (𝓡 2) ∞ (h x)).open_source.preimage
        h.continuous)).preimage ξ.continuous
  have hcover : K.space ⊆ ⋃ x, U x := by
    intro z hz
    let q : K.space := ⟨z, hz⟩
    refine mem_iUnion.mpr ⟨ξ q, q, ?_, rfl⟩
    exact ⟨mem_extChartAt_source (I := 𝓡 2) (ξ q),
      mem_extChartAt_source (I := 𝓡 2) (h (ξ q))⟩
  obtain ⟨R, hR, hfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K U hU hcover
  refine ⟨R, hR, hfinite, fun s hs => ?_⟩
  obtain ⟨x, hx⟩ := hstars s hs
  have hpair : ∀ q : K.space, q.val ∈ (⋃ v ∈ s, closedStar R v) →
      ξ q ∈ A x ∧ h (ξ q) ∈ B x := by
    intro q hq
    obtain ⟨q', hq', heq⟩ := hx hq
    have heq' : q' = q := Subtype.ext heq
    change ξ q' ∈ A x ∧ h (ξ q') ∈ B x at hq'
    simpa only [heq'] using hq'
  refine ⟨x, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (hpair q hq).1
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact (hpair q hq).2

end DifferentialGeometry.Topology.PiecewiseLinear
