/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron
import DifferentialGeometry.Geometry.Boundary.Manifold.Basic
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem nonempty_homeomorph_stdSimplexBoundary_three_sphere :
    Nonempty ({z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hset : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} =
      DifferentialGeometry.Simplex.boundary (Fin (3 + 1)) := by
    ext z
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  exact ⟨(Homeomorph.setCongr hset).trans
    (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩

theorem isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    IsClopen ((fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' range ψ) := by
  classical
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  obtain ⟨a₀⟩ := nonempty_homeomorph_stdSimplexBoundary_three_sphere
  let ψ' : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} →
      BoundaryManifold (𝓡∂ 3) M := fun z => ⟨ψ z, hψbd (mem_range_self z)⟩
  have hψ'c : Continuous ψ' := hψ.continuous.subtype_mk _
  have hψ'i : Function.Injective ψ' := fun z w h => hψ.injective (congrArg Subtype.val h)
  have hpre : (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' range ψ = range ψ' := by
    ext b
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  refine ⟨hψ.isClosed_range.preimage continuous_subtype_val, ?_⟩
  rw [hpre, isOpen_iff_forall_mem_open]
  rintro _ ⟨z, rfl⟩
  let σ := chartAt (EuclideanSpace ℝ (Fin 2)) (a₀ z)
  let f : σ.target → BoundaryManifold (𝓡∂ 3) M := fun u => ψ' (a₀.symm (σ.symm u))
  have hfc : Continuous f := hψ'c.comp (a₀.symm.continuous.comp
    (σ.continuousOn_symm.comp_continuous continuous_subtype_val fun u => u.2))
  have hfi : Function.Injective f := fun u v h =>
    Subtype.ext (σ.symm.injOn u.2 v.2 (a₀.symm.injective (hψ'i h)))
  refine ⟨range f, ?_, isOpen_range_of_isOpen_of_continuous_injective_real (𝓡 2)
    σ.open_target f hfc hfi, ⟨σ (a₀ z), σ.map_source (mem_chart_source _ _)⟩, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact mem_range_self _
  · change ψ' (a₀.symm (σ.symm (σ (a₀ z)))) = ψ' z
    rw [σ.left_inv (mem_chart_source _ _), Homeomorph.symm_apply_apply]

theorem exists_opens_boundaryManifold_homeomorph_sphere
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ W : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M),
      IsClosed (W : Set (BoundaryManifold (𝓡∂ 3) M)) ∧ CompactSpace W ∧
      (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) '' W = range ψ ∧
      Nonempty (W ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  classical
  have hcl := isClopen_boundaryManifold_preimage_range_of_isClosedEmbedding ψ hψ hψbd
  obtain ⟨a₀⟩ := nonempty_homeomorph_stdSimplexBoundary_three_sphere
  let ψ' : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} →
      BoundaryManifold (𝓡∂ 3) M := fun z => ⟨ψ z, hψbd (mem_range_self z)⟩
  have hψ'e : IsEmbedding ψ' := IsEmbedding.subtypeVal.of_comp_iff.mp hψ.isEmbedding
  have hpre : (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' range ψ = range ψ' := by
    ext b
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  let W : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M) := ⟨_, hcl.isOpen⟩
  let hW : W ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ((Homeomorph.setCongr hpre).trans hψ'e.toHomeomorph.symm).trans a₀
  refine ⟨W, hcl.isClosed, hW.symm.compactSpace, ?_, ⟨hW⟩⟩
  change (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ''
    ((fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) ⁻¹' range ψ) = range ψ
  rw [image_preimage_eq_inter_range, inter_eq_left]
  rintro _ ⟨z, rfl⟩
  exact ⟨ψ' z, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
