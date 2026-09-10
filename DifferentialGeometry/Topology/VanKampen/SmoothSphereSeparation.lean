/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.SmoothBicollar
import DifferentialGeometry.Topology.VanKampen.SmoothCollarBoundary
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRetraction

set_option autoImplicit false

open Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace Poincare.Topology.ThreeManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ M]
    [SimplyConnectedSpace M]
    {e : SphereTwo → M}

theorem nonempty_connectedComponents_complement_equiv_bool_of_smoothSphereEmbedding
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e) :
    Nonempty (ConnectedComponents ((range e)ᶜ : Set M) ≃ Bool) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨c⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e he
  exact ⟨c.toTwoSidedCollar.connectedComponentsComplementEquivBool⟩

theorem exists_boundaryAtlas_closure_component_of_smoothSphereEmbedding
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e)
    (p : ((range e)ᶜ : Set M)) :
    ∃ C : SmoothBoundaryAtlas (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) 3
        (closure (Subtype.val '' connectedComponent p)),
      ∀ q : (closure (Subtype.val '' connectedComponent p) : Set M),
        C.ambientChart q q.val 0 = 0 ↔ q.val ∈ range e := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨c⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e he
  let h := c.toTwoSidedCollar
  rcases h.component_eq_negative_or_positive p with hp | hp
  · have hside : Subtype.val '' connectedComponent p = h.negativeSide :=
      congrArg (fun s : Set h.complement ↦ Subtype.val '' s)
        (ConnectedComponents.coe_eq_coe.mp hp)
    rw [hside]
    exact c.exists_boundaryAtlas_closure_negativeSide
  · have hside : Subtype.val '' connectedComponent p = h.positiveSide :=
      congrArg (fun s : Set h.complement ↦ Subtype.val '' s)
        (ConnectedComponents.coe_eq_coe.mp hp)
    rw [hside]
    exact c.exists_boundaryAtlas_closure_positiveSide

theorem exists_chartedSpace_closure_component_of_smoothSphereEmbedding
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e)
    (p : ((range e)ᶜ : Set M)) :
    ∃ c : ChartedSpace (EuclideanHalfSpace 3)
        (closure (Subtype.val '' connectedComponent p) : Set M),
      letI := c
      IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞
        (closure (Subtype.val '' connectedComponent p) : Set M) ∧
      ContMDiff (modelWithCornersEuclideanHalfSpace 3)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
        (Subtype.val : (closure (Subtype.val '' connectedComponent p) : Set M) → M) ∧
      ∀ q : (closure (Subtype.val '' connectedComponent p) : Set M),
        (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔ q.val ∈ range e := by
  obtain ⟨C, hC⟩ := exists_boundaryAtlas_closure_component_of_smoothSphereEmbedding he p
  exact ⟨C.toChartedSpace, C.isManifold, C.contMDiff_subtype_val,
    fun q ↦ (C.isBoundaryPoint_iff q).trans (hC q)⟩

theorem sphere_separation_of_smoothSphereEmbedding
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e) :
    Nonempty (ConnectedComponents ((range e)ᶜ : Set M) ≃ Bool) ∧
    ∀ p : ((range e)ᶜ : Set M),
      ∃ c : ChartedSpace (EuclideanHalfSpace 3)
          (closure (Subtype.val '' connectedComponent p) : Set M),
        letI := c
        IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞
          (closure (Subtype.val '' connectedComponent p) : Set M) ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace 3)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞
          (Subtype.val : (closure (Subtype.val '' connectedComponent p) : Set M) → M) ∧
        ∀ q : (closure (Subtype.val '' connectedComponent p) : Set M),
          (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint q ↔ q.val ∈ range e :=
  ⟨nonempty_connectedComponents_complement_equiv_bool_of_smoothSphereEmbedding he,
    exists_chartedSpace_closure_component_of_smoothSphereEmbedding he⟩

theorem simplyConnectedSpace_closure_component_of_smoothSphereEmbedding
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e)
    (p : ((range e)ᶜ : Set M)) :
    SimplyConnectedSpace (closure (Subtype.val '' connectedComponent p) : Set M) := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨c⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e he
  let h := c.toTwoSidedCollar
  rcases h.component_eq_negative_or_positive p with hp | hp
  · have hside : Subtype.val '' connectedComponent p = h.negativeSide :=
      congrArg (fun s : Set h.complement ↦ Subtype.val '' s)
        (ConnectedComponents.coe_eq_coe.mp hp)
    rw [hside]
    exact h.simplyConnectedSpace_closure_sides.1
  · have hside : Subtype.val '' connectedComponent p = h.positiveSide :=
      congrArg (fun s : Set h.complement ↦ Subtype.val '' s)
        (ConnectedComponents.coe_eq_coe.mp hp)
    rw [hside]
    exact h.simplyConnectedSpace_closure_sides.2

end Poincare.Topology.ThreeManifold
