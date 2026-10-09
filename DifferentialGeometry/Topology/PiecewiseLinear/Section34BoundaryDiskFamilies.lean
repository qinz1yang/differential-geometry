/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDisksDisjoint
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryHoledChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

theorem section34_splitDisk_subset_vertex_boundary
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, src (.splitDisk e) =
      src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    (hinc : w = (ends e).1 ∨ w = (ends e).2) :
    src (.splitDisk e) ⊆ srcBd (.vertexBall w) := by
  have hsub : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    rcases hinc with hw | hw
    · subst w
      rw [hends e]
      exact inter_subset_left
    · subst w
      rw [hends e]
      exact inter_subset_right
  rw [hframe.2.2.2.2.1 (.vertexBall w)]
  exact subset_iUnion₂_of_subset (.splitDisk e) ⟨hsub, by simp⟩ Subset.rfl

theorem section34_source_vertex_boundary_disks
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, src (.splitDisk e) =
      src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (w : Section34VertexIndex 𝒦 𝒦') :
    (∀ i : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2},
      IsPLCellOn 2 (src (.splitDisk i.1)) (srcBd (.splitDisk i.1))) ∧
    (∀ i : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2},
      src (.splitDisk i.1) ⊆ srcBd (.vertexBall w)) ∧
    Pairwise (fun i j : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2} =>
      Disjoint (src (.splitDisk i.1)) (src (.splitDisk j.1))) := by
  refine ⟨fun i => hframe.2.2.2.1 (.splitDisk i.1),
    fun i => section34_splitDisk_subset_vertex_boundary hframe hends w i.1 i.2, ?_⟩
  intro i j hij
  apply section34_splitDisks_disjoint hframe
  intro h
  exact hij (Subtype.ext h)

theorem section34_target_vertex_boundary_disks
    {DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (w : Section34VertexIndex 𝒦 𝒦') :
    (∀ i : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2},
      IsPLCellOn 2 (Dd i.1) (DdBd i.1)) ∧
    (∀ i : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2},
      Dd i.1 ⊆ DvBd w) ∧
    Pairwise (fun i j : {e : Section34EdgeIndex 𝒦 𝒦' //
        w = (ends e).1 ∨ w = (ends e).2} =>
      Disjoint (Dd i.1) (Dd j.1)) := by
  refine ⟨fun i => hDd i.1, ?_, ?_⟩
  · intro i
    rcases i.2 with hw | hw
    · intro x hx
      exact (congrArg DvBd hw.symm) ▸ (hDdBd i.1 hx).1
    · intro x hx
      exact (congrArg DvBd hw.symm) ▸ (hDdBd i.1 hx).2
  · intro i j hij
    apply hDddisj i.1 j.1
    intro h
    exact hij (Subtype.ext h)

end DifferentialGeometry.Topology.PiecewiseLinear
