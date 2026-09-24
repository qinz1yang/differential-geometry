/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCores
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Section34Edge Graph Regions -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem isCompact_inter_graphSkeletonSpace {C : Set M} (hC : IsCompact C) (hCU : C ⊆ U) :
    IsCompact (C ∩ graphSkeletonSpace 𝒦) := by
  let f : 𝒦.complex.space → M := fun x => 𝒦.map x
  have hrange : C ⊆ range f := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := 𝒦.bijOn.surjOn (hCU hx)
    exact ⟨⟨z, hz⟩, hzx⟩
  have hc : IsCompact (f ⁻¹' C) := 𝒦.isEmbedding.isInducing.isCompact_preimage' hC hrange
  have hpre := hc.inter_right (isClosed_preimage_graphSkeletonSpace 𝒦)
  have heq : f '' (f ⁻¹' C ∩ f ⁻¹' graphSkeletonSpace 𝒦) = C ∩ graphSkeletonSpace 𝒦 := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, hz, hzx⟩ := 𝒦.bijOn.surjOn (hCU hx.1)
      refine ⟨⟨z, hz⟩, ?_, hzx⟩
      change 𝒦.map z ∈ C ∩ graphSkeletonSpace 𝒦
      rwa [hzx]
  exact heq ▸ hpre.image 𝒦.isEmbedding.continuous

theorem exists_section34_splitDisk_vertex_neighborhood [T2Space M]
    (hU : IsOpen U) (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (e : Section34EdgeIndex 𝒦 𝒦') {O : Set M} (hO : IsOpen O)
    (hDO : src (.splitDisk e) ⊆ O) :
    ∃ V : Set M, IsOpen V ∧ src (.splitDisk e) ⊆ V ∧ V ⊆ O ∩ U ∧
      ∀ w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint V (src (.vertexBall w)) := by
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, -, -, -, -, -,
    hinc, -⟩ := hframe
  have hsrcU : ∀ l, src l ⊆ U := fun l => (subset_iUnion src l).trans hcover.subset
  let F : Section34CutLabelOf 𝒦 𝒦' → Set U := fun l => Subtype.val ⁻¹' src l
  have hFlf : LocallyFinite F := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hLF x x.2
    refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt hV, hfin.subset ?_⟩
    rintro l ⟨y, hyl, hyV⟩
    exact ⟨y, hyl, hyV⟩
  let J := {w : Section34VertexIndex 𝒦 𝒦' // w ≠ (ends e).1 ∧ w ≠ (ends e).2}
  let B : Set U := ⋃ w : J, F (.vertexBall w.1)
  have hvc : LocallyFinite (fun w : Section34VertexIndex 𝒦 𝒦' => F (.vertexBall w)) :=
    hFlf.comp_injective (fun _ _ heq => Section34Label.vertexBall.inj heq)
  have hBc : IsClosed B := (hvc.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun w => (hcell (.vertexBall w.1)).isCompact.isClosed.preimage continuous_subtype_val)
  let V := (Subtype.val '' Bᶜ) ∩ O
  refine ⟨V, (hU.isOpenMap_subtype_val _ hBc.isOpen_compl).inter hO, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨⟨⟨x, hsrcU _ hx⟩, ?_, rfl⟩, hDO hx⟩
    intro hxB
    obtain ⟨w, hxw⟩ := mem_iUnion.mp hxB
    have hwe := hinc w.1 e ⟨x, hxw, hx⟩
    exact (eq_or_eq_of_section34VertexIndex_subset e (hends e) hwe).elim w.2.1 w.2.2
  · rintro x ⟨⟨y, -, rfl⟩, hxO⟩
    exact ⟨hxO, y.2⟩
  · intro w hw₀ hw₁
    apply Set.disjoint_left.mpr
    rintro x ⟨⟨y, hy, rfl⟩, -⟩ hx
    exact hy (mem_iUnion.mpr ⟨⟨w, hw₀, hw₁⟩, hx⟩)

theorem exists_section34_compact_edge_graph_region [T2Space M]
    (hU : IsOpen U) (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (section34CutNeighborhood src) (graphSkeletonSpace 𝒦) U)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (e : Section34EdgeIndex 𝒦 𝒦') {O : Set M} (hO : IsOpen O)
    (hDO : src (.splitDisk e) ⊆ O) :
    ∃ V G : Set M, IsOpen V ∧ src (.splitDisk e) ⊆ V ∧ V ⊆ O ∩ U ∧
      IsCompact G ∧ G ⊆ O ∩ U ∧
      G ⊆ interior (src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2)) ∧
      graphSkeletonSpace 𝒦 ∩ V ⊆ G ∧
      ∀ w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint V (src (.vertexBall w)) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨W, hW, hDW, hWO, hforeign⟩ :=
    exists_section34_splitDisk_vertex_neighborhood hU hframe ends hends e hO hDO
  have hD : IsCompact (src (.splitDisk e)) := (hframe.2.2.2.1 (.splitDisk e)).isCompact
  obtain ⟨L, hL, hDL, hLW⟩ := exists_compact_between hD hW hDW
  have hLU : L ⊆ U := hLW.trans (hWO.trans inter_subset_right)
  have hpair : W ∩ interior (section34CutNeighborhood src) ⊆
      src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2) := by
    intro x hx
    obtain ⟨w, hxw⟩ := mem_iUnion.mp (interior_subset hx.2)
    by_cases hw₀ : w = (ends e).1
    · exact Or.inl (hw₀ ▸ hxw)
    · by_cases hw₁ : w = (ends e).2
      · exact Or.inr (hw₁ ▸ hxw)
      · exact (Set.disjoint_left.mp (hforeign w hw₀ hw₁) hx.1 hxw).elim
  have hpairI := interior_maximal hpair (hW.inter isOpen_interior)
  have hgraphI : graphSkeletonSpace 𝒦 ⊆ interior (section34CutNeighborhood src) :=
    subset_interior_iff_mem_nhdsSet.mpr hN.mem_nhdsSet
  refine ⟨interior L, L ∩ graphSkeletonSpace 𝒦, isOpen_interior, hDL,
    interior_subset.trans (hLW.trans hWO), isCompact_inter_graphSkeletonSpace hL hLU,
    inter_subset_left.trans (hLW.trans hWO), ?_, ?_, ?_⟩
  · intro x hx
    exact hpairI ⟨hLW hx.1, hgraphI hx.2⟩
  · exact fun _ hx => ⟨interior_subset hx.2, hx.1⟩
  · intro w hw₀ hw₁
    exact (hforeign w hw₀ hw₁).mono_left (interior_subset.trans hLW)

end DifferentialGeometry.Topology.PiecewiseLinear
