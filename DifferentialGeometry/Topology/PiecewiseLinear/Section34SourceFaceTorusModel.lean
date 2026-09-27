/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceCellModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceVertexCycle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceVertexAdjacency

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

open Classical in
theorem exists_section34SourceFaceTorus_cycle
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3) :
    ∃ (n : ℕ) (v : Fin (n + 3) → Section34VertexIndex 𝒦 𝒦'),
      Function.Injective v ∧ (∀ w, Section34Incident w.1 s.1 ↔ ∃ i, v i = w) ∧
      let C : Fin (n + 3) → Set Ea := fun i =>
        𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall (v i))
      (∀ i, IsPLBall 3 (C i)) ∧
      (∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j)) ∧
      (∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
        Disjoint (C i) (C j)) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅) ∧
      (⋃ i, C i) = 𝒦.complex.space ∩
        𝒦.map ⁻¹' section34FaceTorus (fun w => src (.vertexBall w)) s := by
  classical
  obtain ⟨-, hsubdiv, hmap, hcell, -, -, -, -, hcover, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, hends, -, -⟩ := id hcut
  choose a b hab he hsplit using hends
  let ends := fun e => (a e, b e)
  have hends' : ∀ e, (e.1 : Set Ea) =
      (((ends e).1).1 : Set Ea) ∪ (((ends e).2).1 : Set Ea) := he
  obtain ⟨n, v, hv, hvinc, hadj⟩ :=
    exists_section34Face_vertex_cycle hsubdiv hmap ends hends' s
  let C : Fin (n + 3) → Set Ea := fun i =>
    𝒦.complex.space ∩ 𝒦.map ⁻¹' src (.vertexBall (v i))
  have hsrcU (l : Section34CutLabelOf 𝒦 𝒦') : src l ⊆ U := by
    rw [← hcover]
    exact subset_iUnion src l
  have hinter (i j : Fin (n + 3)) : C i ∩ C j =
      𝒦.complex.space ∩
        𝒦.map ⁻¹' (src (.vertexBall (v i)) ∩ src (.vertexBall (v j))) := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩,
      fun hx => ⟨⟨hx.1, hx.2.1⟩, hx.1, hx.2.2⟩⟩
  refine ⟨n, v, hv, hvinc, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact 𝒦.isPLBall_preimage_of_isPLCellOn (hcell (.vertexBall (v i)))
      (hsrcU (.vertexBall (v i)))
  · intro i j hij
    obtain ⟨e, heij⟩ := (hadj i j hij.ne).mp hij
    have hmeet : src (.vertexBall (v i)) ∩ src (.vertexBall (v j)) =
        src (.splitDisk e) := by
      rcases heij with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [hi, hj]
        exact (hsplit e).symm
      · rw [hi, hj, inter_comm]
        exact (hsplit e).symm
    change IsPLBall 2 (C i ∩ C j)
    rw [hinter, hmeet]
    exact 𝒦.isPLBall_preimage_of_isPLCellOn (hcell (.splitDisk e))
      (hsrcU (.splitDisk e))
  · intro i j hij hnot
    apply disjoint_left.mpr
    intro x hxi hxj
    have hmeet : (src (.vertexBall (v i)) ∩ src (.vertexBall (v j))).Nonempty :=
      ⟨𝒦.map x, hxi.2, hxj.2⟩
    obtain ⟨e, -, heij⟩ := exists_section34Edge_of_vertex_inter_nonempty hcut ends hends'
      (fun heq => hij (hv heq)) hmeet
    exact hnot ((hadj i j hij).mpr ⟨e, heij⟩)
  · intro i j k hij hik hjk
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxi, hxj⟩, hxk⟩
    obtain ⟨e, heij, -⟩ := exists_section34Edge_of_vertex_inter_nonempty hcut ends hends'
      (fun heq => hij (hv heq)) ⟨𝒦.map x, hxi.2, hxj.2⟩
    have hxD : 𝒦.map x ∈ src (.splitDisk e) := heij.symm ▸ ⟨hxi.2, hxj.2⟩
    have hsub (l : Fin (n + 3)) (hxl : 𝒦.map x ∈ src (.vertexBall (v l))) :
        v l = a e ∨ v l = b e :=
      eq_or_eq_of_section34VertexIndex_subset e (he e) (hvertexEdge (v l) e ⟨_, hxl, hxD⟩)
    rcases hsub i hxi.2 with hi | hi <;> rcases hsub j hxj.2 with hj | hj <;>
      rcases hsub k hxk.2 with hk | hk
    all_goals first
      | exact hij (hv (hi.trans hj.symm))
      | exact hik (hv (hi.trans hk.symm))
      | exact hjk (hv (hj.trans hk.symm))
  · ext x
    constructor
    · rintro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine ⟨hi.1, mem_iUnion₂.mpr
        ⟨⟨(s, v i), (hvinc _).mpr ⟨i, rfl⟩⟩, rfl, hi.2⟩⟩
    · rintro ⟨hxK, hx⟩
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
      have hia : Section34Incident a.1.2.1 s.1 := by
        rw [← ha]
        exact a.2
      obtain ⟨i, hi⟩ := (hvinc _).mp hia
      exact mem_iUnion.mpr ⟨i, hxK, hi.symm ▸ hxa⟩

theorem isPolyhedron_section34SourceFaceTorus_model
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3) :
    IsPolyhedron (𝒦.complex.space ∩
      𝒦.map ⁻¹' section34FaceTorus (fun w => src (.vertexBall w)) s) := by
  obtain ⟨n, v, -, -, hC, -, -, -, hcover⟩ := exists_section34SourceFaceTorus_cycle hcut s
  rw [← hcover]
  exact IsPolyhedron.iUnion fun i => (hC i).isPolyhedron

end DifferentialGeometry.Topology.PiecewiseLinear
