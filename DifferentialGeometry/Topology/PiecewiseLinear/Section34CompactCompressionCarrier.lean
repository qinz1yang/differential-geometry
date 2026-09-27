/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceHomology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem Section34CompactFaceBallInvariants.exists_isOpen_frontier_eq
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (hfin : K'.faces.Finite) (hV : ∀ w, IsClosed (tgtV w))
    (s : Section34CompactSimplexIndex K 3) :
    ∃ O : Set E3, IsOpen O ∧ fbl s ⊆ O ∧
      frontier (⋃ w, tgtV w) ∩ O = frontier (section34CompactFaceTorus tgtV s) ∩ O ∧
      ∀ w, ¬ Section34Incident w.1 s.1 → Disjoint O (tgtV w) := by
  let _ : Finite (Section34CompactVertexIndex K K') :=
    finite_section34CompactGraphIndex hfin _ 1
  let A := ⋃ w ∈ {w : Section34CompactVertexIndex K K' | ¬ Section34Incident w.1 s.1}, tgtV w
  have hA : IsClosed A := (Set.toFinite _).isClosed_biUnion fun w _ => hV w
  have hOV : ∀ w, ¬ Section34Incident w.1 s.1 → Disjoint Aᶜ (tgtV w) :=
    fun w hw => disjoint_left.mpr fun x hx hxw => hx (mem_iUnion₂.mpr ⟨w, hw, hxw⟩)
  refine ⟨Aᶜ, hA.isOpen_compl, ?_,
    frontier_iUnion_inter_eq_faceTorus_inter s hA.isOpen_compl hOV, hOV⟩
  intro x hx hxA
  obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hxA
  exact notMem_empty x ((hinv.2.2.1 s w hw) ▸ ⟨hx, hxw⟩)

theorem Section34CompactCutFrame.exists_isOpen_compression_disk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w : Section34CompactVertexIndex K K'} {D : Set E3}
    (hDw : D ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hDE : ∀ e, Disjoint D (section34CompactSplitDiskImage src f₁ e)) :
    ∃ O : Set E3, IsOpen O ∧ D ⊆ O ∧
      frontier (⋃ v, section34CompactVertexBallImage src f₁ v) ∩ O =
        frontier (section34CompactVertexBallImage src f₁ w) ∩ O ∧
      (∀ v, v ≠ w → Disjoint O (section34CompactVertexBallImage src f₁ v)) ∧
      ∀ e, Disjoint O (section34CompactSplitDiskImage src f₁ e) := by
  let _ : Finite (Section34CompactVertexIndex K K') :=
    finite_section34CompactGraphIndex hcut.2.2.1 _ 1
  let _ : Finite (Section34CompactEdgeIndex K K') :=
    finite_section34CompactGraphIndex hcut.2.2.1 _ 2
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  let A := ⋃ v ∈ {v : Section34CompactVertexIndex K K' | v ≠ w},
    section34CompactVertexBallImage src f₁ v
  let B := ⋃ e, section34CompactSplitDiskImage src f₁ e
  have hAc : IsClosed A := (Set.toFinite _).isClosed_biUnion fun v _ =>
    (hVcell v).isCompact.isClosed
  have hBc : IsClosed B := isClosed_iUnion_of_finite fun e => (hEcell e).isCompact.isClosed
  have hOV : ∀ v, v ≠ w → Disjoint (A ∪ B)ᶜ (section34CompactVertexBallImage src f₁ v) :=
    fun v hv => disjoint_left.mpr fun x hx hxv =>
      hx (Or.inl (mem_iUnion₂.mpr ⟨v, hv, hxv⟩))
  refine ⟨(A ∪ B)ᶜ, (hAc.union hBc).isOpen_compl, ?_,
    frontier_iUnion_inter_eq_vertexBall_inter w (hAc.union hBc).isOpen_compl hOV, hOV,
    fun e => disjoint_left.mpr fun x hx hxe => hx (Or.inr (mem_iUnion.mpr ⟨e, hxe⟩))⟩
  intro x hx
  rintro (hxA | hxB)
  · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxA
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ (Ne.symm hv)
      ((hVcell w).boundary_subset (hDw hx)) hxv
    exact disjoint_left.mp (hDE e) hx hxe
  · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxB
    exact disjoint_left.mp (hDE e) hx hxe

theorem Section34CompactGraphFrame.isCompact_image_simplexRim
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) : IsCompact (h '' section34CompactSimplexRim s.1) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := hgraph
  obtain ⟨S₁, S₂, -, -, -, -, -, -, hspine⟩ := hnest s
  exact hspine.isCompact

theorem Section34CompactGraphFrame.isConnected_image_simplexRim
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) : IsConnected (h '' section34CompactSimplexRim s.1) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := hgraph
  obtain ⟨S₁, S₂, -, -, -, -, -, -, hspine⟩ := hnest s
  exact hspine.isConnected

theorem Section34CompactGraphFrame.carriesFirstHomologyOnto
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) :
    CarriesFirstHomologyOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨S₁, S₂, -, -, hT, -⟩ := hnest s
  exact (hgraph.carriesFundamentalGroupOnto s).carriesFirstHomologyOnto
    (hgraph.isConnected_image_simplexRim s).nonempty hT.1.isPathConnected

end DifferentialGeometry.Topology.PiecewiseLinear
