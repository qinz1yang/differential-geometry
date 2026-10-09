/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutPair
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPuncturedSphere
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexOperations

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3} {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}

theorem exists_vertex_return_disk_avoiding_split_disks
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd)
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K')
    (e₀ : Section34CompactEdgeIndex K K') {B : Set E3} {η : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B) (hBP : B ⊆ fblBd s)
    (hBS : B ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e₀)
    (hmeet : B ∩ (⋃ e, section34CompactSplitDiskImage src f₁ e) = {η 0, η 1}) :
    ∃ (R D : Set E3) (q : (Fin 3 → ℝ) → E3) (δ : ℝ → E3),
      IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
      R ⊆ section34CompactSplitDiskImage srcBd f₁ e₀ ∧ B ∩ R = {η 0, η 1} ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = B ∪ R ∧
      D ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
        frontier (⋃ v, section34CompactVertexBallImage src f₁ v) ∧
      D ∩ section34CompactSplitDiskImage src f₁ e₀ = R ∧
      ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
        Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
  classical
  have hf₁ := hgraph.2.1
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e₀
  have hη0 : η 0 ∈ B := hη.bijOn.mapsTo (by norm_num)
  have hη1 : η 1 ∈ B := hη.bijOn.mapsTo (by norm_num)
  have hηE : η 0 ∈ section34CompactSplitDiskImage src f₁ e₀ :=
    hE.boundary_subset (hends (by simp))
  have hwe₀ := hcut.subset_of_mem_splitDiskImage hf₁ hηE (hV.boundary_subset (hBS hη0))
  have he₀s : Section34Incident e₀.1 s.1 := by
    by_contra he
    exact Set.disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s e₀ he)
      ((hinv.1 s).boundary_subset (hBP hη0)) hηE
  have hS : IsPLSphere 2 (section34CompactVertexBallImage srcBd f₁ w) := by
    rw [hV.boundary_eq_frontier]
    exact hV.isPLBall_three.isPLSphere_frontier
  have hES := hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e₀ hwe₀
  obtain ⟨p, hp, hpγ⟩ := hE.exists_isPLHomeomorphOn_stdSimplex
  have hED : IsPLBall 2 (section34CompactSplitDiskImage src f₁ e₀) := ⟨p, hp⟩
  let Q := closure (section34CompactVertexBallImage srcBd f₁ w \
    section34CompactSplitDiskImage src f₁ e₀)
  have hQS : Q ⊆ section34CompactVertexBallImage srcBd f₁ w :=
    closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  obtain ⟨r, hr⟩ : IsPLBall 2 Q := hS.isPLBall_closure_sdiff hED hES
  have hQγ : Q ∩ section34CompactSplitDiskImage src f₁ e₀ =
      section34CompactSplitDiskImage srcBd f₁ e₀ := by
    rw [inter_comm]
    exact (hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hp hES).trans hpγ.symm
  have hrγ : r '' stdSimplexBoundary 2 = section34CompactSplitDiskImage srcBd f₁ e₀ :=
    (hS.image_stdSimplexBoundary_complement hED hES hr).trans hQγ
  have hBQ : B ⊆ Q := by
    change B ⊆ closure (section34CompactVertexBallImage srcBd f₁ w \
      section34CompactSplitDiskImage src f₁ e₀)
    rw [hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hp hES, ← hpγ]
    intro x hxB
    exact ⟨hBS hxB, fun hxE => hxE.2 (hends
      (hmeet.subset ⟨hxB, mem_iUnion.mpr ⟨e₀, hxE.1⟩⟩))⟩
  have hBγ : B ∩ section34CompactSplitDiskImage srcBd f₁ e₀ = {η 0, η 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxγ⟩
      exact hmeet.subset ⟨hxB, mem_iUnion.mpr ⟨e₀, hE.boundary_subset hxγ⟩⟩
    · intro x hx
      exact ⟨(pair_subset hη0 hη1) hx, hends hx⟩
  have hγN := hcut.splitDiskBoundary_subset_frontier_vertexBallImages hf₁ e₀
  have hBN : B ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v) := by
    intro x hxB
    by_cases hxE : x ∈ ⋃ e, section34CompactSplitDiskImage src f₁ e
    · exact hγN (hends (hmeet.subset ⟨hxB, hxE⟩))
    · exact (hcut.frontier_eventually_eq_vertexBallBoundary hf₁ w
        (hV.boundary_subset (hBS hxB))
        (fun e hxe => hxE (mem_iUnion.mpr ⟨e, hxe⟩))).self_of_nhds.mpr (hBS hxB)
  obtain ⟨D₁, D₂, R₁, R₂, q₁, q₂, δ₁, δ₂, hq₁, hq₂, hδ₁, hδ₂,
    hδ₁0, hδ₁1, hδ₂0, hδ₂1, hDunion, hDinter, hq₁B, hq₂B, hD₁R, hD₂R, hRunion, -⟩ :=
    exists_disk_pair_with_boundary_arcs_of_proper_arc hr hη hBQ (by rw [hrγ]; exact hBγ)
  rw [hrγ] at hD₁R hD₂R hRunion
  have hD₁Q : D₁ ⊆ Q := subset_union_left.trans hDunion.subset
  have hD₂Q : D₂ ⊆ Q := subset_union_right.trans hDunion.subset
  have hR₁γ : R₁ ⊆ section34CompactSplitDiskImage srcBd f₁ e₀ :=
    subset_union_left.trans hRunion.subset
  have hJ : IsPLSphere 1 (B ∪ R₁) := hq₁B ▸ hq₁.isPLSphere_image_stdSimplexBoundary
  have hJ₁ : B ∪ R₁ ⊆ D₁ := by
    rw [← hq₁B, ← hq₁.image_eq]
    exact image_mono fun x hx => hx.1
  have hJE : ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
      Disjoint (B ∪ R₁) (section34CompactSplitDiskImage src f₁ e) := by
    intro e he
    apply Set.disjoint_left.mpr
    intro x hx hxE
    have hxE₀ : x ∈ section34CompactSplitDiskImage src f₁ e₀ := by
      rcases hx with hxB | hxR
      · exact hE.boundary_subset (hends (hmeet.subset ⟨hxB, mem_iUnion.mpr ⟨e, hxE⟩⟩))
      · exact hE.boundary_subset (hR₁γ hxR)
    exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁ he) hxE hxE₀
  obtain ⟨Y, hY, hYS, hEY⟩ := exists_connected_set_containing_other_split_disks
    hinv hcut hgraph s w e₀ hwe₀ he₀s hJ
    (hJ₁.trans (hD₁Q.trans (hQS.trans hV.boundary_subset)))
    (union_subset hBN (hR₁γ.trans hγN)) (union_subset_union hBP hR₁γ) hJE
  have hselect : ∀ (D R : Set E3) (q : (Fin 3 → ℝ) → E3) (δ : ℝ → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      IsPLHomeomorphOn δ (Icc 0 1) R → δ 0 = η 0 → δ 1 = η 1 →
      D ⊆ Q → q '' stdSimplexBoundary 2 = B ∪ R →
      D ∩ section34CompactSplitDiskImage srcBd f₁ e₀ = R → Disjoint D Y →
      ∃ (R D : Set E3) (q : (Fin 3 → ℝ) → E3) (δ : ℝ → E3),
        IsPLHomeomorphOn δ (Icc 0 1) R ∧ δ 0 = η 0 ∧ δ 1 = η 1 ∧
        R ⊆ section34CompactSplitDiskImage srcBd f₁ e₀ ∧ B ∩ R = {η 0, η 1} ∧
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ q '' stdSimplexBoundary 2 = B ∪ R ∧
        D ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
          frontier (⋃ v, section34CompactVertexBallImage src f₁ v) ∧
        D ∩ section34CompactSplitDiskImage src f₁ e₀ = R ∧
        ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
          Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
    intro D R q δ hq hδ hδ0 hδ1 hDQ hqB hDR hDY
    have hDS := hDQ.trans hQS
    have hRγ := hDR.symm.subset.trans inter_subset_right
    have hRends : ({η 0, η 1} : Set E3) ⊆ R := by
      rw [← hδ0, ← hδ1]
      exact pair_subset (hδ.bijOn.mapsTo (by norm_num)) (hδ.bijOn.mapsTo (by norm_num))
    have hBR : B ∩ R = {η 0, η 1} := Subset.antisymm
      (fun x hx => hBγ.subset ⟨hx.1, hRγ hx.2⟩)
      (fun x hx => ⟨(pair_subset hη0 hη1) hx, hRends hx⟩)
    have hforeign : ∀ e : Section34CompactEdgeIndex K K', e ≠ e₀ →
        Disjoint D (section34CompactSplitDiskImage src f₁ e) := by
      intro e he
      by_cases hwe : w.1 ⊆ e.1
      · exact hDY.mono_right (hEY e hwe he)
      · exact Set.disjoint_left.mpr fun x hxD hxE => hwe
          (hcut.subset_of_mem_splitDiskImage hf₁ hxE (hV.boundary_subset (hDS hxD)))
    have hDE : D ∩ section34CompactSplitDiskImage src f₁ e₀ = R := by
      calc D ∩ section34CompactSplitDiskImage src f₁ e₀ =
          D ∩ (Q ∩ section34CompactSplitDiskImage src f₁ e₀) := by
            rw [← inter_assoc, inter_eq_left.mpr hDQ]
        _ = D ∩ section34CompactSplitDiskImage srcBd f₁ e₀ := by rw [hQγ]
        _ = R := hDR
    have hDN : D ⊆ frontier (⋃ v, section34CompactVertexBallImage src f₁ v) := by
      intro x hxD
      by_cases hxE₀ : x ∈ section34CompactSplitDiskImage src f₁ e₀
      · exact hγN (hRγ (hDE.subset ⟨hxD, hxE₀⟩))
      · exact (hcut.frontier_eventually_eq_vertexBallBoundary hf₁ w
          (hV.boundary_subset (hDS hxD)) (by
            intro e hxe
            by_cases he : e = e₀
            · exact hxE₀ (he ▸ hxe)
            · exact Set.disjoint_left.mp (hforeign e he) hxD hxe)).self_of_nhds.mpr (hDS hxD)
    exact ⟨R, D, q, δ, hδ, hδ0, hδ1, hRγ, hBR, hq, hqB, subset_inter hDS hDN, hDE, hforeign⟩
  have hYJ : Disjoint Y (q₁ '' stdSimplexBoundary 2) := by
    rw [hq₁B]
    exact Set.disjoint_left.mpr fun x hx hxJ => (hYS hx).2 hxJ
  rcases hS.subset_or_disjoint_disk_of_eventually_eq hq₁ (hD₁Q.trans hQS)
      (fun _ _ => Filter.Eventually.of_forall fun _ => Iff.rfl)
      hY.isPreconnected (hYS.trans sdiff_subset) hYJ with hYD₁ | hD₁Y
  · have hD₂Y : Disjoint D₂ Y := by
      apply Set.disjoint_left.mpr
      intro x hxD₂ hxY
      exact (hYS hxY).2 (Or.inl (hDinter.subset ⟨hYD₁ hxY, hxD₂⟩))
    exact hselect D₂ R₂ q₂ δ₂ hq₂ hδ₂ hδ₂0 hδ₂1 hD₂Q hq₂B hD₂R hD₂Y
  · exact hselect D₁ R₁ q₁ δ₁ hq₁ hδ₁ hδ₁0 hδ₁1 hD₁Q hq₁B hD₁R hD₁Y

end DifferentialGeometry.Topology.PiecewiseLinear
