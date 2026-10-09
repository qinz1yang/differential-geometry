/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellIntersectionBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LinkPropagation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PuncturedLink
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.splitDiskImage_subset_vertexBallBoundary
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (hwe : w.1 ⊆ e.1) :
    section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage srcBd f₁ w := by
  obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have hI := hcut.isPLCellOn_splitDiskImage hf₁ e
  rw [heq] at hI ⊢
  rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with ha | hb
  · rw [ha]
    exact (hcut.isPLCellOn_vertexBallImage hf₁ a).inter_subset_boundary_of_isPLCellOn
      (hcut.isPLCellOn_vertexBallImage hf₁ b) hI
  · rw [hb, inter_comm]
    rw [inter_comm] at hI
    exact (hcut.isPLCellOn_vertexBallImage hf₁ b).inter_subset_boundary_of_isPLCellOn
      (hcut.isPLCellOn_vertexBallImage hf₁ a) hI

omit [FiniteDimensional ℝ Ea] in
theorem Section34FaceBallInvariants.disjoint_splitDiskImage_of_not_incident
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦')
    (he : ¬ Section34Incident e.1 s.1) :
    Disjoint (fbl s) (section34SplitDiskImage src f₁ e) := by
  apply Set.disjoint_left.mpr
  intro x hxP hxE
  obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
  have hinc : ∀ w : Section34VertexIndex 𝒦 𝒦',
      x ∈ section34VertexBallImage src f₁ w → Section34Incident w.1 s.1 := by
    intro w hxw
    by_contra hnot
    exact Set.notMem_empty x (hinv.2.2.1 s w hnot ▸ ⟨hxP, hxw⟩)
  apply he
  change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
  rw [heab]
  exact union_subset (hinc a (heq.subset hxE).1) (hinc b (heq.subset hxE).2)

open Classical in
theorem exists_section34_connected_set_containing_split_disks
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hws : Section34Incident w.1 s.1) {J : Set M₂} (hJP : J ⊆ fblBd s)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint J (section34SplitDiskImage src f₁ e))
    (hfill : ∀ t : Section34SimplexIndex 𝒦 3, Section34Incident w.1 t.1 →
      Disjoint J (fblBd t) →
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint J (section34SplitDiskImage srcBd f₁ e)) →
      ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
        ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
          Disjoint D (section34SplitDiskImage src f₁ e)) :
    ∃ Y : Set M₂, IsConnected Y ∧ Y ⊆ section34VertexBallImage srcBd f₁ w \ J ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 →
        section34SplitDiskImage src f₁ e ⊆ Y := by
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  choose p hp using fun e : Section34EdgeIndex 𝒦 𝒦' =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
  let S := section34VertexBallImage srcBd f₁ w \ J
  let c := fun e : Section34EdgeIndex 𝒦 𝒦' => connectedComponentIn S (p e)
  have hES : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34SplitDiskImage src f₁ e ⊆ S := by
    intro e hwe x hx
    exact ⟨hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e hwe hx,
      fun hxJ => Set.disjoint_left.mp (hJE e) hxJ hx⟩
  have hface : ∀ t : Section34SimplexIndex 𝒦 3, t ≠ s →
      ∀ e d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d := by
    intro t hts e d hwe hwd het hdt
    have hJt : Disjoint J (fblBd t) := Set.disjoint_left.mpr fun x hxJ hxt =>
      (hJN hxJ).2 (hinv.2.2.2.1 s t hts.symm
        ⟨(hinv.1 s).boundary_subset (hJP hxJ), (hinv.1 t).boundary_subset hxt⟩)
    obtain ⟨D, hD, hDS, hDE⟩ :=
      hfill t ((Finset.coe_subset.mpr hwe).trans het) hJt (fun e _ =>
        (hJE e).mono_right (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset)
    have hconn := hV.isConnected_boundary_sdiff_of_isPLCellOn hD hDS
    have hsub : section34VertexBallImage srcBd f₁ w \ D ⊆ S :=
      fun x hx => ⟨hx.1, fun hxJ => hx.2 (hD.boundary_subset hxJ)⟩
    have hpe : p e ∈ section34VertexBallImage srcBd f₁ w \ D :=
      ⟨(hES e hwe (hp e)).1, fun hxD => Set.disjoint_left.mp (hDE e het) hxD (hp e)⟩
    have hpd : p d ∈ section34VertexBallImage srcBd f₁ w \ D :=
      ⟨(hES d hwd (hp d)).1, fun hxD => Set.disjoint_left.mp (hDE d hdt) hxD (hp d)⟩
    exact connectedComponentIn_eq (hconn.isPreconnected.subset_connectedComponentIn hpe hsub hpd)
  have hconstant := hcut.eq_on_incident_edges_of_eq_on_other_faces s w hws c hface
  obtain ⟨e₀, _, -, -, -, hwe₀, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hcut.2.1 hcut.2.2.1 s w hws
  refine ⟨c e₀, ⟨⟨p e₀, mem_connectedComponentIn (hES e₀ hwe₀ (hp e₀))⟩,
    isPreconnected_connectedComponentIn⟩, connectedComponentIn_subset _ _, ?_⟩
  intro e hwe x hx
  have hmem := (hcut.isPLCellOn_splitDiskImage hf₁ e).isConnected.isPreconnected
    |>.subset_connectedComponentIn (hp e) (hES e hwe) hx
  change x ∈ c e at hmem
  change x ∈ c e₀
  rwa [hconstant e e₀ hwe hwe₀] at hmem

open Classical in
theorem exists_section34_connected_set_containing_other_split_disks
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (hwe₀ : w.1 ⊆ e₀.1)
    (he₀s : Section34Incident e₀.1 s.1) {J : Set M₂}
    (hJP : J ⊆ fblBd s ∪ section34SplitDiskImage srcBd f₁ e₀)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', e ≠ e₀ →
      Disjoint J (section34SplitDiskImage src f₁ e))
    (hfill : ∀ t : Section34SimplexIndex 𝒦 3, Section34Incident w.1 t.1 →
      Disjoint J (fblBd t) →
      (∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
        Disjoint J (section34SplitDiskImage srcBd f₁ e)) →
      ∃ D : Set M₂, IsPLCellOn 2 D J ∧ D ⊆ section34VertexBallImage srcBd f₁ w ∧
        ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 →
          Disjoint D (section34SplitDiskImage src f₁ e)) :
    ∃ Y : Set M₂, IsConnected Y ∧ Y ⊆ section34VertexBallImage srcBd f₁ w \ J ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → e ≠ e₀ →
        section34SplitDiskImage src f₁ e ⊆ Y := by
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  choose p hp using fun e : Section34EdgeIndex 𝒦 𝒦' =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
  let S := section34VertexBallImage srcBd f₁ w \ J
  let c := fun e : Section34EdgeIndex 𝒦 𝒦' => connectedComponentIn S (p e)
  have hES : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → e ≠ e₀ →
      section34SplitDiskImage src f₁ e ⊆ S := by
    intro e hwe he x hx
    exact ⟨hcut.splitDiskImage_subset_vertexBallBoundary hf₁ w e hwe hx,
      fun hxJ => Set.disjoint_left.mp (hJE e he) hxJ hx⟩
  have hface : ∀ t : Section34SimplexIndex 𝒦 3, ¬ Section34Incident e₀.1 t.1 →
      ∀ e d : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 → w.1 ⊆ d.1 →
        Section34Incident e.1 t.1 → Section34Incident d.1 t.1 → c e = c d := by
    intro t ht e d hwe hwd het hdt
    have he₀ : e ≠ e₀ := fun h => ht (h ▸ het)
    have hd₀ : d ≠ e₀ := fun h => ht (h ▸ hdt)
    have hst : s ≠ t := fun h => ht (h ▸ he₀s)
    have hJt : Disjoint J (fblBd t) := by
      apply Set.disjoint_left.mpr
      intro x hxJ hxt
      rcases hJP hxJ with hxs | hxe
      · exact (hJN hxJ).2 (hinv.2.2.2.1 s t hst
          ⟨(hinv.1 s).boundary_subset hxs, (hinv.1 t).boundary_subset hxt⟩)
      · exact Set.disjoint_left.mp
          (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ t e₀ ht)
          ((hinv.1 t).boundary_subset hxt)
          ((hcut.isPLCellOn_splitDiskImage hf₁ e₀).boundary_subset hxe)
    obtain ⟨D, hD, hDS, hDE⟩ :=
      hfill t ((Finset.coe_subset.mpr hwe).trans het) hJt (fun a hat =>
        (hJE a (fun h => ht (h ▸ hat))).mono_right
          (hcut.isPLCellOn_splitDiskImage hf₁ a).boundary_subset)
    have hconn := hV.isConnected_boundary_sdiff_of_isPLCellOn hD hDS
    have hsub : section34VertexBallImage srcBd f₁ w \ D ⊆ S :=
      fun x hx => ⟨hx.1, fun hxJ => hx.2 (hD.boundary_subset hxJ)⟩
    have hpe : p e ∈ section34VertexBallImage srcBd f₁ w \ D :=
      ⟨(hES e hwe he₀ (hp e)).1, fun hxD => Set.disjoint_left.mp (hDE e het) hxD (hp e)⟩
    have hpd : p d ∈ section34VertexBallImage srcBd f₁ w \ D :=
      ⟨(hES d hwd hd₀ (hp d)).1, fun hxD => Set.disjoint_left.mp (hDE d hdt) hxD (hp d)⟩
    exact connectedComponentIn_eq (hconn.isPreconnected.subset_connectedComponentIn hpe hsub hpd)
  have hconstant := hcut.eq_on_other_edges_of_eq_on_faces_avoiding_edge w e₀ hwe₀ c hface
  have hws : Section34Incident w.1 s.1 := (Finset.coe_subset.mpr hwe₀).trans he₀s
  obtain ⟨e₁, e₂, h₁₂, -, -, hw₁, hw₂, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hcut.2.1 hcut.2.2.1 s w hws
  obtain ⟨b, hwb, hb₀⟩ : ∃ b : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ b.1 ∧ b ≠ e₀ := by
    by_cases h₁₀ : e₁ = e₀
    · exact ⟨e₂, hw₂, fun h₂₀ => h₁₂ (h₁₀.trans h₂₀.symm)⟩
    · exact ⟨e₁, hw₁, h₁₀⟩
  refine ⟨c b, ⟨⟨p b, mem_connectedComponentIn (hES b hwb hb₀ (hp b))⟩,
    isPreconnected_connectedComponentIn⟩, connectedComponentIn_subset _ _, ?_⟩
  intro e hwe he₀ x hx
  have hmem := (hcut.isPLCellOn_splitDiskImage hf₁ e).isConnected.isPreconnected
    |>.subset_connectedComponentIn (hp e) (hES e hwe he₀) hx
  change x ∈ c e at hmem
  change x ∈ c b
  rwa [hconstant e b hwe hwb he₀ hb₀] at hmem

end DifferentialGeometry.Topology.PiecewiseLinear
