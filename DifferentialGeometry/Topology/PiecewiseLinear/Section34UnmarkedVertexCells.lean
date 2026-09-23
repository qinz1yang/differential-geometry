import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCoveringEdgeCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexEdgePasting
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexCellIntersections
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology Function

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem interior_inter_eq_of_inter_eq {X : Type*} [TopologicalSpace X]
    {A B V : Set X} (hV : IsOpen V) (heq : A ∩ V = B ∩ V) :
    interior A ∩ V = interior B ∩ V := by
  simpa only [interior_inter, hV.interior_eq] using congrArg interior heq

private theorem frontier_inter_eq_of_inter_eq {X : Type*} [TopologicalSpace X]
    {A B V : Set X} (hA : IsClosed A) (hB : IsClosed B) (hV : IsOpen V)
    (heq : A ∩ V = B ∩ V) : frontier A ∩ V = frontier B ∩ V := by
  have hi := interior_inter_eq_of_inter_eq hV heq
  rw [hA.frontier_eq, hB.frontier_eq]
  ext x
  have h := Set.ext_iff.mp heq x
  have h' := Set.ext_iff.mp hi x
  simp only [mem_inter_iff, mem_sdiff] at *
  tauto

theorem exists_section34_unmarked_vertex_cells
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}
    (hU : IsOpen U) (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (section34CutNeighborhood src) (graphSkeletonSpace 𝒦) U)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (ends e).1 ≠ (ends e).2 ∧
      (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (Cc : Section34VertexIndex 𝒦 𝒦' → Set M)
    (hCc : ∀ w, src (.vertexBall w) ⊆ interior (Cc w))
    (hCcLF : LocallyFinite fun w => {x : U | (x : M) ∈ Cc w})
    (O : Section34EdgeIndex 𝒦 𝒦' → Set M)
    (hO : ∀ e, IsOpen (O e)) (hDO : ∀ e, src (.splitDisk e) ⊆ O e)
    (hdisj : Pairwise (Disjoint on O)) :
    ∃ Cp : Section34VertexIndex 𝒦 𝒦' → Set M,
      (∀ w, IsPLCellOn 3 (Cp w) (frontier (Cp w))) ∧
      (∀ e, IsPolyhedralSphere (n := 3) 1
          (frontier (Cp (ends e).1) ∩ frontier (Cp (ends e).2)) ∧
        frontier (Cp (ends e).1) ∩ frontier (Cp (ends e).2) ⊆ src (.splitDisk e)) ∧
      (∀ w w', w ≠ w' → (¬ ∃ e : Section34EdgeIndex 𝒦 𝒦',
          (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) →
        Disjoint (Cp w) (Cp w')) ∧
      (∀ w, Cp w ⊆ interior (Cc w)) ∧
      graphSkeletonSpace 𝒦 ⊆ ⋃ w, interior (Cp w) ∧
      (LocallyFinite fun w => {x : U | (x : M) ∈ Cp w}) ∧
      (∀ e, Cp (ends e).1 ∩ Cp (ends e).2 ⊆ O e) ∧
      ∀ e, (interior (Cp (ends e).1) ∩ interior (Cp (ends e).2)).Nonempty := by
  classical
  let O' := fun e => O e ∩ (interior (Cc (ends e).1) ∩ interior (Cc (ends e).2))
  have hO' (e) : IsOpen (O' e) := (hO e).inter (isOpen_interior.inter isOpen_interior)
  have hDO' (e) : src (.splitDisk e) ⊆ O' e := by
    intro x hx
    have hp := (hends e).2.2.subset hx
    exact ⟨hDO e hx, hCc _ hp.1, hCc _ hp.2⟩
  choose V A B hV hDV hVO hforeign hA hB hmeet hcircle hcircleD hlens hpair hgraph
    hdiffA hdiffB K φ₀ φ₁ hK hKV hφ₀ hφ₁ himage₀ himage₁ hfix₀ hfix₁ using
    fun e => exists_section34_graph_covering_edge_cells hU hframe hN ends
      (fun e => (hends e).2) e (hO' e) (hDO' e)
  have hVO' (e) : V e ⊆ O e := fun x hx => (hVO e hx).1.1
  have hdisV : Pairwise (Disjoint on V) := fun e d hed =>
    (hdisj hed).mono (hVO' e) (hVO' d)
  obtain ⟨Φ, hΦ, -, himage, hforeignFix, hfix⟩ := exists_section34_vertex_embeddings
    hframe ends (fun e => (hends e).1) (fun e => (hends e).2.2)
    V K φ₀ φ₁ hV (fun e => (hK e).isClosed) hKV hdisV hφ₀ hφ₁ hfix₀ hfix₁
  let Cp := fun w => Φ w '' src (.vertexBall w)
  have hCp (w) : IsPLCellOn 3 (Cp w) (frontier (Cp w)) := by
    have hc : IsPLCellOn 3 (src (.vertexBall w)) (srcBd (.vertexBall w)) :=
      hframe.2.2.2.1 (.vertexBall w)
    have hc' := hc.image (hΦ w)
    rwa [hc'.boundary_eq_frontier] at hc'
  have hlocal (e) : Cp (ends e).1 ∩ V e = A e ∩ V e ∧
      Cp (ends e).2 ∩ V e = B e ∩ V e := by
    simpa only [himage₀ e, himage₁ e, Cp] using himage e
  have hlocalI (e) : interior (Cp (ends e).1) ∩ V e = interior (A e) ∩ V e ∧
      interior (Cp (ends e).2) ∩ V e = interior (B e) ∩ V e :=
    ⟨interior_inter_eq_of_inter_eq (hV e) (hlocal e).1,
      interior_inter_eq_of_inter_eq (hV e) (hlocal e).2⟩
  have hlocalF (e) : frontier (Cp (ends e).1) ∩ V e = frontier (A e) ∩ V e ∧
      frontier (Cp (ends e).2) ∩ V e = frontier (B e) ∩ V e :=
    ⟨frontier_inter_eq_of_inter_eq (hCp _).isCompact.isClosed (hA e).isCompact.isClosed
        (hV e) (hlocal e).1,
      frontier_inter_eq_of_inter_eq (hCp _).isCompact.isClosed (hB e).isCompact.isClosed
        (hV e) (hlocal e).2⟩
  have hforeignCp (e w) (hw₀ : w ≠ (ends e).1) (hw₁ : w ≠ (ends e).2) :
      Disjoint (V e) (Cp w) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, hy, heq⟩
    have hyx : y = x := (Φ w).injective (heq.trans (hforeignFix e w hw₀ hw₁ hx).symm)
    exact Set.disjoint_left.mp (hforeign e w hw₀ hw₁) hx (hyx ▸ hy)
  have hout (w) {x} (hx : x ∉ ⋃ e, V e) :
      x ∈ Cp w ↔ x ∈ src (.vertexBall w) := by
    have hf : Φ w x = x := hfix w fun hxK => by
      obtain ⟨e, -, he⟩ := mem_iUnion₂.mp hxK
      exact hx (mem_iUnion.mpr ⟨e, hKV e he⟩)
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Φ w).injective (he.trans hf.symm) ▸ hy
    · intro hy
      exact ⟨x, hy, hf⟩
  have hend (e w) {x} (hxV : x ∈ V e) (hx : x ∈ Cp w) :
      w = (ends e).1 ∨ w = (ends e).2 := by
    by_contra hn
    push Not at hn
    exact Set.disjoint_left.mp (hforeignCp e w hn.1 hn.2) hxV hx
  have hedge (e d) (ha : (ends e).1 = (ends d).1 ∨ (ends e).1 = (ends d).2)
      (hb : (ends e).2 = (ends d).1 ∨ (ends e).2 = (ends d).2) : e = d := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [(hends e).2.1, (hends d).2.1]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ((hends e).1 (ha.trans hb.symm)).elim
    · rw [ha, hb]
    · rw [ha, hb, union_comm]
    · exact ((hends e).1 (ha.trans hb.symm)).elim
  have hlensV (e) : Cp (ends e).1 ∩ Cp (ends e).2 ⊆ V e := by
    intro x hx
    by_cases hv : x ∈ ⋃ d, V d
    · obtain ⟨d, hd⟩ := mem_iUnion.mp hv
      exact hedge e d (hend d _ hd hx.1) (hend d _ hd hx.2) ▸ hd
    · exact hDV e ((hends e).2.2.symm ▸ ⟨(hout _ hv).mp hx.1, (hout _ hv).mp hx.2⟩)
  have hCpCc (w) : Cp w ⊆ interior (Cc w) := by
    rintro x ⟨y, hy, rfl⟩
    by_contra hx
    have hxf : Φ w (Φ w y) = Φ w y := hfix w fun hxK => by
      obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxK
      have hC := (hVO e (hKV e hxe)).1.2
      exact hx (he.elim (fun he => he.symm ▸ hC.1) (fun he => he.symm ▸ hC.2))
    exact hx (((Φ w).injective hxf).symm ▸ hCc w hy)
  refine ⟨Cp, hCp, ?_, ?_, hCpCc, ?_, ?_, fun e => (hlensV e).trans (hVO' e), ?_⟩
  · intro e
    have heq : frontier (Cp (ends e).1) ∩ frontier (Cp (ends e).2) =
        frontier (A e) ∩ frontier (B e) := by
      ext x
      constructor
      · intro hx
        have hv := hlensV e ⟨(hCp _).isCompact.isClosed.frontier_subset hx.1,
          (hCp _).isCompact.isClosed.frontier_subset hx.2⟩
        exact ⟨((hlocalF e).1.subset ⟨hx.1, hv⟩).1,
          ((hlocalF e).2.subset ⟨hx.2, hv⟩).1⟩
      · intro hx
        have hv := hDV e (hcircleD e hx)
        exact ⟨((hlocalF e).1.symm.subset ⟨hx.1, hv⟩).1,
          ((hlocalF e).2.symm.subset ⟨hx.2, hv⟩).1⟩
    rw [heq]
    exact ⟨hcircle e, hcircleD e⟩
  · intro w w' hne hn
    apply Set.disjoint_left.mpr
    intro x hx hx'
    by_cases hv : x ∈ ⋃ e, V e
    · obtain ⟨e, he⟩ := mem_iUnion.mp hv
      apply hn
      refine ⟨e, ?_⟩
      rcases hend e w he hx with hw | hw <;> rcases hend e w' he hx' with hw' | hw'
      · exact (hne (hw.trans hw'.symm)).elim
      · exact Or.inl ⟨hw, hw'⟩
      · exact Or.inr ⟨hw, hw'⟩
      · exact (hne (hw.trans hw'.symm)).elim
    · exact Set.disjoint_left.mp
        (section34_vertex_cells_disjoint_of_nonadjacent hframe ends (fun e => (hends e).2)
          hne hn) ((hout w hv).mp hx) ((hout w' hv).mp hx')
  · intro x hx
    by_cases hv : x ∈ ⋃ e, V e
    · obtain ⟨e, he⟩ := mem_iUnion.mp hv
      rcases hgraph e ⟨hx, he⟩ with ha | hb
      · exact mem_iUnion.mpr ⟨(ends e).1, ((hlocalI e).1.symm.subset ⟨ha, he⟩).1⟩
      · exact mem_iUnion.mpr ⟨(ends e).2, ((hlocalI e).2.symm.subset ⟨hb, he⟩).1⟩
    · have hnotD : x ∉ ⋃ e, src (.splitDisk e) := by
        intro hxD
        obtain ⟨e, he⟩ := mem_iUnion.mp hxD
        exact hv (mem_iUnion.mpr ⟨e, hDV e he⟩)
      obtain ⟨w, hw⟩ := mem_iUnion.mp
        ((section34_graph_subset_vertex_interiors_union_splitDisks hU hframe hN hx).resolve_right
          hnotD)
      have hfin : {e | w = (ends e).1 ∨ w = (ends e).2}.Finite := by
        have h₀ := finite_splitDisk_of_section34CutFrame hframe (fun e => (ends e).1)
          (fun e => (hends e).2.2.subset.trans inter_subset_left) w
        have h₁ := finite_splitDisk_of_section34CutFrame hframe (fun e => (ends e).2)
          (fun e => (hends e).2.2.subset.trans inter_subset_right) w
        convert h₀.union h₁ using 1
        ext e
        simp only [mem_ofPred_eq, mem_union, eq_comm]
      let L := ⋃ (e) (_ : w = (ends e).1 ∨ w = (ends e).2), K e
      have hL : IsClosed L := hfin.isClosed_biUnion (fun e _ => (hK e).isClosed)
      have hxL : x ∉ L := by
        intro hxL
        obtain ⟨e, -, he⟩ := mem_iUnion₂.mp hxL
        exact hv (mem_iUnion.mpr ⟨e, hKV e he⟩)
      refine mem_iUnion.mpr ⟨w, interior_maximal ?_
        (isOpen_interior.inter hL.isOpen_compl) ⟨hw, hxL⟩⟩
      rintro y ⟨hy, hyL⟩
      exact ⟨y, interior_subset hy, hfix w hyL⟩
  · exact hCcLF.subset (fun w x hx =>
      (interior_subset : interior (Cc w) ⊆ Cc w) (hCpCc w hx))
  · intro e
    obtain ⟨x, hxA, hxB⟩ := hmeet e
    have hv := hlens e ⟨interior_subset hxA, interior_subset hxB⟩
    exact ⟨x, ((hlocalI e).1.symm.subset ⟨hxA, hv⟩).1,
      ((hlocalI e).2.symm.subset ⟨hxB, hv⟩).1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
