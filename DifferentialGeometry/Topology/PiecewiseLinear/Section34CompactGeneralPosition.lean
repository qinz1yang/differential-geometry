/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.exists_isPLHomeomorphOn_stdSimplex {d : ℕ} {S B : Set E3}
    (hS : IsPLCellOn d S B) : ∃ q : (Fin (d + 1) → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) S ∧ B = q '' stdSimplexBoundary d := by
  obtain ⟨q, hq, hB⟩ := hS.exists_isPLHomeomorphOn_image_chart
    (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid 3) (0 : E3))
    (by rw [chartAt_self_eq]; exact subset_univ S)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id] at hq hB
  exact ⟨q, hq, hB⟩

theorem IsPLCellOn.isPLBall_three {S B : Set E3} (hS : IsPLCellOn 3 S B) : IsPLBall 3 S := by
  obtain ⟨q, hq, -⟩ := hS.exists_isPLHomeomorphOn_stdSimplex
  exact ⟨q, hq⟩

theorem IsPLCellOn.isPLSphere_one_of_two {S B : Set E3} (hS : IsPLCellOn 2 S B) :
    IsPLSphere 1 B := by
  obtain ⟨q, hq, rfl⟩ := hS.exists_isPLHomeomorphOn_stdSimplex
  exact ⟨q, hq.restrict isPolyhedron_stdSimplexBoundary_two fun x hx => hx.1⟩

theorem boundary_subset_frontier_union_of_inter_eq {B₁ B₂ D Db : Set E3} (h₁ : IsPLBall 3 B₁)
    (h₂ : IsPLBall 3 B₂) (hD : IsPLCellOn 2 D Db) (hDeq : B₁ ∩ B₂ = D)
    (hD₁ : D ⊆ frontier B₁) : Db ⊆ frontier (B₁ ∪ B₂) := by
  obtain ⟨q, hq, rfl⟩ := hD.exists_isPLHomeomorphOn_stdSimplex
  have hB : ∀ b, IsPLBall 3 (cond b B₁ B₂) := fun b => by
    cases b
    · exact h₂
    · exact h₁
  have h3 : ∀ i j k : Bool, i ≠ j → k ≠ i → k ≠ j →
      Disjoint (cond i B₁ B₂ ∩ cond j B₁ B₂) (cond k B₁ B₂) := by
    intro i j k hij hki hkj
    exfalso
    cases i <;> cases j <;> cases k <;> simp_all
  have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (cond true B₁ B₂ ∩ cond false B₁ B₂) := by
    change IsPLHomeomorphOn q _ (B₁ ∩ B₂)
    rw [hDeq]
    exact hq
  have hsub := image_stdSimplexBoundary_subset_frontier_iUnion hB h3 (by decide) hq'
    (by change B₁ ∩ B₂ ⊆ frontier B₁; rw [hDeq]; exact hD₁)
  rwa [← union_eq_iUnion] at hsub

theorem exists_compactFaceBall_transverse {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
    {K K' : Geometry.SimplicialComplex ℝ E3} {src srcBd : Section34CompactLabelOf K K' → Set E3}
    {H : Finset E3 → Set E3} {env : Section34CompactSimplexIndex K 3 → Set E3}
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁) env)
    (s : Section34CompactSimplexIndex K 3) {F : Set E3} (hF : IsPLBall 3 F) (hFs : F ⊆ env s) :
    ∃ P : Set E3, IsPLBall 3 P ∧ F ⊆ interior P ∧ P ⊆ env s ∧
      (∀ y ∈ frontier P ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w),
        HasPLCrossingAt (frontier P) (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
          y) ∧
      (∀ e : Section34CompactEdgeIndex K K',
        ∀ y ∈ frontier P ∩ section34CompactSplitDiskImage srcBd f₁ e,
          HasPLSurfaceCurveCrossingAt (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (frontier P ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (section34CompactSplitDiskImage srcBd f₁ e) y) ∧
      (frontier P ∩ ⋃ e : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage srcBd f₁ e).Finite ∧
      ((fun y => connectedComponentIn
          (frontier P ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) y) ''
        (frontier P ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))).Finite := by
  classical
  obtain ⟨-, -, hK'fin, -, -, -, hcell, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, hends, -, -⟩ := hcut
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -, -⟩ := hgraph
  obtain ⟨henvo, -, hVenv, -⟩ := henv
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 2
  have hN : ∀ v : Section34CompactVertexIndex K K',
      src (.vertexBall v) ⊆ section34CompactCutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34BoundedLabel.vertexBall v)) v
  have hinj : InjOn f₁ (section34CompactCutNeighborhood src) := hf₁.bijOn.injOn
  have hGv : ∀ v : Section34CompactVertexIndex K K',
      IsPLHomeomorphInto 3 f₁ (src (.vertexBall v)) := fun v =>
    isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁ (hcell (.vertexBall v)).isPolyhedron
      (hN v)
  have hVcell : ∀ v : Section34CompactVertexIndex K K', IsPLCellOn 3
      (section34CompactVertexBallImage src f₁ v) (f₁ '' srcBd (.vertexBall v)) :=
    fun v => (hcell (.vertexBall v)).image (hGv v)
  have hVfr : ∀ v : Section34CompactVertexIndex K K',
      f₁ '' srcBd (.vertexBall v) = frontier (section34CompactVertexBallImage src f₁ v) :=
    fun v => ((hcell (.vertexBall v)).image_boundary_interior (hGv v)).1
  have hDN : ∀ e : Section34CompactEdgeIndex K K',
      src (.splitDisk e) ⊆ section34CompactCutNeighborhood src := by
    intro e
    obtain ⟨w, _, -, -, he⟩ := hends e
    rw [he]
    exact inter_subset_left.trans (hN w)
  have hDcell : ∀ e : Section34CompactEdgeIndex K K', IsPLCellOn 2
      (f₁ '' src (.splitDisk e)) (section34CompactSplitDiskImage srcBd f₁ e) := fun e =>
    (hcell (.splitDisk e)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hcell (.splitDisk e)).isPolyhedron (hDN e))
  have hTmem : ∀ y, y ∈ section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ↔
      ∃ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 ∧
        y ∈ section34CompactVertexBallImage src f₁ w := by
    intro y
    constructor
    · intro hy
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      refine ⟨a.1.2, ?_, hya⟩
      rw [← ha]
      exact a.2
    · rintro ⟨w, hw, hyw⟩
      exact mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hyw⟩
  have hUT : (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ env s =
      section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∩ env s := by
    ext y
    constructor
    · rintro ⟨hy, hyU⟩
      obtain ⟨w, hyw⟩ := mem_iUnion.mp hy
      by_cases hw : Section34Incident w.1 s.1
      · exact ⟨(hTmem y).mpr ⟨w, hw, hyw⟩, hyU⟩
      · have hmem : y ∈ env s ∩ section34CompactVertexBallImage src f₁ w := ⟨hyU, hyw⟩
        rw [hVenv s w hw] at hmem
        exact hmem.elim
    · rintro ⟨hy, hyU⟩
      obtain ⟨w, -, hyw⟩ := (hTmem y).mp hy
      exact ⟨mem_iUnion.mpr ⟨w, hyw⟩, hyU⟩
  have hR0 : frontier (⋃ w, section34CompactVertexBallImage src f₁ w) ∩ env s =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩
        env s := by
    rw [← frontier_inter_open_inter (henvo s), hUT, frontier_inter_open_inter (henvo s)]
  have hDbd : ∀ (e : Section34CompactEdgeIndex K K') (w : Section34CompactVertexIndex K K'),
      src (.splitDisk e) ⊆ src (.vertexBall w) → src (.splitDisk e) ⊆ srcBd (.vertexBall w) := by
    intro e w hsub x hx
    rw [hbd (.vertexBall w)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hx⟩
  obtain ⟨ι, hι⟩ : ∃ ι : Set (Section34CompactEdgeIndex K K'),
      ι = {e | Section34Incident e.1 s.1} := ⟨_, rfl⟩
  have hιm : ∀ e, e ∈ ι ↔ Section34Incident e.1 s.1 := fun e => by rw [hι]; exact Iff.rfl
  have hJsph : ∀ a : ι, IsPLSphere 1 (section34CompactSplitDiskImage srcBd f₁ a.1) :=
    fun a => (hDcell a.1).isPLSphere_one_of_two
  have hJT : ∀ a : ι, section34CompactSplitDiskImage srcBd f₁ a.1 ⊆
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro a
    obtain ⟨w, w', -, hew, hDw⟩ := hends a.1
    have hwe : (w.1 : Set E3) ∪ w'.1 ⊆ convexHull ℝ (s.1 : Set E3) := by
      rw [← hew]
      exact (hιm _).mp a.2
    have hw : Section34Incident w.1 s.1 := subset_union_left.trans hwe
    have hw' : Section34Incident w'.1 s.1 := subset_union_right.trans hwe
    have hinter : section34CompactVertexBallImage src f₁ w ∩
        section34CompactVertexBallImage src f₁ w' = f₁ '' src (.splitDisk a.1) := by
      rw [hDw]
      exact (hinj.image_inter (hN w) (hN w')).symm
    have hD₁ : f₁ '' src (.splitDisk a.1) ⊆ frontier (section34CompactVertexBallImage src f₁ w) :=
      by
        rw [← hVfr w]
        exact image_mono (hDbd a.1 w (by rw [hDw]; exact inter_subset_left))
    have hfr2 := boundary_subset_frontier_union_of_inter_eq (hVcell w).isPLBall_three
      (hVcell w').isPLBall_three (hDcell a.1) hinter hD₁
    have hOo : IsOpen (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
        section34CompactVertexBallImage src f₁ u)ᶜ :=
      (isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ =>
        (hVcell u).isCompact.isClosed).isOpen_compl
    have hJO : section34CompactSplitDiskImage srcBd f₁ a.1 ⊆
        (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
          section34CompactVertexBallImage src f₁ u)ᶜ := by
      rintro _ ⟨x, hx, rfl⟩ hy
      obtain ⟨u, hu, x', hx', hxx'⟩ := mem_iUnion₂.mp hy
      have hxD : x ∈ src (.splitDisk a.1) := (hcell (.splitDisk a.1)).boundary_subset hx
      have hx'x : x' = x := hinj (hN u hx') (hDN a.1 hxD) hxx'
      rw [hx'x] at hx'
      have hue : ((u.1 : Finset E3) : Set E3) ⊆ (w.1 : Set E3) ∪ w'.1 := by
        rw [← hew]
        exact Finset.coe_subset.mpr (hvertexEdge u a.1 ⟨x, hx', hxD⟩)
      rcases eq_or_eq_of_card_eq_one_of_subset_union u.2.2.1 w.2.2.1 w'.2.2.1 hue with h1 | h1
      · exact hu.1 (Subtype.ext h1)
      · exact hu.2 (Subtype.ext h1)
    have hTO : section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∩
        (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
          section34CompactVertexBallImage src f₁ u)ᶜ =
        (section34CompactVertexBallImage src f₁ w ∪ section34CompactVertexBallImage src f₁ w') ∩
        (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
          section34CompactVertexBallImage src f₁ u)ᶜ := by
      ext y
      constructor
      · rintro ⟨hyT, hyO⟩
        obtain ⟨u, -, hyu⟩ := (hTmem y).mp hyT
        refine ⟨?_, hyO⟩
        by_cases huw : u = w
        · rw [huw] at hyu
          exact Or.inl hyu
        by_cases huw' : u = w'
        · rw [huw'] at hyu
          exact Or.inr hyu
        exact absurd (mem_iUnion₂.mpr ⟨u, ⟨huw, huw'⟩, hyu⟩) hyO
      · rintro ⟨hy, hyO⟩
        refine ⟨(hTmem y).mpr ?_, hyO⟩
        rcases hy with hy | hy
        · exact ⟨w, hw, hy⟩
        · exact ⟨w', hw', hy⟩
    intro y hy
    have h1 : y ∈ frontier (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ w') ∩
        (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
          section34CompactVertexBallImage src f₁ u)ᶜ := ⟨hfr2 hy, hJO hy⟩
    rw [← frontier_inter_open_inter hOo, ← hTO, frontier_inter_open_inter hOo] at h1
    exact h1.1
  have hDdisj : ∀ e e' : Section34CompactEdgeIndex K K', e ≠ e' →
      src (.splitDisk e) ∩ src (.splitDisk e') = ∅ := by
    intro e e' hee
    by_contra hne
    obtain ⟨x, hxe, hxe'⟩ := nonempty_iff_ne_empty.mpr hne
    have hsub : ∀ a b : Section34CompactEdgeIndex K K', x ∈ src (.splitDisk a) →
        x ∈ src (.splitDisk b) → b.1 ⊆ a.1 := by
      intro a b ha hb
      obtain ⟨u, u', -, hbu, hDu⟩ := hends b
      have hb' : x ∈ src (.vertexBall u) ∩ src (.vertexBall u') := by
        rw [← hDu]
        exact hb
      rw [← Finset.coe_subset, hbu]
      exact union_subset (Finset.coe_subset.mpr (hvertexEdge u a ⟨x, hb'.1, ha⟩))
        (Finset.coe_subset.mpr (hvertexEdge u' a ⟨x, hb'.2, ha⟩))
    exact hee (Subtype.ext (Finset.Subset.antisymm (hsub e' e hxe' hxe) (hsub e e' hxe hxe')))
  have hJdisj : Pairwise fun a b : ι => Disjoint (section34CompactSplitDiskImage srcBd f₁ a.1)
      (section34CompactSplitDiskImage srcBd f₁ b.1) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have hxa := (hcell (.splitDisk a.1)).boundary_subset hx
    have hxb := (hcell (.splitDisk b.1)).boundary_subset hx'
    have hx'x : x' = x := hinj (hDN b.1 hxb) (hDN a.1 hxa) hxx'
    rw [hx'x] at hxb
    exact absurd ((hDdisj a.1 b.1 fun h => hab (Subtype.ext h)).subset ⟨hxa, hxb⟩)
      (notMem_empty x)
  have hEinc : ∀ (e : Section34CompactEdgeIndex K K') (y : E3), y ∈ env s →
      y ∈ section34CompactSplitDiskImage srcBd f₁ e → Section34Incident e.1 s.1 := by
    intro e y hyU hye
    obtain ⟨w, w', -, hew, hDw⟩ := hends e
    obtain ⟨x, hx, rfl⟩ := hye
    have hxD := (hcell (.splitDisk e)).boundary_subset hx
    rw [hDw] at hxD
    have hinc1 : ∀ u : Section34CompactVertexIndex K K', x ∈ src (.vertexBall u) →
        Section34Incident u.1 s.1 := by
      intro u hu
      by_contra hn
      have hmem : f₁ x ∈ env s ∩ section34CompactVertexBallImage src f₁ u :=
        ⟨hyU, mem_image_of_mem f₁ hu⟩
      rw [hVenv s u hn] at hmem
      exact hmem
    change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [hew]
    exact union_subset (hinc1 w hxD.1) (hinc1 w' hxD.2)
  have hJc : ∀ a : ι, IsClosed (section34CompactSplitDiskImage srcBd f₁ a.1) :=
    fun a => (hJsph a).isPolyhedron.isClosed
  obtain ⟨G, hGfin, hGcard, hGsp⟩ := exists_simplicialComplex_iUnion_isPLSphere_one hJsph hJdisj
  have : Finite G.faces := hGfin.to_subtype
  have hJloc : ∀ a : ι, ∀ y ∈ section34CompactSplitDiskImage srcBd f₁ a.1, ∀ᶠ z in 𝓝 y,
      z ∈ G.space ↔ z ∈ section34CompactSplitDiskImage srcBd f₁ a.1 := by
    intro a y hy
    have hO : IsOpen (⋃ b ∈ {b : ι | b ≠ a}, section34CompactSplitDiskImage srcBd f₁ b.1)ᶜ :=
      ((Set.toFinite _).isClosed_biUnion fun b _ => hJc b).isOpen_compl
    have hyO : y ∈ (⋃ b ∈ {b : ι | b ≠ a}, section34CompactSplitDiskImage srcBd f₁ b.1)ᶜ := by
      intro hy'
      obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy'
      exact Set.disjoint_left.mp (hJdisj hb) hyb hy
    filter_upwards [hO.mem_nhds hyO] with z hz
    rw [hGsp]
    constructor
    · intro hzG
      obtain ⟨b, hzb⟩ := mem_iUnion.mp hzG
      by_cases hba : b = a
      · rw [hba] at hzb
        exact hzb
      · exact absurd (mem_biUnion (show b ∈ {b : ι | b ≠ a} from hba) hzb) hz
    · exact fun hza => mem_iUnion.mpr ⟨a, hza⟩
  obtain ⟨S₁, S₂, -, -, hT, -⟩ := hnest s
  obtain ⟨hTpoly, ⟨ψ⟩⟩ := hT.isPLTorus_frontier
  obtain ⟨T₀, hT₀fin, hT₀sp⟩ := hTpoly.exists_simplicialComplex
  have : Finite T₀.faces := hT₀fin.to_subtype
  have hGS : G.space ⊆ T₀.space := by
    rw [hGsp, hT₀sp]
    exact iUnion_subset hJT
  obtain ⟨L, hLT₀, hLfin, hGL⟩ := exists_isSubdivision_restrict_isSubdivision T₀ G hGS
  have : Finite L.faces := hLfin.to_subtype
  have hLsp : L.space =
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :=
    hLT₀.space_eq.trans hT₀sp
  have hLman : IsCombinatorialManifold 2 L :=
    isCombinatorialManifold_two_of_homeomorph_sphere_prod L ((Homeomorph.setCongr hLsp).trans ψ)
  have hCsp : (restrict L G.space).space = G.space := hGL.space_eq
  obtain ⟨B', hB', hFB', hB'U⟩ := hF.exists_isPLBall_subset_interior_of_isOpen (henvo s) hFs
  obtain ⟨P', hP', hFP', hP'U, hcross, hcurve, hfinC, M, Nc, hMfin, hNM, -, hNsp, -⟩ :=
    exists_isPLBall_transverse_of_isPLBall hB' hF.isPolyhedron.isCompact hFB' (henvo s) hB'U L
      (restrict L G.space) hLman.isCombinatorialManifoldWithBoundary (restrict_faces_subset L _)
      (fun t ht => hGL.card_le hGcard ht)
      (fun t _ _ hB => Set.eq_empty_iff_forall_notMem.mp hLman.boundaryComplex_faces_eq_empty t
        (by convert hB))
  have hfrU : frontier P' ⊆ env s := hP'.isPolyhedron.isClosed.frontier_subset.trans hP'U
  have hR1 : ∀ y ∈ env s, ∀ᶠ z in 𝓝 y,
      z ∈ L.space ↔ z ∈ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) := by
    intro y hy
    filter_upwards [(henvo s).mem_nhds hy] with z hz
    rw [hLsp]
    have := Set.ext_iff.mp hR0 z
    exact ⟨fun h1 => (this.mpr ⟨h1, hz⟩).1, fun h1 => (this.mp ⟨h1, hz⟩).1⟩
  refine ⟨P', hP', hFP', hP'U, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨hyP, hyX⟩
    have hyL : y ∈ L.space := ((hR1 y (hfrU hyP)).self_of_nhds).mpr hyX
    exact (hcross y ⟨hyP, hyL⟩).congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
      (hR1 y (hfrU hyP))
  · rintro e y ⟨hyP, hye⟩
    have he : e ∈ ι := (hιm e).mpr (hEinc e y (hfrU hyP) hye)
    have hyC : y ∈ (restrict L G.space).space := by
      rw [hCsp, hGsp]
      exact mem_iUnion.mpr ⟨⟨e, he⟩, hye⟩
    have hc : HasPLCurveCrossingOnAt (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
        (frontier P' ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
        (section34CompactSplitDiskImage srcBd f₁ e) y :=
      (hcurve y ⟨hyP, hyC⟩).congr (hR1 y (hfrU hyP))
        (by
          filter_upwards [hR1 y (hfrU hyP)] with z hz
          exact and_congr Iff.rfl hz)
        (by
          filter_upwards [hJloc ⟨e, he⟩ y hye] with z hz
          rw [hCsp]
          exact hz)
    exact hc
  · refine hfinC.subset ?_
    rintro y ⟨hyP, hyE⟩
    obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
    have he : e ∈ ι := (hιm e).mpr (hEinc e y (hfrU hyP) hye)
    refine ⟨hyP, ?_⟩
    rw [hCsp, hGsp]
    exact mem_iUnion.mpr ⟨⟨e, he⟩, hye⟩
  · have : Finite Nc.faces := (hMfin.subset hNM).to_subtype
    have htr : frontier P' ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) =
        ⋃ σ : Nc.faces, convexHull ℝ (σ.1 : Set E3) := by
      have h1 : frontier P' ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w) =
          Nc.space := by
        rw [hNsp]
        ext y
        constructor
        · rintro ⟨hyP, hyX⟩
          exact ⟨hyP, ((hR1 y (hfrU hyP)).self_of_nhds).mpr hyX⟩
        · rintro ⟨hyP, hyL⟩
          exact ⟨hyP, ((hR1 y (hfrU hyP)).self_of_nhds).mp hyL⟩
      rw [h1]
      ext x
      rw [Geometry.SimplicialComplex.mem_space_iff, mem_iUnion]
      exact ⟨fun ⟨σ, hσ, hx⟩ => ⟨⟨σ, hσ⟩, hx⟩, fun ⟨σ, hx⟩ => ⟨σ.1, σ.2, hx⟩⟩
    exact finite_image_connectedComponentIn_of_eq_iUnion
      (fun σ => (convex_convexHull ℝ _).isPreconnected) htr

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactFaceBallsGeneralPosition
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hfam : ∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl s) (fblBd s) ∧
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl s) ∧
      fbl s ⊆ env s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ s : Section34CompactSimplexIndex K 3, IsPLCellOn 3 (fbl' s) (fblBd' s) ∧
        h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ interior (fbl' s) ∧
        fbl' s ⊆ env s) ∧
      (∀ s, ∀ y ∈ fblBd' s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w),
        HasPLCrossingAt (fblBd' s)
          (frontier (⋃ w, section34CompactVertexBallImage src f₁ w)) y) ∧
      (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
        ∀ y ∈ fblBd' s ∩ section34CompactSplitDiskImage srcBd f₁ e,
          HasPLSurfaceCurveCrossingAt
            (frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (fblBd' s ∩ frontier (⋃ w, section34CompactVertexBallImage src f₁ w))
            (section34CompactSplitDiskImage srcBd f₁ e) y) ∧
      (∀ s, (fblBd' s ∩ ⋃ e : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage srcBd f₁ e).Finite) ∧
      ∀ s, (section34CompactTraceComponents (section34CompactVertexBallImage src f₁)
        fblBd' s).Finite := by
  choose P hP hFP hPU hcr hcu hfin htr using fun s =>
    exists_compactFaceBall_transverse hcut hgraph henv s (hfam s).1.isPLBall_three (hfam s).2.2
  exact ⟨P, fun s => frontier (P s), fun s => ⟨(hP s).isPLCellOn_frontier,
    (hfam s).2.1.trans (interior_subset.trans (hFP s)), hPU s⟩, hcr, hcu, hfin, htr⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
