/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceArcNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusCycle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

local notation "E3" => EuclideanSpace ℝ (Fin 3)

omit [FiniteDimensional ℝ Ea] in
theorem section34Bigon_inter_faceBall_boundary
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {e : Section34EdgeIndex 𝒦 𝒦'}
    {B B' Bb Dj Jd : Set M₂} (hB : IsPLCellOn 1 B Bb) (hBf : B ⊆ fblBd s)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ section34SplitDiskImage srcBd f₁ e)
    (hBB' : B ∩ B' = Bb) (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ frontier (⋃ w, section34VertexBallImage src f₁ w))
    (hJ : Jd = B ∪ B') (hclean : Disjoint (Dj \ Jd) (fblBd s))
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hDc : Dj ⊆ c.source) : Dj ∩ fblBd s = B := by
  classical
  obtain ⟨-, -, -, -, -, hcross, -, -, -, -⟩ := id hinv
  have hBD : B ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inl hx)
  have hB'D : B' ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inr hx)
  have hBc := hBD.trans hDc
  have hB'c := hB'D.trans hDc
  have hBbc := hB'.boundary_subset.trans hB'c
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  obtain ⟨r, hr, hrBb⟩ := hB'.exists_isPLHomeomorphOn_image_chart hc hB'c
  have hBbi : c '' Bb ⊆ c '' B' := image_mono hB'.boundary_subset
  have hrbd : r '' stdSimplexBoundary 1 = (c '' B') ∩ (c '' Bb) := by
    rw [inter_eq_right.mpr hBbi, hrBb]
  obtain ⟨γ, hγ, hends⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hr hrbd
  rw [inter_eq_right.mpr hBbi] at hends
  let S := frontier (⋃ w, section34VertexBallImage src f₁ w)
  let A := fblBd s ∩ S
  have hpair : (c '' (A ∩ c.source)) ∩ (c '' B') ⊆ c '' Bb := by
    rw [← hends]
    refine inter_subset_endpoints_of_disk_boundary_crossing hq
      (S := c '' (S ∩ c.source))
      (B := c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (F := c '' B)
      ?_ hγ ?_ ?_ ?_ ?_ ?_ ?_
    · exact image_mono fun x hx => ⟨hDS hx, hDc hx⟩
    · exact image_mono fun x hx => ⟨hB'e hx, hB'c hx⟩
    · exact (hB.isCompact.image_of_continuousOn (c.continuousOn.mono hBc)).isClosed
    · rw [← c.injOn.image_inter hBc hB'c, hBB', hends]
    · rw [← hqJ, hJ, image_union]
    · refine disjoint_left.mpr ?_
      rintro _ ⟨⟨x, hxD, rfl⟩, hxJ⟩ ⟨y, ⟨⟨hyBd, _⟩, hyc⟩, hyx⟩
      have hy : y = x := c.injOn hyc (hDc hxD) hyx
      subst y
      apply disjoint_left.mp hclean ⟨hxD, ?_⟩ hyBd
      intro hxJd
      exact hxJ (hqJ ▸ ⟨x, hxJd, rfl⟩)
    · rintro _ ⟨⟨x, ⟨⟨hxBd, hxS⟩, hxc⟩, rfl⟩, y, hyB', hyx⟩
      have hy : y = x := c.injOn (hB'c hyB') hxc hyx
      subst y
      obtain ⟨c', hc', hxc', hcross'⟩ := hcross s e x ⟨hxBd, hB'e hyB'⟩
      exact hcross'.image_chart_of_mem_maximalAtlas hc hc' hxc hxc'
  apply subset_antisymm
  · rintro x ⟨hxD, hxBd⟩
    have hxJ : x ∈ Jd := by
      by_contra hxJ
      exact disjoint_left.mp hclean ⟨hxD, hxJ⟩ hxBd
    rw [hJ] at hxJ
    rcases hxJ with hxB | hxB'
    · exact hxB
    · have hxpair : c x ∈ (c '' (A ∩ c.source)) ∩ (c '' B') :=
        ⟨⟨x, ⟨⟨hxBd, hDS hxD⟩, hDc hxD⟩, rfl⟩, x, hxB', rfl⟩
      obtain ⟨y, hyBb, hyx⟩ := hpair hxpair
      have hy : y = x := c.injOn (hBbc hyBb) (hDc hxD) hyx
      exact hy ▸ hB.boundary_subset hyBb
  · exact fun x hx => ⟨hBD hx, hBf hx⟩

theorem section34Bigon_inter_splitDisk_boundary (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {w : Section34VertexIndex 𝒦 𝒦'} {e : Section34EdgeIndex 𝒦 𝒦'}
    {B B' Bb Dj Jd : Set M₂}
    (hBsplit : B ∩ (⋃ e', section34SplitDiskImage src f₁ e') = Bb)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ section34SplitDiskImage srcBd f₁ e)
    (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ section34VertexBallImage srcBd f₁ w ∩
      frontier (⋃ w', section34VertexBallImage src f₁ w')) (hJ : Jd = B ∪ B')
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hwc : section34VertexBallImage src f₁ w ⊆ c.source) :
    Dj ∩ section34SplitDiskImage srcBd f₁ e = B' := by
  classical
  obtain ⟨-, -, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends,
    -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  have hDw : Dj ⊆ section34VertexBallImage src f₁ w :=
    fun x hx => (hVcell w).boundary_subset (hDS hx).1
  have hDc := hDw.trans hwc
  obtain ⟨hW, hWbd⟩ := (hVcell w).isPLBall_image_chart hc hwc
  obtain ⟨p, hp, hpb⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hDsurface : c '' Dj ⊆ frontier (c '' section34VertexBallImage src f₁ w) := by
    rw [← hWbd]
    exact image_mono fun x hx => (hDS hx).1
  have hDinter : Dj ∩ section34SplitDiskImage src f₁ e ⊆ Jd := by
    intro x hx
    have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hx.2 (hDw hx.1)
    obtain ⟨a, b, -, heab, hEab⟩ := hends e
    have hEwsrc : src (.splitDisk e) ⊆ src (.vertexBall w) := by
      rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with rfl | rfl
      · rw [hEab]
        exact inter_subset_left
      · rw [hEab]
        exact inter_subset_right
    have hEw : section34SplitDiskImage src f₁ e ⊆
        section34VertexBallImage srcBd f₁ w := by
      refine image_mono fun y hy => ?_
      rw [hbd (.vertexBall w)]
      exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hEwsrc, by simp⟩, hy⟩
    have hEc : section34SplitDiskImage src f₁ e ⊆ c.source :=
      (hEw.trans (hVcell w).boundary_subset).trans hwc
    obtain ⟨q, hq, hqb⟩ := (hEcell e).exists_isPLHomeomorphOn_image_chart hc hEc
    have hcore : c '' section34SplitDiskImage src f₁ e \ q '' stdSimplexBoundary 2 ⊆
        frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj := by
      rintro _ ⟨⟨y, hy, rfl⟩, hyb⟩
      refine ⟨?_, ?_⟩
      · rw [← hWbd]
        exact mem_image_of_mem c (hEw hy)
      · rintro ⟨z, hz, hzy⟩
        have hzy' : z = y := c.injOn (hDc hz) (hEc hy) hzy
        have hyD : y ∈ Dj := hzy' ▸ hz
        have hynb : y ∉ section34SplitDiskImage srcBd f₁ e := by
          intro hyb'
          exact hyb (hqb ▸ mem_image_of_mem c hyb')
        exact (hDS hyD).2.2
          (hcut.splitDiskImage_sdiff_subset_interior_iUnion hh hctrl hgraph e ⟨hy, hynb⟩)
    have hEcl : c '' section34SplitDiskImage src f₁ e ⊆
        closure (frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj) := by
      rw [← hq.closure_sdiff_image_stdSimplexBoundary]
      exact closure_mono hcore
    have hcJ : c x ∈ c '' Jd := by
      rw [hpb, ← hW.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
        hp hDsurface]
      exact ⟨mem_image_of_mem c hx.1, hEcl (mem_image_of_mem c hx.2)⟩
    obtain ⟨y, hy, hyx⟩ := hcJ
    exact c.injOn (hDc (hD.boundary_subset hy)) (hDc hx.1) hyx ▸ hy
  apply subset_antisymm
  · rintro x ⟨hxD, hxe⟩
    have hxe' := (hEcell e).boundary_subset hxe
    have hxJ := hDinter ⟨hxD, hxe'⟩
    rw [hJ] at hxJ
    rcases hxJ with hxB | hxB'
    · exact hB'.boundary_subset (hBsplit ▸ ⟨hxB, mem_iUnion.mpr ⟨e, hxe'⟩⟩)
    · exact hxB'
  · exact fun x hx => ⟨hD.boundary_subset (hJ.symm ▸ Or.inr hx), hB'e hx⟩

theorem exists_section34BigonTraceArc (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {B Bb Dj : Set M₂}
    (hB : IsPLCellOn 1 B Bb) (hDB : Dj ∩ fblBd s = B)
    (hDS : Dj ⊆ frontier (⋃ w, section34VertexBallImage src f₁ w))
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hfc : fbl s ⊆ c.source)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    (hDc : Dj ⊆ c.source) {V : Set E3} (hV : IsOpen V) (hDV : c '' Dj ⊆ V) :
    ∃ (A : Set E3) (q : (Fin 2 → ℝ) → E3) (O : Set E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
      A ⊆ (c '' (fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))) ∩ V ∧
      (c '' Dj) ∩ A = c '' B ∧ Disjoint (c '' Dj) (q '' stdSimplexBoundary 1) ∧
      IsOpen O ∧ c '' Dj ⊆ O ∧ O ⊆ V ∧
      O ∩ (c '' (fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))) = O ∩ A := by
  classical
  obtain ⟨hfcell, -, hfavoid, -, hf5, -, -, -, -, hext⟩ := id hinv
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨_, _, _, _, hTcomp, O₀, hO₀, hfO₀, hfront₀⟩ :=
    exists_chart_section34FaceBall hh hcut hctrl hgraph hext s (hfavoid s)
  let T := section34FaceTorus (section34VertexBallImage src f₁) s
  let Sg := frontier (⋃ w, section34VertexBallImage src f₁ w)
  let X := c '' T
  let P := c '' fbl s
  have hVX (w : Section34VertexIndex 𝒦 𝒦') (hw : Section34Incident w.1 s.1) :
      section34VertexBallImage src f₁ w ⊆ T := by
    intro y hy
    exact mem_section34FaceTorus_iff.mpr ⟨w, hw, hy⟩
  have hVc (w : Section34VertexIndex 𝒦 𝒦') (hw : Section34Incident w.1 s.1) :
      section34VertexBallImage src f₁ w ⊆ c.source := (hVX w hw).trans hTc
  have hfbc : fblBd s ⊆ c.source := (hfcell s).boundary_subset.trans hfc
  have hfrTc : frontier T ⊆ c.source := hTcomp.isClosed.frontier_subset.trans hTc
  have hXT : c '' frontier T = frontier X := c.image_frontier_of_isCompact hTcomp hTc
  obtain ⟨hP, hPbd⟩ := (hfcell s).isPLBall_image_chart hc hfc
  have hX : IsPolyhedron X :=
    (isCombinatorialSolidTorus_image_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc).isPolyhedron
  have hreg : X ⊆ closure (interior X) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hyw⟩ := mem_section34FaceTorus_iff.mp hy
    obtain ⟨hW, -⟩ := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_image_chart hc
      (hVc w hw)
    have hcl : c y ∈ closure (interior (c '' section34VertexBallImage src f₁ w)) := by
      rw [hW.closure_interior_of_finrank (by simp)]
      exact mem_image_of_mem c hyw
    exact closure_mono (interior_mono (image_mono (hVX w hw))) hcl
  have htrace : fblBd s ∩ frontier T = fblBd s ∩ Sg := by
    ext y
    have hlocal : y ∈ fblBd s → (y ∈ frontier T ↔ y ∈ Sg) := by
      intro hy
      have hyO := hfO₀ ((hfcell s).boundary_subset hy)
      exact ⟨fun h => ((hfront₀.symm ▸ ⟨h, hyO⟩ : y ∈ Sg ∩ O₀)).1,
        fun h => ((hfront₀ ▸ ⟨h, hyO⟩ : y ∈ frontier T ∩ O₀)).1⟩
    exact ⟨fun hy => ⟨hy.1, (hlocal hy.1).mp hy.2⟩,
      fun hy => ⟨hy.1, (hlocal hy.1).mpr hy.2⟩⟩
  have hZ : frontier P ∩ frontier X = c '' (fblBd s ∩ Sg) := by
    rw [← hPbd, ← hXT, ← c.injOn.image_inter hfbc hfrTc, htrace]
  have hcross : ∀ x ∈ frontier P ∩ frontier X,
      HasPLCrossingAt (frontier P) (frontier X) x := by
    intro x hx
    rw [hZ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc := hfbc hy.1
    have hyO := hfO₀ ((hfcell s).boundary_subset hy.1)
    obtain ⟨c', hc', hyc', hcr⟩ := hf5 s y hy
    have hcr' := hcr.image_chart_of_mem_maximalAtlas hc hc' hyc hyc'
    refine hcr'.congr ?_ ?_
    · rw [inter_eq_left.mpr hfbc, hPbd]
      exact Filter.Eventually.of_forall fun _ => Iff.rfl
    · filter_upwards [eventually_mem_image_inter_source_iff hO₀ hfront₀ hyO hyc] with z hz
      rw [hz, inter_eq_left.mpr hfrTc, hXT]
  have hBD : B ⊆ Dj := fun y hy => (hDB.symm ▸ hy).1
  obtain ⟨b, hb, -⟩ := hB.exists_isPLHomeomorphOn_image_chart hc (hBD.trans hDc)
  have hF : IsPLBall 1 (c '' B) := ⟨b, hb⟩
  have hDF : (c '' Dj) ∩ (frontier P ∩ frontier X) = c '' B := by
    rw [hZ, ← c.injOn.image_inter hDc (inter_subset_left.trans hfbc)]
    congr 1
    rw [← hDB]
    ext y
    exact ⟨fun hy => ⟨hy.1, hy.2.1⟩, fun hy => ⟨hy.1, hy.2, hDS hy.1⟩⟩
  obtain ⟨A, q, O, hq, hA, hDA, hends, hO, hDO, hOV, hOA⟩ :=
    hP.isPLSphere_frontier.exists_arc_neighborhood_of_crossing_trace hX hreg hcross hF hDF
      hV hDV
  rw [hZ] at hA hOA
  exact ⟨A, q, O, hq, hA, hDA, hends, hO, hDO, hOV, hOA⟩

omit [FiniteDimensional ℝ Ea] in
theorem exists_section34BigonSplittingArc
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {e : Section34EdgeIndex 𝒦 𝒦'} {B' Bb Dj : Set M₂}
    (hB' : IsPLCellOn 1 B' Bb)
    (hDB' : Dj ∩ section34SplitDiskImage srcBd f₁ e = B')
    {c : OpenPartialHomeomorph M₂ E3} (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hEc : section34SplitDiskImage src f₁ e ⊆ c.source) (hDc : Dj ⊆ c.source)
    {V : Set E3} (hV : IsOpen V) (hDV : c '' Dj ⊆ V) :
    ∃ (A : Set E3) (q : (Fin 2 → ℝ) → E3) (O : Set E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) A ∧
      A ⊆ (c '' section34SplitDiskImage srcBd f₁ e) ∩ V ∧
      (c '' Dj) ∩ A = c '' B' ∧ Disjoint (c '' Dj) (q '' stdSimplexBoundary 1) ∧
      IsOpen O ∧ c '' Dj ⊆ O ∧ O ⊆ V ∧
      O ∩ (c '' section34SplitDiskImage srcBd f₁ e) = O ∩ A := by
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  have hE := hcut.isPLCellOn_splitDiskImage hf₁ e
  obtain ⟨r, hr, hrbd⟩ := hE.exists_isPLHomeomorphOn_image_chart hc hEc
  have hcircle : IsPLSphere 1 (c '' section34SplitDiskImage srcBd f₁ e) := by
    rw [hrbd]
    exact hr.isPLSphere_image_stdSimplexBoundary
  have hB'D : B' ⊆ Dj := fun x hx => (hDB'.symm ▸ hx).1
  obtain ⟨b, hb, -⟩ := hB'.exists_isPLHomeomorphOn_image_chart hc (hB'D.trans hDc)
  have hBball : IsPLBall 1 (c '' B') := ⟨b, hb⟩
  have hDF : (c '' Dj) ∩ (⋃ _ : Unit, c '' section34SplitDiskImage srcBd f₁ e) = c '' B' := by
    rw [iUnion_const, ← c.injOn.image_inter hDc (hE.boundary_subset.trans hEc), hDB']
  obtain ⟨A, q, O, hq, hA, hDA, hends, hO, hDO, hOV, hOA⟩ :=
    exists_arc_neighborhood_of_finite_circle_union
      (fun _ : Unit => c '' section34SplitDiskImage srcBd f₁ e) (fun _ => hcircle)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim) hBball hDF hV hDV
  simp only [iUnion_const] at hA hOA
  exact ⟨A, q, O, hq, hA, hDA, hends, hO, hDO, hOV, hOA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
