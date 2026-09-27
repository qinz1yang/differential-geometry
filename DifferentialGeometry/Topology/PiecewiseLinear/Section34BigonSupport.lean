/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {H : Finset Ea → Set M₂} {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem section34Bigon_disjoint_other_faceBall
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s s' : Section34SimplexIndex 𝒦 3} (hss' : s ≠ s')
    {e : Section34EdgeIndex 𝒦 𝒦'} {B B' Bb Dj Jd : Set M₂}
    (hB : IsPLCellOn 1 B Bb) (hBf : B ⊆ fblBd s)
    (hB' : IsPLCellOn 1 B' Bb) (hB'e : B' ⊆ tgtEBd e) (hBB' : B ∩ B' = Bb)
    (hD : IsPLCellOn 2 Dj Jd) (hDS : Dj ⊆ frontier (⋃ w, tgtV w))
    (hJ : Jd = B ∪ B') (hclean : Disjoint (Dj \ Jd) (fblBd s'))
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂) (hDc : Dj ⊆ c.source) :
    Disjoint Dj (fbl s') := by
  classical
  obtain ⟨hfcell, -, -, hsep, -, hcross, -, -, -, -⟩ := hinv
  have hBD : B ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inl hx)
  have hB'D : B' ⊆ Dj := fun x hx => hD.boundary_subset (hJ.symm ▸ Or.inr hx)
  have hBc := hBD.trans hDc
  have hB'c := hB'D.trans hDc
  have hBbc := hB'.boundary_subset.trans hB'c
  have hBavoid : Disjoint B (fbl s') := by
    refine disjoint_left.mpr fun x hxB hxf => ?_
    exact (hDS (hBD hxB)).2
      (hsep s s' hss' ⟨(hfcell s).boundary_subset (hBf hxB), hxf⟩)
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  obtain ⟨r, hr, hrBb⟩ := hB'.exists_isPLHomeomorphOn_image_chart hc hB'c
  have hBbi : c '' Bb ⊆ c '' B' := image_mono hB'.boundary_subset
  have hrbd : r '' stdSimplexBoundary 1 = (c '' B') ∩ (c '' Bb) := by
    rw [inter_eq_right.mpr hBbi, hrBb]
  obtain ⟨γ, hγ, hends⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hr hrbd
  rw [inter_eq_right.mpr hBbi] at hends
  let S := frontier (⋃ w, tgtV w)
  let A := fblBd s' ∩ S
  have hpair : (c '' (A ∩ c.source)) ∩ (c '' B') ⊆ c '' Bb := by
    rw [← hends]
    refine inter_subset_endpoints_of_disk_boundary_crossing hq
      (S := c '' (S ∩ c.source)) (B := c '' (tgtEBd e ∩ c.source)) (F := c '' B)
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
      obtain ⟨c', hc', hxc', hcross'⟩ := hcross s' e x ⟨hxBd, hB'e hyB'⟩
      exact hcross'.image_chart_of_mem_maximalAtlas hc hc' hxc hxc'
  have hB'avoid : Disjoint B' (fblBd s') := by
    refine disjoint_left.mpr fun x hxB' hxBd => ?_
    have hxpair : c x ∈ (c '' (A ∩ c.source)) ∩ (c '' B') :=
      ⟨⟨x, ⟨⟨hxBd, hDS (hB'D hxB')⟩, hB'c hxB'⟩, rfl⟩, x, hxB', rfl⟩
    obtain ⟨y, hyBb, hyx⟩ := hpair hxpair
    have hy : y = x := c.injOn (hBbc hyBb) (hB'c hxB') hyx
    subst y
    exact disjoint_left.mp hBavoid (hB.boundary_subset hyBb)
      ((hfcell s').boundary_subset hxBd)
  have hDavoid : Disjoint Dj (fblBd s') := by
    refine disjoint_left.mpr fun x hxD hxBd => ?_
    by_cases hxJ : x ∈ Jd
    · rw [hJ] at hxJ
      rcases hxJ with hxB | hxB'
      · exact disjoint_left.mp hBavoid hxB ((hfcell s').boundary_subset hxBd)
      · exact disjoint_left.mp hB'avoid hxB' hxBd
    · exact disjoint_left.mp hclean ⟨hxD, hxJ⟩ hxBd
  have hfr : Disjoint Dj (frontier (fbl s')ᶜ) := by
    rw [frontier_compl, ← (hfcell s').boundary_eq_frontier]
    exact hDavoid
  obtain ⟨x, hxB⟩ := hB.nonempty
  have hsub : Dj ⊆ (fbl s')ᶜ := IsPreconnected.subset_of_disjoint_frontier
    hD.isConnected.isPreconnected
    ⟨x, hBD hxB, fun hxf => disjoint_left.mp hBavoid hxB hxf⟩ hfr
  exact disjoint_left.mpr fun x hxD hxf => hsub hxD hxf

theorem Section34Exterior.locallyFinite_faceBall
    (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {η : M₁ → ℝ}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H) :
    (∀ s, fbl s ⊆ h '' U) ∧
      LocallyFinite (fun s => (Subtype.val : h '' U → M₂) ⁻¹' fbl s) := by
  classical
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, hHU, hHlf, -, -, -⟩ := hctrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcof⟩ := hcut
  choose ts hts using hcof
  have hsub : ∀ s : Section34SimplexIndex 𝒦 3, fbl s ⊆ H (ts s).1 := by
    intro s x hx
    apply interior_subset (hext1 (ts s) ?_)
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hts s, hx⟩)
  refine ⟨fun s => (hsub s).trans (hHU (ts s).1 (ts s).2.1), ?_⟩
  apply locallyFinite_subtype_of_subset_carriers (h '' U) fbl
    (fun t : Section34SimplexIndex 𝒦 4 => H t.1) ts hsub
  · intro t
    refine (finite_setOf_section34Incident t).subset ?_
    intro s hs
    rw [← hs]
    exact hts s
  · intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
    rintro t ⟨_, _, htV⟩
    exact ⟨t.2.1, htV⟩

theorem exists_isOpen_section34FaceBall_avoiding
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {η : M₁ → ℝ}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (s : Section34SimplexIndex 𝒦 3) {D : Set M₂} (hDU : D ⊆ h '' U)
    (havoid : ∀ s', s' ≠ s → Disjoint D (fbl s')) :
    ∃ O : Set M₂, IsOpen O ∧ D ⊆ O ∧ Disjoint O (⋃ s' ≠ s, fbl s') := by
  obtain ⟨hfcell, -, -, -, -, -, -, -, -, hext⟩ := hinv
  obtain ⟨hfU, hlf⟩ := hext.locallyFinite_faceBall hcut hctrl
  let F : {s' : Section34SimplexIndex 𝒦 3 // s' ≠ s} → Set (h '' U) :=
    fun s' => Subtype.val ⁻¹' fbl s'.1
  have hFc : IsClosed (⋃ s', F s') :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun s' => (hfcell s'.1).isCompact.isClosed.preimage continuous_subtype_val)
  obtain ⟨O, hO, hOF⟩ := isOpen_induced_iff.mp hFc.isOpen_compl
  refine ⟨O, hO, ?_, ?_⟩
  · intro x hxD
    have hx : (⟨x, hDU hxD⟩ : h '' U) ∈ (⋃ s', F s')ᶜ := by
      intro hxF
      obtain ⟨s', hxs'⟩ := mem_iUnion.mp hxF
      exact disjoint_left.mp (havoid s'.1 s'.2) hxD hxs'
    exact (Set.ext_iff.mp hOF ⟨x, hDU hxD⟩).mpr hx
  · refine disjoint_left.mpr ?_
    intro x hxO hxf
    obtain ⟨s', hs', hxs'⟩ := mem_iUnion₂.mp hxf
    have hx : (⟨x, hfU s' hxs'⟩ : h '' U) ∈ (⋃ s', F s')ᶜ :=
      (Set.ext_iff.mp hOF ⟨x, hfU s' hxs'⟩).mp hxO
    exact hx (mem_iUnion.mpr ⟨⟨s', hs'⟩, hxs'⟩)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
private theorem isCompact_image_section34SimplexRim (hh : ContinuousOn h U)
    (s : Section34SimplexIndex 𝒦 3) : IsCompact (h '' simplexRim 𝒦 s.1) := by
  have hfin : {t : Finset Ea | t ⊂ s.1}.Finite :=
    s.1.powerset.finite_toSet.subset fun t ht => Finset.mem_powerset.mpr ht.le
  have hcont : ContinuousOn (h ∘ 𝒦.map) 𝒦.complex.space :=
    hh.comp 𝒦.continuousOn 𝒦.bijOn.mapsTo
  simp only [simplexRim, image_iUnion]
  refine hfin.isCompact_biUnion fun t ht => ?_
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp [simplexBody]
  · have htf : t ∈ 𝒦.complex.faces := 𝒦.complex.down_closed s.2.1 ht.le hne
    rw [simplexBody, image_image]
    exact (t.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (hcont.mono (𝒦.complex.convexHull_subset_space htf))

theorem exists_isOpen_section34BigonSupport
    (hh : IsEmbedding (U.domRestrict h))
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {η : M₁ → ℝ}
    {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {D : Set M₂} (hDw : D ⊆ section34VertexBallImage src f₁ w)
    (hDS : D ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (havoid : ∀ s', s' ≠ s → Disjoint D (fbl s')) :
    ∃ O : Set M₂, IsOpen O ∧ D ⊆ O ∧ Disjoint O (⋃ s' ≠ s, fbl s') ∧
      Disjoint O (h '' simplexRim 𝒦 s.1) := by
  obtain ⟨-, hHU, -, -, -, -⟩ := id hctrl
  obtain ⟨-, -, -, -, -, -, -, -, hrim, -, hcr, -, -, hcar⟩ := hgraph
  have hDU : D ⊆ h '' U := fun x hx =>
    hHU (cr w) (hcr w) (hcar w (Or.inr (hDw hx)))
  obtain ⟨O, hO, hDO, hOavoid⟩ :=
    exists_isOpen_section34FaceBall_avoiding hinv hcut hctrl s hDU havoid
  have hRclosed : IsClosed (h '' simplexRim 𝒦 s.1) :=
    (isCompact_image_section34SimplexRim
      (continuousOn_iff_continuous_domRestrict.mpr hh.continuous) s).isClosed
  have hTY : section34FaceTorus (section34VertexBallImage src f₁) s ⊆
      ⋃ v, section34VertexBallImage src f₁ v := by
    rintro x hx
    obtain ⟨a, _, hxa⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨a.1.2, hxa⟩
  refine ⟨O \ h '' simplexRim 𝒦 s.1, hO.sdiff hRclosed, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hDO hx, fun hxR => (hDS hx).2 (interior_mono hTY (hrim s hxR))⟩
  · exact disjoint_left.mpr fun x hx hxf => disjoint_left.mp hOavoid hx.1 hxf
  · exact disjoint_left.mpr fun x hx hxR => hx.2 hxR

end DifferentialGeometry.Topology.PiecewiseLinear
