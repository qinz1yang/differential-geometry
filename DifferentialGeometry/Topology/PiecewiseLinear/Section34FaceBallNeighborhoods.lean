/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSeparatingNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Control
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

open Classical in
theorem exists_section34FaceBallNeighborhoods (hU : IsOpen U)
    (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    (Bad : Section34SimplexIndex 𝒦 3 → Set M₂) (hBadc : ∀ s, IsClosed (Bad s))
    (hBad : ∀ s, Disjoint (h '' simplexBody 𝒦 s.1) (Bad s)) :
    ∃ (Wn : Section34SimplexIndex 𝒦 3 → Set M₂)
      (c : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))),
      (∀ s, c s ∈ (plGroupoid 3).maximalAtlas M₂) ∧ (∀ s, IsOpen (Wn s)) ∧
      (∀ s, Wn s ⊆ (c s).source) ∧ (∀ s, h '' simplexBody 𝒦 s.1 ⊆ Wn s) ∧
      (∀ (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4),
        Section34Incident s.1 t.1 → Wn s ⊆ interior (H t.1)) ∧
      (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
        ¬ Section34Incident w.1 s.1 → Wn s ∩ section34VertexBallImage src f₁ w = ∅) ∧
      (∀ s s', s ≠ s' → Wn s ∩ Wn s' ⊆ interior (⋃ w, section34VertexBallImage src f₁ w)) ∧
      (∀ s : Section34SimplexIndex 𝒦 3,
        Wn s ⊆ h '' (𝒦.map '' ⋃ v ∈ s.1, openStar 𝒦.complex v)) ∧
      (∀ s, Disjoint (Wn s) (Bad s)) ∧
      ∀ s, ∃ C B : Set M₂, IsPLCellOn 3 C B ∧ h '' simplexBody 𝒦 s.1 ⊆ interior C ∧
        C ⊆ Wn s := by
  obtain ⟨hK, -, -, hcell, -⟩ := id hcut
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ := id hcut
  obtain ⟨hcarrier, hHU, hHlf, -, hHcell, hchart⟩ := id hctrl
  obtain ⟨-, -, hf₁, hN, -, -, -, hvb, -, -, hcr, -, hcrfin, hsub⟩ := id hgraph
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhinj : InjOn h U := fun a ha b hb hab =>
    congrArg Subtype.val (@hh.injective ⟨a, ha⟩ ⟨b, hb⟩ hab)
  have hXo : IsOpen (h '' U) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hU hhU hhinj
  have hΦcont : ContinuousOn (fun z => h (𝒦.map z)) 𝒦.complex.space :=
    hhU.comp 𝒦.continuousOn fun z hz => 𝒦.bijOn.mapsTo hz
  have hΦinj : InjOn (fun z => h (𝒦.map z)) 𝒦.complex.space := fun z hz z' hz' hzz =>
    𝒦.bijOn.injOn hz hz' (hhinj (𝒦.bijOn.mapsTo hz) (𝒦.bijOn.mapsTo hz') hzz)
  let E' : 𝒦.complex.space → h '' U := fun z =>
    ⟨h (𝒦.map z), 𝒦.map z, 𝒦.bijOn.mapsTo z.2, rfl⟩
  have hE' : IsEmbedding E' := by
    let k : 𝒦.complex.space → U := fun z => ⟨𝒦.map z, 𝒦.bijOn.mapsTo z.2⟩
    have hk : IsEmbedding k := 𝒦.isEmbedding.codRestrict U fun z => 𝒦.bijOn.mapsTo z.2
    exact (IsEmbedding.subtypeVal.of_comp_iff (f := E')).mp (hh.comp hk)
  have hE'surj : Function.Surjective E' := by
    rintro ⟨_, u, hu, rfl⟩
    obtain ⟨z, hz, rfl⟩ := 𝒦.bijOn.surjOn hu
    exact ⟨⟨z, hz⟩, rfl⟩
  have himgOpen : ∀ S : Set 𝒦.complex.space, IsOpen S → IsOpen (E' '' S) := by
    intro S hS
    obtain ⟨O, hO, rfl⟩ := hE'.isInducing.isOpen_iff.mp hS
    rw [hE'surj.image_preimage]
    exact hO
  have hstarOpen : ∀ v, IsOpen ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹'
      openStar 𝒦.complex v) := by
    intro v
    have heq : (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' openStar 𝒦.complex v =
        (Subtype.val ⁻¹' avoidingUnion 𝒦.complex v)ᶜ := by
      ext z
      exact ⟨fun hz => hz.2, fun hz => ⟨z.2, hz⟩⟩
    rw [heq]
    exact (𝒦.isClosed_preimage_avoidingUnion v).isOpen_compl
  choose ts hts using hcof
  choose c hc hcsrc using fun s : Section34SimplexIndex 𝒦 3 => hchart (ts s).1 (ts s).2.1
  have hbodyCS : ∀ s t : Finset Ea, (∃ v ∈ s, v ∈ t) → s ∈ 𝒦.complex.faces →
      simplexBody 𝒦 s ⊆ Section34CarrierSupport 𝒦 t := by
    rintro s t ⟨v, hvs, hvt⟩ hs _ ⟨z, hz, rfl⟩
    simp only [Section34CarrierSupport, mem_iUnion₂]
    exact ⟨v, hvt, s, ⟨hs, hvs⟩, z, hz, rfl⟩
  have hbodyH : ∀ (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4),
      Section34Incident s.1 t.1 → h '' simplexBody 𝒦 s.1 ⊆ interior (H t.1) := by
    intro s t hst
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
    have hvt : v ∈ t.1 := mem_of_mem_convexHull_of_singleton_mem _
      (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)) t.2.1 (hst (Finset.mem_coe.mpr hv))
    exact (image_mono (hbodyCS s.1 t.1 ⟨v, hv, hvt⟩ s.2.1)).trans (hcarrier t.1 t.2.1)
  have hbodyHs : ∀ s : Section34SimplexIndex 𝒦 3, h '' simplexBody 𝒦 s.1 ⊆ H s.1 := by
    intro s
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
    exact ((image_mono (hbodyCS s.1 s.1 ⟨v, hv, hv⟩ s.2.1)).trans
      (hcarrier s.1 s.2.1)).trans interior_subset
  have hbodyC : ∀ s : Section34SimplexIndex 𝒦 3, IsCompact (h '' simplexBody 𝒦 s.1) := by
    intro s
    have heq : h '' simplexBody 𝒦 s.1 =
        (fun z => h (𝒦.map z)) '' convexHull ℝ (s.1 : Set Ea) := by
      rw [simplexBody, image_image]
    rw [heq]
    exact (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (hΦcont.mono (𝒦.complex.convexHull_subset_space s.2.1))
  have hAc : ∀ s : Section34SimplexIndex 𝒦 3,
      IsClosed ((Subtype.val : h '' U → M₂) ⁻¹' (h '' simplexBody 𝒦 s.1)) :=
    fun s => (hbodyC s).isClosed.preimage continuous_subtype_val
  have hAlf : LocallyFinite fun s : Section34SimplexIndex 𝒦 3 =>
      (Subtype.val : h '' U → M₂) ⁻¹' (h '' simplexBody 𝒦 s.1) := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hHlf x.1 x.2
    refine ⟨Subtype.val ⁻¹' V, ?_, ?_⟩
    · rw [mem_nhds_subtype_iff_nhdsWithin, Subtype.image_preimage_coe]
      exact Filter.inter_mem self_mem_nhdsWithin hV
    · refine (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset ?_
      rintro s ⟨y, hyA, hyV⟩
      exact ⟨s.2.1, y.1, hbodyHs s hyA, hyV⟩
  have hZo : IsOpen ((Subtype.val : h '' U → M₂) ⁻¹'
      interior (⋃ w, section34VertexBallImage src f₁ w)) :=
    isOpen_interior.preimage continuous_subtype_val
  have hNeq : f₁ '' section34CutNeighborhood src = ⋃ w, section34VertexBallImage src f₁ w := by
    rw [section34CutNeighborhood, image_iUnion]
    rfl
  have hΓint : h '' graphSkeletonSpace 𝒦 ⊆ interior (⋃ w, section34VertexBallImage src f₁ w) := by
    rw [← hNeq]
    exact subset_interior_iff_mem_nhdsSet.mpr hN
  have hAZ : ∀ s s' : Section34SimplexIndex 𝒦 3, s ≠ s' →
      (Subtype.val : h '' U → M₂) ⁻¹' (h '' simplexBody 𝒦 s.1) ∩
        (Subtype.val : h '' U → M₂) ⁻¹' (h '' simplexBody 𝒦 s'.1) ⊆
      interior ((Subtype.val : h '' U → M₂) ⁻¹'
        interior (⋃ w, section34VertexBallImage src f₁ w)) := by
    intro s s' hss' x ⟨hx, hx'⟩
    rw [hZo.interior_eq]
    obtain ⟨_, ⟨z, hz, rfl⟩, hmz⟩ := hx
    obtain ⟨_, ⟨z', hz', rfl⟩, hmz'⟩ := hx'
    have hzK := 𝒦.complex.convexHull_subset_space s.2.1 hz
    have hz'K := 𝒦.complex.convexHull_subset_space s'.2.1 hz'
    have hzz : z = z' := hΦinj hzK hz'K (hmz.trans hmz'.symm)
    subst hzz
    have hint := 𝒦.complex.inter_subset_convexHull s.2.1 s'.2.1 ⟨hz, hz'⟩
    rw [← Finset.coe_inter] at hint
    have hne : (s.1 ∩ s'.1).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.coe_empty, convexHull_empty] at hint
      exact hint
    have hface : s.1 ∩ s'.1 ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed s.2.1 Finset.inter_subset_left hne
    have hcard : (s.1 ∩ s'.1).card ≤ 2 := by
      have hlt : s.1 ∩ s'.1 ⊂ s.1 := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, fun heq => hss' ?_⟩
        have hsub' : s.1 ⊆ s'.1 := heq ▸ Finset.inter_subset_right
        exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub' (by rw [s.2.2, s'.2.2]))
      have := Finset.card_lt_card hlt
      rw [s.2.2] at this
      omega
    change x.1 ∈ interior _
    rw [← hmz]
    apply hΓint
    exact ⟨𝒦.map z, mem_iUnion₂.mpr ⟨s.1 ∩ s'.1, ⟨hface, hcard⟩, z, hint, rfl⟩, rfl⟩
  have hincfin : ∀ s : Section34SimplexIndex 𝒦 3,
      {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1}.Finite := by
    intro s
    refine Set.Finite.of_finite_image (f := fun t : Section34SimplexIndex 𝒦 4 =>
      (⟨t.1, t.2.1⟩ : 𝒦.complex.faces)) ((𝒦.cofaces_finite s.2.1).subset ?_) ?_
    · rintro _ ⟨t, hst, rfl⟩
      change s.1 ⊆ t.1
      intro v hv
      exact mem_of_mem_convexHull_of_singleton_mem _
        (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)) t.2.1 (hst (Finset.mem_coe.mpr hv))
    · intro t _ t' _ htt
      have htt' : (⟨t.1, t.2.1⟩ : 𝒦.complex.faces) = ⟨t'.1, t'.2.1⟩ := htt
      exact Subtype.ext (Subtype.mk.inj htt')
  have hVnear : ∀ s : Section34SimplexIndex 𝒦 3, {w : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w ∩ H (ts s).1).Nonempty}.Finite := by
    intro s
    have hLF : ∀ x ∈ h '' U, ∃ V ∈ 𝓝 x,
        {l : 𝒦.complex.faces | (H l.1 ∩ V).Nonempty}.Finite := by
      intro x hx
      obtain ⟨V, hV, hfin⟩ := hHlf x hx
      refine ⟨V, (hXo.nhdsWithin_eq hx) ▸ hV, ?_⟩
      refine (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset ?_
      intro l hl
      exact ⟨l.2, hl⟩
    have hSig := finite_inter_nonempty_of_isCompact_of_locallyFinite
      (fun l : 𝒦.complex.faces => H l.1) (h '' U) (H (ts s).1)
      (hHcell (ts s).1 (ts s).2.1).isCompact (hHU (ts s).1 (ts s).2.1) hLF
    refine ((hSig.biUnion fun l _ => hcrfin l.1)).subset ?_
    intro w hw
    obtain ⟨y, hyw, hyH⟩ := hw
    refine mem_iUnion₂.mpr ⟨⟨cr w, hcr w⟩, ⟨y, hsub w (Or.inr hyw), hyH⟩, rfl⟩
  have hObc : ∀ s : Section34SimplexIndex 𝒦 3, IsClosed (⋃ w ∈ {w : Section34VertexIndex 𝒦 𝒦' |
      ¬ Section34Incident w.1 s.1 ∧ (section34VertexBallImage src f₁ w ∩ H (ts s).1).Nonempty},
      section34VertexBallImage src f₁ w) :=
    fun s => ((hVnear s).subset fun w hw => hw.2).isClosed_biUnion fun w _ =>
      ((hcell (.vertexBall w)).isCompact.image_of_continuousOn
        (hf₁.continuousOn.mono (hNV w))).isClosed
  have hOopen : ∀ s : Section34SimplexIndex 𝒦 3,
      IsOpen (E' '' ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹'
        ⋃ v ∈ s.1, openStar 𝒦.complex v)) := by
    intro s
    apply himgOpen
    rw [preimage_iUnion₂]
    exact isOpen_biUnion fun v _ => hstarOpen v
  have hGo : ∀ s : Section34SimplexIndex 𝒦 3, IsOpen ((Subtype.val : h '' U → M₂) ⁻¹'
      ((c s).source ∩ (⋂ t ∈ {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1},
        interior (H t.1)) ∩ (⋃ w ∈ {w : Section34VertexIndex 𝒦 𝒦' |
          ¬ Section34Incident w.1 s.1 ∧
            (section34VertexBallImage src f₁ w ∩ H (ts s).1).Nonempty},
          section34VertexBallImage src f₁ w)ᶜ ∩ (Bad s)ᶜ) ∩
      E' '' ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹' ⋃ v ∈ s.1, openStar 𝒦.complex v)) :=
    fun s => ((((c s).open_source.inter ((hincfin s).isOpen_biInter fun t _ =>
      isOpen_interior)).inter (hObc s).isOpen_compl).inter
        (hBadc s).isOpen_compl).preimage continuous_subtype_val |>.inter (hOopen s)
  have hAG : ∀ s : Section34SimplexIndex 𝒦 3,
      (Subtype.val : h '' U → M₂) ⁻¹' (h '' simplexBody 𝒦 s.1) ⊆
      (Subtype.val : h '' U → M₂) ⁻¹'
        ((c s).source ∩ (⋂ t ∈ {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1},
          interior (H t.1)) ∩ (⋃ w ∈ {w : Section34VertexIndex 𝒦 𝒦' |
            ¬ Section34Incident w.1 s.1 ∧
              (section34VertexBallImage src f₁ w ∩ H (ts s).1).Nonempty},
            section34VertexBallImage src f₁ w)ᶜ ∩ (Bad s)ᶜ) ∩
      E' '' ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹' ⋃ v ∈ s.1, openStar 𝒦.complex v) := by
    intro s x hx
    have hxH : x.1 ∈ interior (H (ts s).1) := hbodyH s (ts s) (hts s) hx
    refine ⟨⟨⟨⟨hcsrc s (interior_subset hxH), mem_iInter₂.mpr fun t hst => hbodyH s t hst hx⟩,
      ?_⟩, fun hxB => disjoint_left.mp (hBad s) hx hxB⟩, ?_⟩
    · intro hxOb
      obtain ⟨w, ⟨hw, -⟩, hxw⟩ := mem_iUnion₂.mp hxOb
      exact hw (hvb w s ⟨x.1, hxw, hx⟩)
    · obtain ⟨_, ⟨z, hz, rfl⟩, hmz⟩ := hx
      have hzK := 𝒦.complex.convexHull_subset_space s.2.1 hz
      obtain ⟨ρ, hρ, hzρ⟩ := exists_face_mem_openSimplex 𝒦.complex hzK
      have hρs := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ s.2.1 hzρ hz
      obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces hρ
      refine ⟨⟨z, hzK⟩, mem_iUnion₂.mpr ⟨v, hρs hv, hzK,
        notMem_avoidingUnion_of_mem_openSimplex _ hρ hzρ hv⟩, Subtype.ext hmz⟩
  obtain ⟨W', hW'o, hAW', hW'G, hW'Z⟩ :=
    exists_isOpen_inter_subset_interior_of_locallyFinite hAc hAlf hAZ hGo hAG
  have hWo : ∀ s, IsOpen (Subtype.val '' W' s) := fun s => hXo.isOpenMap_subtype_val _ (hW'o s)
  have hWsrc : ∀ s, Subtype.val '' W' s ⊆ (c s).source := by
    rintro s _ ⟨x, hx, rfl⟩
    exact (hW'G s hx).1.1.1.1
  have hbodyW : ∀ s, h '' simplexBody 𝒦 s.1 ⊆ Subtype.val '' W' s := by
    intro s y hy
    have hyX : y ∈ h '' U := hHU s.1 s.2.1 (hbodyHs s hy)
    exact ⟨⟨y, hyX⟩, hAW' s hy, rfl⟩
  refine ⟨fun s => Subtype.val '' W' s, c, hc, hWo, hWsrc, hbodyW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s t hst _ ⟨x, hx, rfl⟩
    exact mem_iInter₂.mp (hW'G s hx).1.1.1.2 t hst
  · intro s w hw
    apply eq_empty_of_forall_notMem
    rintro _ ⟨⟨x, hx, rfl⟩, hxw⟩
    have hG := hW'G s hx
    have hxH : x.1 ∈ H (ts s).1 := interior_subset (mem_iInter₂.mp hG.1.1.1.2 (ts s) (hts s))
    exact hG.1.1.2 (mem_iUnion₂.mpr ⟨w, ⟨hw, x.1, hxw, hxH⟩, hxw⟩)
  · rintro s s' hss' _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
    have hxeq : x' = x := Subtype.ext hxx'
    subst hxeq
    have hZ := hW'Z s s' hss' ⟨hx, hx'⟩
    rw [hZo.interior_eq] at hZ
    exact hZ
  · rintro s _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := (hW'G s hx).2
    rw [← hzx]
    exact ⟨𝒦.map z, ⟨z, hz, rfl⟩, rfl⟩
  · intro s
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxB
    exact (hW'G s hx).1.2 hxB
  · intro s
    exact Moise305Tame.exists_isPLCellOn_superset_image_of_isPLBall_two hU 𝒦 hK hhU hhinj
      (isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) (by rw [s.2.2]))
      (𝒦.complex.convexHull_subset_space s.2.1) (hc s) (hWo s) (hWsrc s) (hbodyW s)

end DifferentialGeometry.Topology.PiecewiseLinear
