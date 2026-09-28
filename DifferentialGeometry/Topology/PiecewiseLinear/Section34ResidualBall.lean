/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraPocket

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

theorem Section34NormalPlus.exists_residualBall
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP) (t : Section34SimplexIndex 𝒦 4) :
    ∃ R : Set M₂, IsPLCellOn 3 R (frontier R) ∧
      (∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 → tgtD s ⊆ frontier R) ∧
      frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
          section34VertexBallImage src f₁ w) ∪
        ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s ∧
      Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
        (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w) ∧
      R ⊆ H t.1 ∧
      ∀ arc : Section34ArcIndex 𝒦 𝒦', Section34Incident arc.1.1.1 t.1 → ∀ y ∈ tgtA arc,
        (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
        ∀ W ∈ 𝓝 y,
          (∃ z ∈ W, z ∈ frontier (section34VertexBallImage src f₁ arc.1.2) ∧ z ∈ R ∧
            z ∉ tgtD arc.1.1) ∧
          ∃ z ∈ W, z ∈ frontier (section34VertexBallImage src f₁ arc.1.2) ∧ z ∉ R := by
  classical
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hmap := hcut.2.2.1
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, htabcd⟩ := Finset.card_eq_four.mp t.2.2
  have ht := t.2.1
  have ha : a ∈ t.1 := by rw [htabcd]; simp
  have hb : b ∈ t.1 := by rw [htabcd]; simp
  have hc : c ∈ t.1 := by rw [htabcd]; simp
  have hd : d ∈ t.1 := by rw [htabcd]; simp
  have hpK : ∀ {u v : Ea}, u ∈ t.1 → v ∈ t.1 → ({u, v} : Finset Ea) ∈ 𝒦.complex.faces :=
    fun hu hv =>
    𝒦.complex.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  have htri : ∀ {x y z : Ea}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → x ≠ y → x ≠ z → y ≠ z →
      ∃ s : Section34SimplexIndex 𝒦 3, s.1 = {x, y, z} := by
    intro x y z hx hy hz hxy hxz hyz
    refine ⟨⟨{x, y, z}, 𝒦.complex.down_closed ht ?_ (Finset.insert_nonempty _ _),
      Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩⟩, rfl⟩
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  obtain ⟨sacd, hsacd⟩ := htri ha hc hd hac had hcd
  obtain ⟨sabc, hsabc⟩ := htri ha hb hc hab hac hbc
  obtain ⟨sbcd, hsbcd⟩ := htri hb hc hd hbc hbd hcd
  obtain ⟨sabd, hsabd⟩ := htri ha hb hd hab had hbd
  obtain ⟨ea, hea₁, hea₂, hea⟩ := hcut.exists_edgeIndex_mem_subset_segment had (hpK ha hd)
  obtain ⟨eb, heb₁, heb₂, heb⟩ := hcut.exists_edgeIndex_mem_subset_segment hbc (hpK hb hc)
  obtain ⟨ec, hec₁, hec₂, hec⟩ := hcut.exists_edgeIndex_mem_subset_segment hac.symm (hpK hc ha)
  obtain ⟨ed, hed₁, hed₂, hed⟩ := hcut.exists_edgeIndex_mem_subset_segment hbd.symm (hpK hd hb)
  obtain ⟨chart, hchart, hHsrc, hVchart, hfchart⟩ := hdata.exists_chart_tetrahedron t
  obtain ⟨-, hcar, -, hext, -, -, -, -, -, -, -, -, hfbl, -⟩ := id hdata
  obtain ⟨hD1, hD2, -, -, -, -, hA7, -⟩ := id hdisk
  have hDfbl : ∀ s, tgtD s ⊆ fbl s := fun s => (hD2 s).trans (hfbl s).boundary_subset
  have hDchart : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ chart.source := fun s hs => (hDfbl s).trans (hfchart s hs)
  obtain ⟨R₀, A, Ω, hR₀, hRf, hAB₁, hΩB₂, ⟨qA, hqA, hqAb⟩, ⟨qΩ, hqΩ, hqΩb⟩,
      hΩB₁, hAB₂, hdisj⟩ :=
    hdata.exists_isPLBall_of_tetra_in_chart hdisk ht htabcd hab hac had hbc hbd hcd hea₁
      hea₂ hea heb₁ heb₂ heb hec₁ hec₂ hec hed₁ hed₂ hed hsacd hsabc hsbcd hsabd
      hchart hVchart hDchart
  set V := section34VertexBallImage src f₁
  set B₁ := section34ClawBall V a b c d
  set B₂ := section34ClawBall V d c a b
  let C₁ := chart '' B₁
  let C₂ := chart '' B₂
  let F : Fin 4 → Section34SimplexIndex 𝒦 3 := ![sacd, sabc, sbcd, sabd]
  let Vs := ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1), V w
  let Ds := ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s
  have hfaces : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      s = sacd ∨ s = sabc ∨ s = sbcd ∨ s = sabd := by
    intro s hs
    rcases section34SimplexIndex_eq_of_incident ht htabcd hab hac had hbc hbd hcd s hs with
      h | h | h | h
    · exact Or.inl (Subtype.ext (h.trans hsacd.symm))
    · exact Or.inr (Or.inl (Subtype.ext (h.trans hsabc.symm)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (h.trans hsbcd.symm))))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (h.trans hsabd.symm))))
  have hsegt : ∀ {u v : Ea}, u ∈ t.1 → v ∈ t.1 → segment ℝ u v ⊆ convexHull ℝ (t.1 : Set Ea) :=
    fun hu hv => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu)
      (subset_convexHull ℝ _ hv)
  have hFinc : ∀ {s : Section34SimplexIndex 𝒦 3} {x y z : Ea}, s.1 = {x, y, z} →
      x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → Section34Incident s.1 t.1 := by
    intro s x y z hs hx hy hz u hu
    rw [hs] at hu
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact subset_convexHull ℝ _ hx
    · exact subset_convexHull ℝ _ hy
    · exact subset_convexHull ℝ _ hz
  have hpinc : ∀ {w : Section34VertexIndex 𝒦 𝒦'} {p : Ea}, w.1 = {p} →
      p ∈ convexHull ℝ (t.1 : Set Ea) → Section34Incident w.1 t.1 := by
    intro w p hw hp z hz
    rw [hw, Finset.coe_singleton] at hz
    rw [mem_singleton_iff.mp hz]
    exact hp
  have hB₁inc : B₁ ⊆ ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
      V w := by
    intro z hz
    obtain ⟨w, ⟨p, hw, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨w, hpinc hw ?_, hzw⟩
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt ha hb h
    · exact hsegt ha hc h
    · exact hsegt hb hd h
  have hB₂inc : B₂ ⊆ ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
      V w := by
    intro z hz
    obtain ⟨w, ⟨p, hw, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨w, hpinc hw ?_, hzw⟩
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt hd hc h
    · exact hsegt hd ha h
    · exact hsegt hc hb h
  have hVsH : Vs ⊆ H t.1 := by
    intro z hzV
    obtain ⟨w, hw, hz⟩ := mem_iUnion₂.mp hzV
    exact interior_subset (hext.1 t (Or.inl
      (mem_iUnion₂.mpr ⟨⟨(t, w), hw⟩, rfl, hz⟩)))
  have hDsH : Ds ⊆ H t.1 := by
    intro z hzD
    obtain ⟨s, hs, hz⟩ := mem_iUnion₂.mp hzD
    exact interior_subset (hext.1 t (Or.inr (mem_iUnion₂.mpr ⟨s, hs, hDfbl s hz⟩)))
  have hVsSrc : Vs ⊆ chart.source := hVsH.trans hHsrc
  have hDsSrc : Ds ⊆ chart.source := hDsH.trans hHsrc
  have hB₁src : B₁ ⊆ chart.source := hB₁inc.trans hVsSrc
  have hB₂src : B₂ ⊆ chart.source := hB₂inc.trans hVsSrc
  have hB₁M := hcut.isPLCellOn_section34ClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc hcd
    hchart hVchart
  have hB₂M := hcut.isPLCellOn_section34ClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
    hbd.symm hac.symm hab hchart hVchart
  obtain ⟨hB₁, hfr₁⟩ := hB₁M.isPLBall_image_chart hchart hB₁src
  obtain ⟨hB₂, hfr₂⟩ := hB₂M.isPLBall_image_chart hchart hB₂src
  have hFt : ∀ k, Section34Incident (F k).1 t.1 := by
    intro k
    fin_cases k
    exacts [hFinc hsacd ha hc hd, hFinc hsabc ha hb hc, hFinc hsbcd hb hc hd,
      hFinc hsabd ha hb hd]
  have hDall : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      chart '' tgtD s ∩ C₁ ⊆ qA '' stdSimplexBoundary 2 ∧
        chart '' tgtD s ∩ C₂ ⊆ qΩ '' stdSimplexBoundary 2 := by
    intro s hs
    rcases hfaces s hs with rfl | rfl | rfl | rfl
    · exact ⟨hqAb 0, hqΩb 0⟩
    · exact ⟨hqAb 1, hqΩb 1⟩
    · exact ⟨hqAb 2, hqΩb 2⟩
    · exact ⟨hqAb 3, hqΩb 3⟩
  have hDfront : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      chart '' tgtD s ⊆ frontier R₀ := by
    intro s hs z hz
    rw [hRf]
    refine Or.inl (Or.inr ?_)
    rcases hfaces s hs with rfl | rfl | rfl | rfl
    · exact mem_iUnion.mpr ⟨0, hz⟩
    · exact mem_iUnion.mpr ⟨1, hz⟩
    · exact mem_iUnion.mpr ⟨2, hz⟩
    · exact mem_iUnion.mpr ⟨3, hz⟩
  have hfrontSupp : frontier R₀ ⊆ chart '' (Vs ∪ Ds) := by
    rw [hRf]
    rintro z ((hzA | hzD) | hzΩ)
    · exact image_mono (hB₁inc.trans subset_union_left)
        (hB₁.isPolyhedron.isClosed.frontier_subset (hAB₁ hzA))
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hzD
      exact image_mono (show tgtD (F k) ⊆ Vs ∪ Ds from fun z hz =>
        Or.inr (mem_iUnion₂.mpr ⟨F k, hFt k, hz⟩)) hk
    · exact image_mono (hB₂inc.trans subset_union_left)
        (hB₂.isPolyhedron.isClosed.frontier_subset (hΩB₂ hzΩ))
  have hHball := (hcar.2.2.2.2.1 t.1 t.2.1).isPLBall_image_chart hchart hHsrc
  have hR₀H : R₀ ⊆ chart '' H t.1 := hHball.1.subset_of_isCompact_frontier_subset
    hR₀.isPolyhedron.isCompact (hfrontSupp.trans (image_mono (union_subset hVsH hDsH)))
  have hR₀target : R₀ ⊆ chart.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hR₀H hz
    exact chart.map_source (hHsrc hx)
  let R := chart.symm '' R₀
  have hRpre := hR₀.isPLCellOn_frontier.image_chart_symm hchart hR₀target
  have hRF : chart.symm '' frontier R₀ = frontier R := hRpre.boundary_eq_frontier
  have hR : IsPLCellOn 3 R (frontier R) := by
    rw [← hRF]
    exact hRpre
  have hRimage : chart '' R = R₀ := chart.image_symm_image_of_subset_target hR₀target
  have hRH : R ⊆ H t.1 := by
    calc R ⊆ chart.symm '' (chart '' H t.1) := image_mono hR₀H
      _ = H t.1 := chart.symm_image_image_of_subset_source hHsrc
  have hRsrc : R ⊆ chart.source := hRH.trans hHsrc
  have hfront : frontier R ⊆ Vs ∪ Ds := by
    rw [← hRF]
    calc chart.symm '' frontier R₀ ⊆ chart.symm '' (chart '' (Vs ∪ Ds)) :=
          image_mono hfrontSupp
      _ = Vs ∪ Ds := chart.symm_image_image_of_subset_source (union_subset hVsSrc hDsSrc)
  have hRint : Disjoint (interior R) Vs := by
    refine Set.disjoint_left.mpr fun z hz hzV => ?_
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hzV
    have hzi : chart z ∈ interior R₀ := by
      have hi : chart '' interior R ⊆ interior (chart '' R) :=
        interior_maximal (image_mono interior_subset)
          (chart.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hRsrc))
      rw [hRimage] at hi
      exact hi (mem_image_of_mem chart hz)
    have hzB := section34VertexBallImage_subset_clawBall_union hmap ht htabcd hw hzw
    have hci : chart z ∈ C₁ ∪ C₂ := by
      rcases hzB with hzB | hzB
      · exact Or.inl (mem_image_of_mem chart hzB)
      · exact Or.inr (mem_image_of_mem chart hzB)
    exact Set.disjoint_left.mp hdisj hzi hci
  have hbd : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → q '' stdSimplexBoundary 2 ⊆ P :=
    fun hq => by
      rw [← hq.image_eq]
      exact image_mono fun x hx => hx.1
  have hAR : A ⊆ frontier R₀ := by rw [hRf]; exact subset_union_left.trans subset_union_left
  have hΩR : Ω ⊆ frontier R₀ := by rw [hRf]; exact subset_union_right
  have hRB₁ : frontier R₀ ∩ C₁ ⊆ A := by
    rw [hRf]
    rintro z ⟨(hzA | hzD) | hzΩ, hzB⟩
    · exact hzA
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hzD
      exact hbd hqA (hqAb k ⟨hk, hzB⟩)
    · exact hΩB₁ ⟨hzΩ, hzB⟩
  have hRB₂ : frontier R₀ ∩ C₂ ⊆ Ω := by
    rw [hRf]
    rintro z ⟨(hzA | hzD) | hzΩ, hzB⟩
    · exact hAB₂ ⟨hzA, hzB⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hzD
      exact hbd hqΩ (hqΩb k ⟨hk, hzB⟩)
    · exact hzΩ
  refine ⟨R, hR, ?_, hfront, hRint, hRH, ?_⟩
  · intro s hs z hz
    rw [← hRF]
    exact ⟨chart z, hDfront s hs (mem_image_of_mem chart hz), chart.left_inv (hDchart s hs hz)⟩
  · intro arc hs y hy hyE W hW
    have hws : Section34Incident arc.1.2.1 arc.1.1.1 := arc.2
    have hwt : Section34Incident arc.1.2.1 t.1 := fun z hz =>
      convexHull_min hs (convex_convexHull ℝ _) (hws hz)
    have hyDV : y ∈ tgtDBd arc.1.1 ∩ V arc.1.2 := by
      rw [hA7 arc]
      exact hy
    have hyD : y ∈ tgtD arc.1.1 := (hD1 arc.1.1).boundary_subset hyDV.1
    have hysrc : y ∈ chart.source := hVchart arc.1.2 hwt hyDV.2
    have hytarget : chart y ∈ chart.target := chart.map_source hysrc
    let C : Section34VertexIndex 𝒦 𝒦' → Set E3 := fun w => chart '' V w
    let O := (⋃ u ∈ {u : Section34VertexIndex 𝒦 𝒦' |
      Section34Incident u.1 t.1 ∧ u ≠ arc.1.2}, C u)ᶜ
    have hfin := finite_setOf_section34Incident_graphIndex hcut.2.1 (graphSkeletonSpace 𝒦)
      1 t.2.1
    have hfin' : {u : Section34VertexIndex 𝒦 𝒦' |
        Section34Incident u.1 t.1 ∧ u ≠ arc.1.2}.Finite := hfin.subset fun u hu => hu.1
    have hCclosed : ∀ u : Section34VertexIndex 𝒦 𝒦', Section34Incident u.1 t.1 →
        IsClosed (C u) := fun u hu =>
      ((hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.image_of_continuousOn
        (chart.continuousOn.mono (hVchart u hu))).isClosed
    have hO : IsOpen O :=
      (hfin'.isClosed_biUnion fun u hu => hCclosed u hu.1).isOpen_compl
    have hyO : chart y ∈ O := by
      intro hyu
      obtain ⟨u, ⟨hut, hu⟩, x, hx, hxy⟩ := mem_iUnion₂.mp hyu
      have hxy' : x = y := chart.injOn (hVchart u hut hx) hysrc hxy
      have hyu' : y ∈ V u := hxy' ▸ hx
      obtain ⟨e, he⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn
        (Ne.symm hu) hyDV.2 hyu'
      exact hyE e he
    let N := chart.symm ⁻¹' W ∩ chart.target
    have hsymm : ContinuousAt chart.symm (chart y) :=
      (chart.continuousOn_symm _ hytarget).continuousAt (chart.open_target.mem_nhds hytarget)
    have hW' : W ∈ 𝓝 (chart.symm (chart y)) := by rwa [chart.left_inv hysrc]
    have hN : N ∈ 𝓝 (chart y) :=
      Filter.inter_mem (hsymm.preimage_mem_nhds hW') (chart.open_target.mem_nhds hytarget)
    have hN' := Filter.inter_mem hN (hO.mem_nhds hyO)
    have hfrV : ∀ {B : Set E3} {z : E3}, IsClosed B →
        (∀ z ∈ B, ∃ u, Section34Incident u.1 t.1 ∧ z ∈ C u) →
        C arc.1.2 ⊆ B → z ∈ frontier B → z ∈ O → z ∈ frontier (C arc.1.2) := by
      intro B z hBc hcov hVB hzB hzO
      obtain ⟨u, hut, hzu⟩ := hcov z (hBc.frontier_subset hzB)
      by_cases huw : u = arc.1.2
      · rw [huw] at hzu
        exact ⟨subset_closure hzu, fun hzi => hzB.2 (interior_mono hVB hzi)⟩
      · exact absurd (mem_iUnion₂.mpr ⟨u, ⟨hut, huw⟩, hzu⟩) hzO
    have hcov₁ : ∀ z ∈ C₁, ∃ u, Section34Incident u.1 t.1 ∧ z ∈ C u := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hB₁inc hx)
      exact ⟨u, hu, mem_image_of_mem chart hxu⟩
    have hcov₂ : ∀ z ∈ C₂, ∃ u, Section34Incident u.1 t.1 ∧ z ∈ C u := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hB₂inc hx)
      exact ⟨u, hu, mem_image_of_mem chart hxu⟩
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp arc.1.2.2.2.1
    have hpw : p ∈ (arc.1.2.1 : Set Ea) := by
      rw [hp]
      exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
    have hpg : 𝒦.map p ∈ graphSkeletonSpace 𝒦 := by
      rw [← hmap]
      exact arc.1.2.2.2.2 ⟨p, subset_convexHull ℝ _ hpw, rfl⟩
    obtain ⟨x, hx, y', hy', hpxy⟩ :=
      exists_mem_segment_of_mem_convexHull_of_map_mem_graphSkeleton ht (hwt hpw) hpg
    have hcoord :
        (∃ z ∈ N, z ∈ frontier (C arc.1.2) ∧ z ∈ R₀ ∧ z ∉ chart '' tgtD arc.1.1) ∧
        ∃ z ∈ N, z ∈ frontier (C arc.1.2) ∧ z ∉ R₀ := by
      rcases SimplicialComplex.mem_claw_or_mem_claw_of_mem_segment htabcd hx hy' hpxy with
        hcl | hcl
      · have hVBM : V arc.1.2 ⊆ B₁ := fun z hz =>
          mem_iUnion₂.mpr ⟨arc.1.2, ⟨p, hp, hcl⟩, hz⟩
        have hVB : C arc.1.2 ⊆ C₁ := image_mono hVBM
        have hyq : chart y ∈ qA '' stdSimplexBoundary 2 := (hDall arc.1.1 hs).1
          ⟨mem_image_of_mem chart hyD, mem_image_of_mem chart (hVBM hyDV.2)⟩
        obtain ⟨⟨z, hzN, hzB, hzR, hzq⟩, ⟨z', hz'N, hz'B, hz'R⟩⟩ :=
          exists_mem_frontier_of_mem_boundary_disk hB₁ hR₀.isPolyhedron.isClosed hqA hAB₁
            hAR hRB₁ (hdisj.mono_right subset_union_left) hyq hN'
        refine ⟨⟨z, hzN.1, hfrV hB₁.isPolyhedron.isClosed hcov₁ hVB hzB hzN.2, hzR,
          fun hzD => hzq ?_⟩,
          ⟨z', hz'N.1, hfrV hB₁.isPolyhedron.isClosed hcov₁ hVB hz'B hz'N.2, hz'R⟩⟩
        exact (hDall arc.1.1 hs).1 ⟨hzD, hB₁.isPolyhedron.isClosed.frontier_subset hzB⟩
      · have hVBM : V arc.1.2 ⊆ B₂ := fun z hz =>
          mem_iUnion₂.mpr ⟨arc.1.2, ⟨p, hp, hcl⟩, hz⟩
        have hVB : C arc.1.2 ⊆ C₂ := image_mono hVBM
        have hyq : chart y ∈ qΩ '' stdSimplexBoundary 2 := (hDall arc.1.1 hs).2
          ⟨mem_image_of_mem chart hyD, mem_image_of_mem chart (hVBM hyDV.2)⟩
        obtain ⟨⟨z, hzN, hzB, hzR, hzq⟩, ⟨z', hz'N, hz'B, hz'R⟩⟩ :=
          exists_mem_frontier_of_mem_boundary_disk hB₂ hR₀.isPolyhedron.isClosed hqΩ hΩB₂
            hΩR hRB₂ (hdisj.mono_right subset_union_right) hyq hN'
        refine ⟨⟨z, hzN.1, hfrV hB₂.isPolyhedron.isClosed hcov₂ hVB hzB hzN.2, hzR,
          fun hzD => hzq ?_⟩,
          ⟨z', hz'N.1, hfrV hB₂.isPolyhedron.isClosed hcov₂ hVB hz'B hz'N.2, hz'R⟩⟩
        exact (hDall arc.1.1 hs).2 ⟨hzD, hB₂.isPolyhedron.isClosed.frontier_subset hzB⟩
    have hVcell := hcut.isPLCellOn_vertexBallImage hf₁ arc.1.2
    have hVfr : chart '' frontier (V arc.1.2) = frontier (C arc.1.2) := by
      have h := (hVcell.isPLBall_image_chart hchart (hVchart arc.1.2 hwt)).2
      rwa [hVcell.boundary_eq_frontier] at h
    have hpull : ∀ z ∈ frontier (C arc.1.2), chart.symm z ∈ frontier (V arc.1.2) := by
      intro z hz
      rw [← hVfr] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [chart.left_inv (hVchart arc.1.2 hwt (hVcell.isCompact.isClosed.frontier_subset hx))]
      exact hx
    obtain ⟨⟨z, hzN, hzV, hzR, hzD⟩, ⟨z', hz'N, hz'V, hz'R⟩⟩ := hcoord
    refine ⟨⟨chart.symm z, hzN.1, hpull z hzV, ⟨z, hzR, rfl⟩, fun hz => hzD ?_⟩,
      ⟨chart.symm z', hz'N.1, hpull z' hz'V, fun hz => hz'R ?_⟩⟩
    · exact ⟨chart.symm z, hz, chart.right_inv hzN.2⟩
    · have hm := mem_image_of_mem chart hz
      rw [hRimage, chart.right_inv hz'N.2] at hm
      exact hm

end DifferentialGeometry.Topology.PiecewiseLinear
