/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem Section34CutFrame.splitDiskImage_sdiff_subset_interior_iUnion
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hh : IsEmbedding (U.domRestrict h))
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    section34SplitDiskImage src f₁ e \ section34SplitDiskImage srcBd f₁ e ⊆
      interior (⋃ w, section34VertexBallImage src f₁ w) := by
  obtain ⟨-, hsub, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨t, ht, het⟩ := hsub.exists_face_subset e.2.1
  obtain ⟨-, -, -, -, -, hcharts⟩ := id hctrl
  obtain ⟨c, hc, hHc⟩ := hcharts t ht
  have hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34VertexBallImage src f₁ w ⊆ c.source := by
    intro w hwe
    have hwt : Section34Incident w.1 t :=
      ((Finset.coe_subset.mpr hwe).trans (subset_convexHull ℝ _)).trans het
    exact (image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w ht hwt).trans
      (interior_subset.trans hHc)
  exact (hcut.splitDiskImage_sdiff_subset_interior hf₁ e hc hVc).trans
    (interior_mono (iUnion₂_subset fun w _ => subset_iUnion _ w))

theorem exists_section34BigonCarrier (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {s : Section34SimplexIndex 𝒦 3} {w v : Section34VertexIndex 𝒦 𝒦'}
    {e : Section34EdgeIndex 𝒦 𝒦'} {B B' Bb Dj Jd : Set M₂}
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hwv : w ≠ v) (hwi : Section34Incident w.1 s.1) (hvi : Section34Incident v.1 s.1)
    (hinter : section34SplitDiskImage src f₁ e =
      section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ v)
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hwc : section34VertexBallImage src f₁ w ⊆ c.source)
    (hD : IsPLCellOn 2 Dj Jd)
    (hDS : Dj ⊆ section34VertexBallImage srcBd f₁ w ∩
      frontier (⋃ w', section34VertexBallImage src f₁ w'))
    (hJ : Jd = B ∪ B') (hBbe : Bb ⊆ section34SplitDiskImage srcBd f₁ e)
    (hBsplit : B ∩ (⋃ e', section34SplitDiskImage src f₁ e') = Bb)
    (hB'e : B' ⊆ section34SplitDiskImage srcBd f₁ e) :
    ∃ O : Set M₂, IsOpen O ∧ Dj ⊆ O ∧ O ⊆ c.source ∧
      O ∩ (⋃ w', section34VertexBallImage src f₁ w') =
        O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) ∧
      O ∩ section34FaceTorus (section34VertexBallImage src f₁) s =
        O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) ∧
      (∀ e', e' ≠ e → Disjoint O (section34SplitDiskImage src f₁ e')) := by
  classical
  obtain ⟨-, hsub, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends,
    -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  have hDw : Dj ⊆ section34VertexBallImage src f₁ w :=
    fun x hx => (hVcell w).boundary_subset (hDS hx).1
  have hDc : Dj ⊆ c.source := hDw.trans hwc
  obtain ⟨hW, hWbd⟩ := (hVcell w).isPLBall_image_chart hc hwc
  obtain ⟨p, hp, hpb⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hDsurface : c '' Dj ⊆ frontier (c '' section34VertexBallImage src f₁ w) := by
    rw [← hWbd]
    exact image_mono fun x hx => (hDS hx).1
  have hDinter : ∀ e', Dj ∩ section34SplitDiskImage src f₁ e' ⊆ Jd := by
    intro e' x hx
    have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hx.2 (hDw hx.1)
    obtain ⟨a, b, -, heab, hEab⟩ := hends e'
    have hEwsrc : src (.splitDisk e') ⊆ src (.vertexBall w) := by
      rcases eq_or_eq_of_section34VertexIndex_subset e' heab hwe with rfl | rfl
      · rw [hEab]
        exact inter_subset_left
      · rw [hEab]
        exact inter_subset_right
    have hEw : section34SplitDiskImage src f₁ e' ⊆
        section34VertexBallImage srcBd f₁ w := by
      refine image_mono fun y hy => ?_
      rw [hbd (.vertexBall w)]
      exact mem_iUnion₂.mpr ⟨.splitDisk e', ⟨hEwsrc, by simp⟩, hy⟩
    have hEc : section34SplitDiskImage src f₁ e' ⊆ c.source :=
      (hEw.trans (hVcell w).boundary_subset).trans hwc
    obtain ⟨q, hq, hqb⟩ := (hEcell e').exists_isPLHomeomorphOn_image_chart hc hEc
    have hcore : c '' section34SplitDiskImage src f₁ e' \ q '' stdSimplexBoundary 2 ⊆
        frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj := by
      rintro _ ⟨⟨y, hy, rfl⟩, hyb⟩
      refine ⟨?_, ?_⟩
      · rw [← hWbd]
        exact mem_image_of_mem c (hEw hy)
      · rintro ⟨z, hz, hzy⟩
        have hzy' : z = y := c.injOn (hDc hz) (hEc hy) hzy
        have hyD : y ∈ Dj := hzy' ▸ hz
        have hynb : y ∉ section34SplitDiskImage srcBd f₁ e' := by
          intro hyb'
          exact hyb (hqb ▸ mem_image_of_mem c hyb')
        exact (hDS hyD).2.2
          (hcut.splitDiskImage_sdiff_subset_interior_iUnion hh hctrl hgraph e' ⟨hy, hynb⟩)
    have hEcl : c '' section34SplitDiskImage src f₁ e' ⊆
        closure (frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj) := by
      rw [← hq.closure_sdiff_image_stdSimplexBoundary]
      exact closure_mono hcore
    have hcJ : c x ∈ c '' Jd := by
      rw [hpb, ← hW.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
        hp hDsurface]
      exact ⟨mem_image_of_mem c hx.1, hEcl (mem_image_of_mem c hx.2)⟩
    obtain ⟨y, hy, hyx⟩ := hcJ
    exact c.injOn (hDc (hD.boundary_subset hy)) (hDc hx.1) hyx ▸ hy
  have hDavoid : ∀ e', e' ≠ e → Disjoint Dj (section34SplitDiskImage src f₁ e') := by
    intro e' he
    refine Set.disjoint_left.mpr fun x hxD hxe' => ?_
    have hxJ := hDinter e' ⟨hxD, hxe'⟩
    have hxe : x ∈ section34SplitDiskImage src f₁ e := by
      apply (hEcell e).boundary_subset
      rw [hJ] at hxJ
      rcases hxJ with hxB | hxB'
      · exact hBbe (hBsplit ▸ ⟨hxB, mem_iUnion.mpr ⟨e', hxe'⟩⟩)
      · exact hB'e hxB'
    exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁.injOn he) hxe' hxe
  have hDvertices : ∀ z, (Dj ∩ section34VertexBallImage src f₁ z).Nonempty →
      z = w ∨ z = v := by
    rintro z ⟨x, hxD, hxz⟩
    by_cases hzw : z = w
    · exact Or.inl hzw
    obtain ⟨e', hxe'⟩ :=
      hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn (Ne.symm hzw) (hDw hxD) hxz
    have he : e' = e := by
      by_contra he
      exact Set.disjoint_left.mp (hDavoid e' he) hxD hxe'
    have hxe : x ∈ section34SplitDiskImage src f₁ e := he ▸ hxe'
    have hxwv := hinter ▸ hxe
    obtain ⟨a, b, -, heab, -⟩ := hends e
    have hwa := eq_or_eq_of_section34VertexIndex_subset e heab
      (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hxwv.1)
    have hva := eq_or_eq_of_section34VertexIndex_subset e heab
      (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hxwv.2)
    have hza := eq_or_eq_of_section34VertexIndex_subset e heab
      (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hxz)
    rcases hwa with hwa | hwb
    · have hvb : v = b := hva.resolve_left fun hva => hwv (hwa.trans hva.symm)
      exact hza.imp (fun hza => hza.trans hwa.symm) (fun hzb => hzb.trans hvb.symm)
    · have hva : v = a := hva.resolve_right fun hvb => hwv (hwb.trans hvb.symm)
      exact hza.elim (fun hza => Or.inr (hza.trans hva.symm))
        (fun hzb => Or.inl (hzb.trans hwb.symm))
  obtain ⟨t, ht, hwt⟩ := hsub.exists_face_subset w.2.1
  have hwt' : Section34Incident w.1 t := (subset_convexHull ℝ _).trans hwt
  have hVH := image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w ht hwt'
  let I : Set (Section34VertexIndex 𝒦 𝒦') :=
    {z | (section34VertexBallImage src f₁ z ∩ H t).Nonempty ∧ z ≠ w ∧ z ≠ v}
  let Q : Set M₂ := ⋃ z ∈ I, section34VertexBallImage src f₁ z
  have hQc : IsClosed Q :=
    ((finite_setOf_vertexBallImage_inter_nonempty hctrl hgraph ht).subset
      fun z hz => hz.1).isClosed_biUnion fun z _ => (hVcell z).isCompact.isClosed
  let O : Set M₂ := c.source ∩ (interior (H t) \ Q)
  have hO : IsOpen O := c.open_source.inter (isOpen_interior.sdiff hQc)
  have hDO : Dj ⊆ O := by
    intro x hx
    refine ⟨hDc hx, hVH (hDw hx), ?_⟩
    intro hxQ
    obtain ⟨z, hzI, hxz⟩ := mem_iUnion₂.mp hxQ
    rcases hDvertices z ⟨x, hx, hxz⟩ with hzw | hzv
    · exact hzI.2.1 hzw
    · exact hzI.2.2 hzv
  have hOvertices : ∀ x ∈ O, ∀ z, x ∈ section34VertexBallImage src f₁ z →
      z = w ∨ z = v := by
    intro x hx z hxz
    by_cases hzw : z = w
    · exact Or.inl hzw
    by_cases hzv : z = v
    · exact Or.inr hzv
    exact False.elim (hx.2.2 (mem_iUnion₂.mpr
      ⟨z, ⟨⟨x, hxz, interior_subset hx.2.1⟩, hzw, hzv⟩, hxz⟩))
  have hOeq : O ∩ (⋃ z, section34VertexBallImage src f₁ z) =
      O ∩ (section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v) := by
    apply Subset.antisymm
    · rintro x ⟨hxO, hx⟩
      obtain ⟨z, hxz⟩ := mem_iUnion.mp hx
      refine ⟨hxO, ?_⟩
      rcases hOvertices x hxO z hxz with rfl | rfl
      · exact Or.inl hxz
      · exact Or.inr hxz
    · exact inter_subset_inter_right O
        (union_subset (subset_iUnion _ w) (subset_iUnion _ v))
  refine ⟨O, hO, hDO, inter_subset_left, hOeq, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hxO, hxT⟩
      obtain ⟨z, -, hxz⟩ := mem_section34FaceTorus_iff.mp hxT
      exact hOeq ▸ ⟨hxO, mem_iUnion.mpr ⟨z, hxz⟩⟩
    · rintro x ⟨hxO, hxw | hxv⟩
      · exact ⟨hxO, mem_section34FaceTorus_iff.mpr ⟨w, hwi, hxw⟩⟩
      · exact ⟨hxO, mem_section34FaceTorus_iff.mpr ⟨v, hvi, hxv⟩⟩
  · intro e' he
    refine Set.disjoint_left.mpr fun x hxO hxe' => ?_
    obtain ⟨a, b, hab, -, hEab⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e'
    have hxab := hEab ▸ hxe'
    have ha := hOvertices x hxO a hxab.1
    have hb := hOvertices x hxO b hxab.2
    have hxwv : x ∈ section34VertexBallImage src f₁ w ∩
        section34VertexBallImage src f₁ v := by
      rcases ha with haw | hav
      · have hbv : b = v := hb.resolve_left fun hbw => hab (haw.trans hbw.symm)
        exact ⟨haw ▸ hxab.1, hbv ▸ hxab.2⟩
      · have hbw : b = w := hb.resolve_right fun hbv => hab (hav.trans hbv.symm)
        exact ⟨hbw ▸ hxab.2, hav ▸ hxab.1⟩
    have hxe : x ∈ section34SplitDiskImage src f₁ e := hinter.symm ▸ hxwv
    exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁.injOn he) hxe' hxe

end DifferentialGeometry.Topology.PiecewiseLinear
