/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TargetCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34BigonBall (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3)
    (hop : Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd s) :
    ∃ (w v : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (B B' Bb Dj Jd : Set M₂) (c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))),
      IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ section34VertexBallImage srcBd f₁ w ∧
      Bb ⊆ section34SplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ e', section34SplitDiskImage src f₁ e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ section34SplitDiskImage srcBd f₁ e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧
      Dj ⊆ section34VertexBallImage srcBd f₁ w ∩
        frontier (⋃ w', section34VertexBallImage src f₁ w') ∧ Jd = B ∪ B' ∧
      (∀ s', Disjoint (Dj \ Jd) (fblBd s')) ∧
      w ≠ v ∧ Section34Incident w.1 s.1 ∧ Section34Incident v.1 s.1 ∧
      Section34Incident e.1 s.1 ∧
      section34SplitDiskImage src f₁ e =
        section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ v ∧
      c ∈ (plGroupoid 3).maximalAtlas M₂ ∧ fbl s ⊆ c.source ∧
      section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source ∧
      section34VertexBallImage src f₁ w ∪ section34VertexBallImage src f₁ v ⊆ c.source ∧
      IsPLBall 3 (c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v)) ∧ IsPLBall 2 (c '' Dj) ∧
      c '' Dj ⊆ frontier (c '' (section34VertexBallImage src f₁ w ∪
        section34VertexBallImage src f₁ v)) := by
  classical
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨hfcell, -, hfavoid, -, -, -, -, -, -, hext⟩ := id hinv
  obtain ⟨w, e, B, B', Bb, Dj, Jd, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean⟩ := hop
  have hBb : Bb.Nonempty := by
    obtain ⟨P, q, u, -, -, -, hBb⟩ := hB
    rw [hBb]
    exact ((nonempty_stdSimplexBoundary_of_pos (by decide : 0 < 1)).image q).image u
  obtain ⟨x, hx⟩ := hBb
  have hxB : x ∈ B := hB.boundary_subset hx
  have hxF : x ∈ fbl s := (hfcell s).boundary_subset (hBf hxB)
  have hxw : x ∈ section34VertexBallImage src f₁ w :=
    (hcut.isPLCellOn_vertexBallImage hf₁ w).boundary_subset (hBw hxB)
  have hxe : x ∈ section34SplitDiskImage src f₁ e :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset (hBbe hx)
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hxe hxw
  obtain ⟨-, -, -, -, hbd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hends, -, -⟩ :=
    id hcut
  obtain ⟨a, b, hab, heab, hEab⟩ := hends e
  have hpair : ∃ v : Section34VertexIndex 𝒦 𝒦', w ≠ v ∧
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (v.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall v) := by
    rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, hab, heab, hEab⟩
    · exact ⟨a, hab.symm, heab.trans (union_comm _ _), hEab.trans (inter_comm _ _)⟩
  obtain ⟨v, hwv, hewv, hEwv⟩ := hpair
  have hN : ∀ z : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall z) ⊆ section34CutNeighborhood src :=
    fun z => subset_iUnion (fun z => src (Section34Label.vertexBall z)) z
  have hinter : section34SplitDiskImage src f₁ e =
      section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ v := by
    change f₁ '' src (.splitDisk e) = f₁ '' src (.vertexBall w) ∩ f₁ '' src (.vertexBall v)
    rw [hEwv]
    exact hf₁.injOn.image_inter (hN w) (hN v)
  have hxv : x ∈ section34VertexBallImage src f₁ v := (hinter ▸ hxe).2
  have hinc : ∀ z : Section34VertexIndex 𝒦 𝒦',
      x ∈ section34VertexBallImage src f₁ z → Section34Incident z.1 s.1 := by
    intro z hxz
    by_contra hn
    have hmem : x ∈ fbl s ∩ section34VertexBallImage src f₁ z := ⟨hxF, hxz⟩
    rw [hfavoid s z hn] at hmem
    exact hmem
  have hwi := hinc w hxw
  have hvi := hinc v hxv
  have hei : Section34Incident e.1 s.1 := by
    change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [hewv]
    exact union_subset hwi hvi
  obtain ⟨c, hc, hfc, hTc, -, -⟩ :=
    exists_chart_section34FaceBall hh hcut hctrl hgraph hext s (hfavoid s)
  have hVc : ∀ z : Section34VertexIndex 𝒦 𝒦', Section34Incident z.1 s.1 →
      section34VertexBallImage src f₁ z ⊆ c.source := by
    intro z hzi y hy
    exact hTc (mem_section34FaceTorus_iff.mpr ⟨z, hzi, hy⟩)
  have hwc := hVc w hwi
  have hvc := hVc v hvi
  have hYc := union_subset hwc hvc
  have hEc : section34SplitDiskImage src f₁ e ⊆ c.source := by
    rw [hinter]
    exact inter_subset_left.trans hwc
  have hwcell := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hvcell := hcut.isPLCellOn_vertexBallImage hf₁ v
  obtain ⟨hW, hWbd⟩ := hwcell.isPLBall_image_chart hc hwc
  obtain ⟨hV, hVbd⟩ := hvcell.isPLBall_image_chart hc hvc
  obtain ⟨q, hq, -⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_image_chart hc hEc
  have hci : c '' section34VertexBallImage src f₁ w ∩
      c '' section34VertexBallImage src f₁ v = c '' section34SplitDiskImage src f₁ e := by
    rw [hinter]
    exact (c.injOn.image_inter hwc hvc).symm
  have hsrcbd : ∀ z : Section34VertexIndex 𝒦 𝒦',
      src (.splitDisk e) ⊆ src (.vertexBall z) →
      src (.splitDisk e) ⊆ srcBd (.vertexBall z) := by
    intro z hz y hy
    rw [hbd (.vertexBall z)]
    exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hz, by simp⟩, hy⟩
  have hEw : section34SplitDiskImage src f₁ e ⊆
      section34VertexBallImage srcBd f₁ w :=
    image_mono (hsrcbd w (by rw [hEwv]; exact inter_subset_left))
  have hEv : section34SplitDiskImage src f₁ e ⊆
      section34VertexBallImage srcBd f₁ v :=
    image_mono (hsrcbd v (by rw [hEwv]; exact inter_subset_right))
  have hY : IsPLBall 3 (c '' (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ v)) := by
    rw [image_union]
    refine isPLBall_union_of_inter_isPLBall_two hW hV ?_ ?_ ?_
    · rw [hci]
      exact ⟨q, hq⟩
    · rw [hci, ← hWbd]
      exact image_mono hEw
    · rw [hci, ← hVbd]
      exact image_mono hEv
  have hDw : Dj ⊆ section34VertexBallImage src f₁ w :=
    fun y hy => hwcell.boundary_subset (hDS hy).1
  have hDc : Dj ⊆ c.source := hDw.trans hwc
  obtain ⟨r, hr, -⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hDF : c '' Dj ⊆ frontier (c '' (section34VertexBallImage src f₁ w ∪
      section34VertexBallImage src f₁ v)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨subset_closure ⟨y, Or.inl (hDw hy), rfl⟩, fun hcy => ?_⟩
    have hiy := OpenPartialHomeomorph.mem_interior_of_mem_interior_image c hYc (hDc hy) hcy
    apply (hDS hy).2.2
    exact interior_mono (union_subset (subset_iUnion _ w) (subset_iUnion _ v)) hiy
  exact ⟨w, v, e, B, B', Bb, Dj, Jd, c, hB, hBf, hBw, hBbe, hBsplit, hB', hB'e,
    hBB', hD, hDS, hJ, hclean, hwv, hwi, hvi, hei, hinter, hc, hfc, hTc, hYc, hY,
    ⟨r, hr⟩, hDF⟩

end DifferentialGeometry.Topology.PiecewiseLinear
