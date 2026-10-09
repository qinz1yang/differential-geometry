/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraClaws
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionMeetingDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.disjoint_interior_vertexBallImage
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w u : Section34CompactVertexIndex K K'} (hwu : w ≠ u) :
    Disjoint (interior (section34CompactVertexBallImage src f₁ w))
      (section34CompactVertexBallImage src f₁ u) := by
  refine Set.disjoint_left.mpr fun z hz hzu => ?_
  obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hwu (interior_subset hz) hzu
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hze (interior_subset hz)
  exact (hcut.splitDiskImage_subset_frontier hf₁ hwe hze).2 hz

theorem Section34CompactCutFrame.splitDiskImage_subset_frontier_clawBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t)
    (hd : d ∈ t) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {e : Section34CompactEdgeIndex K K'} {w w' : Section34CompactVertexIndex K K'}
    {p p' : E3} (hw : w.1 = {p}) (hw' : w'.1 = {p'})
    (hp : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (hp' : p' ∈ segment ℝ d c ∨ (p' ∈ segment ℝ d a ∧ p' ≠ a) ∨
      (p' ∈ segment ℝ c b ∧ p' ≠ b))
    (hwe : w.1 ⊆ e.1) (hw'e : w'.1 ⊆ e.1) :
    section34CompactSplitDiskImage src f₁ e ⊆
        section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b ∧
      section34CompactSplitDiskImage src f₁ e ⊆
        frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d) ∧
      section34CompactSplitDiskImage src f₁ e ⊆
        frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) ∧
      section34CompactSplitDiskImage src f₁ e \ section34CompactSplitDiskImage srcBd f₁ e ⊆
        interior (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∪
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) := by
  set V := section34CompactVertexBallImage src f₁
  set B₁ := section34CompactClawBall V a b c d
  set B₂ := section34CompactClawBall V d c a b
  have hnot : ∀ {q : E3},
      (q ∈ segment ℝ a b ∨ (q ∈ segment ℝ a c ∧ q ≠ c) ∨ (q ∈ segment ℝ b d ∧ q ≠ d)) →
      (q ∈ segment ℝ d c ∨ (q ∈ segment ℝ d a ∧ q ≠ a) ∨ (q ∈ segment ℝ c b ∧ q ≠ b)) →
      False := fun h₁ h₂ => not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd h₁ h₂
  have hww : w ≠ w' := by
    intro h
    have hpp : p = p' := by
      rw [h, hw'] at hw
      exact (Finset.singleton_injective hw).symm
    rw [hpp] at hp
    exact hnot hp hp'
  have hwB₁ : V w ⊆ B₁ := fun z hz => mem_iUnion₂.mpr ⟨w, ⟨p, hw, hp⟩, hz⟩
  have hw'B₂ : V w' ⊆ B₂ := fun z hz => mem_iUnion₂.mpr ⟨w', ⟨p', hw', hp'⟩, hz⟩
  have hE : V w ∩ V w' = section34CompactSplitDiskImage src f₁ e :=
    hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww hwe hw'e
  have hint₁ : Disjoint (interior (V w')) B₁ := by
    refine Set.disjoint_left.mpr fun z hz hzB => ?_
    obtain ⟨u, ⟨q, hu, hq⟩, hzu⟩ := mem_iUnion₂.mp hzB
    have hu' : w' ≠ u := by
      intro h
      rw [← h, hw'] at hu
      rw [← Finset.singleton_injective hu] at hq
      exact hnot hq hp'
    exact Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hu') hz hzu
  have hint₂ : Disjoint (interior (V w)) B₂ := by
    refine Set.disjoint_left.mpr fun z hz hzB => ?_
    obtain ⟨u, ⟨q, hu, hq⟩, hzu⟩ := mem_iUnion₂.mp hzB
    have hu' : w ≠ u := by
      intro h
      rw [← h, hw] at hu
      rw [← Finset.singleton_injective hu] at hq
      exact hnot hp hq
    exact Set.disjoint_left.mp (hcut.disjoint_interior_vertexBallImage hf₁ hu') hz hzu
  have hfr : ∀ {P W : Set E3}, P ⊆ closure (interior W) → Disjoint (interior W) B₁ →
      P ⊆ B₁ → P ⊆ frontier B₁ := by
    intro P W hPW hWB hPB z hz
    refine ⟨subset_closure (hPB hz), fun hzi => ?_⟩
    obtain ⟨y, hyo, hyW⟩ := mem_closure_iff.mp (hPW hz) _ isOpen_interior hzi
    exact Set.disjoint_left.mp hWB hyW (interior_subset hyo)
  have hfr₂ : ∀ {P W : Set E3}, P ⊆ closure (interior W) → Disjoint (interior W) B₂ →
      P ⊆ B₂ → P ⊆ frontier B₂ := by
    intro P W hPW hWB hPB z hz
    refine ⟨subset_closure (hPB hz), fun hzi => ?_⟩
    obtain ⟨y, hyo, hyW⟩ := mem_closure_iff.mp (hPW hz) _ isOpen_interior hzi
    exact Set.disjoint_left.mp hWB hyW (interior_subset hyo)
  have hVw : IsPLBall 3 (V w) := (hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three
  have hVw' : IsPLBall 3 (V w') := (hcut.isPLCellOn_vertexBallImage hf₁ w').isPLBall_three
  have hEfw : section34CompactSplitDiskImage src f₁ e ⊆ frontier (V w) :=
    hcut.splitDiskImage_subset_frontier hf₁ hwe
  have hEfw' : section34CompactSplitDiskImage src f₁ e ⊆ frontier (V w') :=
    hcut.splitDiskImage_subset_frontier hf₁ hw'e
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hcl : ∀ W : Set E3, IsPLBall 3 W → frontier W ⊆ closure (interior W) := fun W hW => by
    rw [hW.closure_interior_of_finrank hdim]
    exact hW.isPolyhedron.isClosed.frontier_subset
  have hEB : section34CompactSplitDiskImage src f₁ e ⊆ B₁ ∩ B₂ := by
    rw [← hE]
    exact inter_subset_inter hwB₁ hw'B₂
  refine ⟨hEB, hfr (hEfw'.trans (hcl _ hVw')) hint₁ (hEB.trans inter_subset_left),
    hfr₂ (hEfw.trans (hcl _ hVw)) hint₂ (hEB.trans inter_subset_right), ?_⟩
  obtain ⟨q, hq, hqb⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  rw [hqb]
  exact (sdiff_subset_interior_union_of_inter_eq hVw hVw' hq hE hEfw hEfw').trans
    (interior_mono (union_subset_union hwB₁ hw'B₂))

theorem exists_vertexIndex_pair_of_mem_edgeIndex
    (e : Section34CompactEdgeIndex K K') {u : E3} (hu : u ∈ e.1) :
    ∃ (w w' : Section34CompactVertexIndex K K') (p' : E3), w.1 = {u} ∧ w'.1 = {p'} ∧
      p' ∈ e.1 ∧ p' ≠ u ∧ w.1 ⊆ e.1 ∧ w'.1 ⊆ e.1 := by
  classical
  obtain ⟨p', hp', hsub⟩ := exists_subset_pair_of_card_le_two e.2.2.1.le hu
  have hp'u : p' ≠ u := by
    intro h
    rw [h] at hsub
    have hcard : e.1.card ≤ ({u} : Finset E3).card := by
      refine Finset.card_le_card fun z hz => ?_
      have hz' := hsub (Finset.mem_coe.mpr hz)
      simp only [mem_insert_iff, mem_singleton_iff, or_self] at hz'
      exact Finset.mem_singleton.mpr hz'
    rw [e.2.2.1, Finset.card_singleton] at hcard
    omega
  have hvert : ∀ {q : E3}, q ∈ e.1 → ∃ w : Section34CompactVertexIndex K K', w.1 = {q} :=
    fun hq => exists_section34CompactVertexIndex_eq_singleton
      (K'.down_closed e.2.1 (Finset.singleton_subset_iff.mpr hq) (Finset.singleton_nonempty _))
      (e.2.2.2 (subset_convexHull ℝ _ hq))
  obtain ⟨w, hw⟩ := hvert hu
  obtain ⟨w', hw'⟩ := hvert hp'
  refine ⟨w, w', p', hw, hw', hp', hp'u, ?_, ?_⟩
  · rw [hw]
    exact Finset.singleton_subset_iff.mpr hu
  · rw [hw']
    exact Finset.singleton_subset_iff.mpr hp'

theorem Section34CompactCutFrame.clawBall_inter_clawBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34CompactEdgeIndex K K'}
    (hea : ∀ e : Section34CompactEdgeIndex K K', a ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d → e = ea)
    (heb : ∀ e : Section34CompactEdgeIndex K K', b ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c → e = eb)
    (hec : ∀ e : Section34CompactEdgeIndex K K', c ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a → e = ec)
    (hed : ∀ e : Section34CompactEdgeIndex K K', d ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b → e = ed) :
    section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∩
        section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b ⊆
      section34CompactSplitDiskImage src f₁ ea ∪ section34CompactSplitDiskImage src f₁ eb ∪
        section34CompactSplitDiskImage src f₁ ec ∪ section34CompactSplitDiskImage src f₁ ed := by
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  rintro z ⟨hz1, hz2⟩
  obtain ⟨w, ⟨p, hw, hp⟩, hzw⟩ := mem_iUnion₂.mp hz1
  obtain ⟨w', ⟨p', hw', hp'⟩, hzw'⟩ := mem_iUnion₂.mp hz2
  have hww : w ≠ w' := by
    intro h
    rw [h, hw'] at hw
    rw [Finset.singleton_injective hw] at hp'
    exact not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd hp hp'
  obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ hww hzw hzw'
  have hpe : p ∈ e.1 := hcut.subset_of_mem_splitDiskImage hf₁ hze hzw
    (by rw [hw]; exact Finset.mem_singleton_self p)
  have hp'e : p' ∈ e.1 := hcut.subset_of_mem_splitDiskImage hf₁ hze hzw'
    (by rw [hw']; exact Finset.mem_singleton_self p')
  rcases hcut.mem_segment_of_mem_claw_of_mem_claw ht htabcd hab hac had hbc hbd hcd hpe hp'e hp
    hp' with h | h | h | h
  · rw [hea e h.1 h.2] at hze
    exact Or.inl (Or.inl (Or.inl hze))
  · rw [heb e h.1 h.2] at hze
    exact Or.inl (Or.inl (Or.inr hze))
  · rw [hec e h.1 h.2] at hze
    exact Or.inl (Or.inr hze)
  · rw [hed e h.1 h.2] at hze
    exact Or.inr hze

theorem vertexBallImage_subset_clawBall_union
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (htabcd : t = {a, b, c, d})
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t) :
    section34CompactVertexBallImage src f₁ w ⊆
      section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∪
        section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set E3) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  obtain ⟨x, hx, y, hy, hpxy⟩ := exists_mem_segment_of_mem_convexHull_graphSkeleton ht (hw hpw)
    (w.2.2.2 (subset_convexHull ℝ _ hpw))
  intro z hz
  rcases mem_claw_or_mem_claw_of_mem_segment htabcd hx hy hpxy with h | h
  · exact Or.inl (mem_iUnion₂.mpr ⟨w, ⟨p, hp, h⟩, hz⟩)
  · exact Or.inr (mem_iUnion₂.mpr ⟨w, ⟨p, hp, h⟩, hz⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
