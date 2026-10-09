/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ClawBall
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraEdges

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

open Classical in
theorem Section34CutFrame.splitDiskImage_subset_frontier_clawBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t)
    (hd : d ∈ t) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) {e : Section34EdgeIndex 𝒦 𝒦'} {w w' : Section34VertexIndex 𝒦 𝒦'}
    {p p' : Ea} (hw : w.1 = {p}) (hw' : w'.1 = {p'})
    (hp : p ∈ segment ℝ a b ∨ (p ∈ segment ℝ a c ∧ p ≠ c) ∨ (p ∈ segment ℝ b d ∧ p ≠ d))
    (hp' : p' ∈ segment ℝ d c ∨ (p' ∈ segment ℝ d a ∧ p' ≠ a) ∨
      (p' ∈ segment ℝ c b ∧ p' ≠ b))
    (hwe : w.1 ⊆ e.1) (hw'e : w'.1 ⊆ e.1)
    {chart : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVc : ∀ v : Section34VertexIndex 𝒦 𝒦', v.1 ⊆ e.1 →
      section34VertexBallImage src f₁ v ⊆ chart.source) :
    section34SplitDiskImage src f₁ e ⊆
        section34ClawBall (section34VertexBallImage src f₁) a b c d ∩
          section34ClawBall (section34VertexBallImage src f₁) d c a b ∧
      section34SplitDiskImage src f₁ e ⊆
        frontier (section34ClawBall (section34VertexBallImage src f₁) a b c d) ∧
      section34SplitDiskImage src f₁ e ⊆
        frontier (section34ClawBall (section34VertexBallImage src f₁) d c a b) ∧
      section34SplitDiskImage src f₁ e \ section34SplitDiskImage srcBd f₁ e ⊆
        interior (section34ClawBall (section34VertexBallImage src f₁) a b c d ∪
          section34ClawBall (section34VertexBallImage src f₁) d c a b) := by
  set V := section34VertexBallImage src f₁
  set B₁ := section34ClawBall V a b c d
  set B₂ := section34ClawBall V d c a b
  have hnot : ∀ {q : Ea},
      (q ∈ segment ℝ a b ∨ (q ∈ segment ℝ a c ∧ q ≠ c) ∨ (q ∈ segment ℝ b d ∧ q ≠ d)) →
      (q ∈ segment ℝ d c ∨ (q ∈ segment ℝ d a ∧ q ≠ a) ∨ (q ∈ segment ℝ c b ∧ q ≠ b)) →
      False := fun h₁ h₂ =>
        SimplicialComplex.not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd h₁ h₂
  have hww : w ≠ w' := by
    intro h
    have hpp : p = p' := by
      rw [h, hw'] at hw
      exact (Finset.singleton_injective hw).symm
    rw [hpp] at hp
    exact hnot hp hp'
  have hwB₁ : V w ⊆ B₁ := fun z hz => mem_iUnion₂.mpr ⟨w, ⟨p, hw, hp⟩, hz⟩
  have hw'B₂ : V w' ⊆ B₂ := fun z hz => mem_iUnion₂.mpr ⟨w', ⟨p', hw', hp'⟩, hz⟩
  have hE : V w ∩ V w' = section34SplitDiskImage src f₁ e :=
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
  have hfr : ∀ {P W : Set M₂}, P ⊆ closure (interior W) → Disjoint (interior W) B₁ →
      P ⊆ B₁ → P ⊆ frontier B₁ := by
    intro P W hPW hWB hPB z hz
    refine ⟨subset_closure (hPB hz), fun hzi => ?_⟩
    obtain ⟨y, hyo, hyW⟩ := mem_closure_iff.mp (hPW hz) _ isOpen_interior hzi
    exact Set.disjoint_left.mp hWB hyW (interior_subset hyo)
  have hfr₂ : ∀ {P W : Set M₂}, P ⊆ closure (interior W) → Disjoint (interior W) B₂ →
      P ⊆ B₂ → P ⊆ frontier B₂ := by
    intro P W hPW hWB hPB z hz
    refine ⟨subset_closure (hPB hz), fun hzi => ?_⟩
    obtain ⟨y, hyo, hyW⟩ := mem_closure_iff.mp (hPW hz) _ isOpen_interior hzi
    exact Set.disjoint_left.mp hWB hyW (interior_subset hyo)
  have hVw := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hVw' := hcut.isPLCellOn_vertexBallImage hf₁ w'
  have hEfw : section34SplitDiskImage src f₁ e ⊆ frontier (V w) :=
    hcut.splitDiskImage_subset_frontier hf₁ hwe
  have hEfw' : section34SplitDiskImage src f₁ e ⊆ frontier (V w') :=
    hcut.splitDiskImage_subset_frontier hf₁ hw'e
  have hcl : ∀ (W Wb : Set M₂), IsPLCellOn 3 W Wb →
      frontier W ⊆ closure (interior W) := fun _ _ hW =>
    hW.isCompact.isClosed.frontier_subset.trans hW.subset_closure_interior
  have hEB : section34SplitDiskImage src f₁ e ⊆ B₁ ∩ B₂ := by
    rw [← hE]
    exact inter_subset_inter hwB₁ hw'B₂
  refine ⟨hEB, hfr (hEfw'.trans (hcl _ _ hVw')) hint₁ (hEB.trans inter_subset_left),
    hfr₂ (hEfw.trans (hcl _ _ hVw)) hint₂ (hEB.trans inter_subset_right), ?_⟩
  have hpp : p ≠ p' := by
    intro h
    have h' : w = w' := Subtype.ext (by rw [hw, hw', h])
    exact hww h'
  have hepair : e.1 = {p, p'} :=
    (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset (hwe (by rw [hw]; simp))
        (Finset.singleton_subset_iff.mpr (hw'e (by rw [hw']; simp))))
      (by rw [e.2.2.1, Finset.card_pair hpp])).symm
  have hends : (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) := by
    rw [hepair, hw, hw']
    simp only [Finset.coe_pair, Finset.coe_singleton, singleton_union]
  refine (hcut.splitDiskImage_sdiff_subset_interior hf₁ e hchart hVc).trans
    (interior_mono (iUnion₂_subset fun v hv => ?_))
  rcases eq_or_eq_of_section34VertexIndex_subset e hends hv with rfl | rfl
  · exact hwB₁.trans subset_union_left
  · exact hw'B₂.trans subset_union_right

open Classical in
theorem Section34CutFrame.clawBall_inter_clawBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34EdgeIndex 𝒦 𝒦'}
    (hea : ∀ e : Section34EdgeIndex 𝒦 𝒦', a ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d → e = ea)
    (heb : ∀ e : Section34EdgeIndex 𝒦 𝒦', b ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c → e = eb)
    (hec : ∀ e : Section34EdgeIndex 𝒦 𝒦', c ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a → e = ec)
    (hed : ∀ e : Section34EdgeIndex 𝒦 𝒦', d ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b → e = ed) :
    section34ClawBall (section34VertexBallImage src f₁) a b c d ∩
        section34ClawBall (section34VertexBallImage src f₁) d c a b ⊆
      section34SplitDiskImage src f₁ ea ∪ section34SplitDiskImage src f₁ eb ∪
        section34SplitDiskImage src f₁ ec ∪ section34SplitDiskImage src f₁ ed := by
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
    exact SimplicialComplex.not_mem_claw_and_mem_claw ht ha hb hc hd hab hac had hbc hbd hcd hp hp'
  obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hww hzw hzw'
  have hpe : p ∈ e.1 := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzw
    (by rw [hw]; exact Finset.mem_singleton_self p)
  have hp'e : p' ∈ e.1 := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzw'
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

omit [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
open Classical in
theorem section34VertexBallImage_subset_clawBall_union (hmap : 𝒦'.map = 𝒦.map)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (htabcd : t = {a, b, c, d})
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : Section34Incident w.1 t) :
    section34VertexBallImage src f₁ w ⊆
      section34ClawBall (section34VertexBallImage src f₁) a b c d ∪
        section34ClawBall (section34VertexBallImage src f₁) d c a b := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hpg : 𝒦.map p ∈ graphSkeletonSpace 𝒦 := by
    rw [← hmap]
    exact w.2.2.2 ⟨p, subset_convexHull ℝ _ hpw, rfl⟩
  obtain ⟨x, hx, y, hy, hpxy⟩ :=
    exists_mem_segment_of_mem_convexHull_of_map_mem_graphSkeleton ht (hw hpw) hpg
  intro z hz
  rcases SimplicialComplex.mem_claw_or_mem_claw_of_mem_segment htabcd hx hy hpxy with h | h
  · exact Or.inl (mem_iUnion₂.mpr ⟨w, ⟨p, hp, h⟩, hz⟩)
  · exact Or.inr (mem_iUnion₂.mpr ⟨w, ⟨p, hp, h⟩, hz⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
