/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourDiskPocket
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraFaceRuns

open Set

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

open Classical in
theorem Section34NormalPlus.exists_isPLBall_of_tetra_in_chart
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {a b c d : Ea} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34EdgeIndex 𝒦 𝒦'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set Ea) ⊆ segment ℝ a d)
    (hea : ∀ e : Section34EdgeIndex 𝒦 𝒦', a ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ a d → e = ea)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set Ea) ⊆ segment ℝ b c)
    (heb : ∀ e : Section34EdgeIndex 𝒦 𝒦', b ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ b c → e = eb)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set Ea) ⊆ segment ℝ c a)
    (hec : ∀ e : Section34EdgeIndex 𝒦 𝒦', c ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ c a → e = ec)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set Ea) ⊆ segment ℝ d b)
    (hed : ∀ e : Section34EdgeIndex 𝒦 𝒦', d ∈ e.1 →
      convexHull ℝ (e.1 : Set Ea) ⊆ segment ℝ d b → e = ed)
    {sacd sabc sbcd sabd : Section34SimplexIndex 𝒦 3} (hsacd : sacd.1 = {a, c, d})
    (hsabc : sabc.1 = {a, b, c}) (hsbcd : sbcd.1 = {b, c, d}) (hsabd : sabd.1 = {a, b, d})
    {chart : OpenPartialHomeomorph M₂ E3}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVchart : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t →
      section34VertexBallImage src f₁ w ⊆ chart.source)
    (hDchart : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t →
      tgtD s ⊆ chart.source) :
    let C₁ := chart '' section34ClawBall (section34VertexBallImage src f₁) a b c d
    let C₂ := chart '' section34ClawBall (section34VertexBallImage src f₁) d c a b
    let D : Fin 4 → Set E3 := fun k => chart '' tgtD (![sacd, sabc, sbcd, sabd] k)
    ∃ R A Ω : Set E3, IsPLBall 3 R ∧ frontier R = A ∪ (⋃ k, D k) ∪ Ω ∧
      A ⊆ frontier C₁ ∧ Ω ⊆ frontier C₂ ∧
      (∃ qA : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
        ∀ k, D k ∩ C₁ ⊆ qA '' stdSimplexBoundary 2) ∧
      (∃ qΩ : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qΩ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ω ∧
        ∀ k, D k ∩ C₂ ⊆ qΩ '' stdSimplexBoundary 2) ∧
      Ω ∩ C₁ ⊆ A ∧ A ∩ C₂ ⊆ Ω ∧ Disjoint (interior R) (C₁ ∪ C₂) := by
  classical
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨hinj, h12M, hH₁M, hH₂M, hHintM⟩ := hcut.clawBall_holes hf₁ ht htabcd hab hac had
    hbc hbd hcd hea₁ hea₂ hea heb₁ heb₂ heb hec₁ hec₂ hec hed₁ hed₂ hed hchart hVchart
  obtain ⟨pin, pout, γ₁, γ₂, hp, hq, hDi, hDj, hDo, hDbM, hintM, hg₁, hg₂⟩ :=
    hdisk.exists_faceRuns_of_tetra hdata ht htabcd hab hac had hbc hbd hcd hea₁ hea₂ heb₁
      heb₂ hec₁ hec₂ hed₁ hed₂ hinj h12M hsacd hsabc hsbcd hsabd hchart hVchart hDchart
  set V := section34VertexBallImage src f₁
  set B₁ := section34ClawBall V a b c d
  set B₂ := section34ClawBall V d c a b
  let C₁ := chart '' B₁
  let C₂ := chart '' B₂
  let eH : Fin 4 → Section34EdgeIndex 𝒦 𝒦' := ![ec, eb, ed, ea]
  let F : Fin 4 → Section34SimplexIndex 𝒦 3 := ![sacd, sabc, sbcd, sabd]
  let E : Fin 4 → Set M₂ := fun k => section34SplitDiskImage src f₁ (eH k)
  let Eb : Fin 4 → Set M₂ := fun k => section34SplitDiskImage srcBd f₁ (eH k)
  let DH : Fin 4 → Set E3 := fun k => chart '' E k
  let D : Fin 4 → Set E3 := fun k => chart '' tgtD (F k)
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hsegt : ∀ {x y : Ea}, x ∈ t → y ∈ t → segment ℝ x y ⊆ convexHull ℝ (t : Set Ea) :=
    fun hx hy => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hx)
      (subset_convexHull ℝ _ hy)
  have hBc : ∀ x y x' y' : Ea, x ∈ t → y ∈ t → x' ∈ t → y' ∈ t →
      section34ClawBall V x y x' y' ⊆ chart.source := by
    intro x y x' y' hx hy hx' hy' z hz
    obtain ⟨w, ⟨p, hwp, hpc⟩, hzw⟩ := mem_iUnion₂.mp hz
    refine hVchart w ?_ hzw
    rw [Section34Incident, hwp, Finset.coe_singleton, singleton_subset_iff]
    rcases hpc with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt hx hy h
    · exact hsegt hx hx' h
    · exact hsegt hy hy' h
  have hB₁src : B₁ ⊆ chart.source := hBc a b c d ha hb hc hd
  have hB₂src : B₂ ⊆ chart.source := hBc d c a b hd hc ha hb
  have hB₁M := hcut.isPLCellOn_section34ClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc hcd
    hchart hVchart
  have hB₂M := hcut.isPLCellOn_section34ClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
    hbd.symm hac.symm hab hchart hVchart
  have hB₁closed : IsClosed B₁ := hB₁M.isCompact.isClosed
  obtain ⟨hB₁, hfr₁⟩ := hB₁M.isPLBall_image_chart hchart hB₁src
  obtain ⟨hB₂, hfr₂⟩ := hB₂M.isPLBall_image_chart hchart hB₂src
  have hEsrc : ∀ k, E k ⊆ chart.source :=
    fun k => (hH₁M k).trans (hB₁closed.frontier_subset.trans hB₁src)
  have htri : ∀ {s : Finset Ea} {x y z : Ea}, s = {x, y, z} →
      x ∈ t → y ∈ t → z ∈ t → Section34Incident s t := by
    intro s x y z hs hx hy hz u hu
    rw [hs] at hu
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact subset_convexHull ℝ _ hx
    · exact subset_convexHull ℝ _ hy
    · exact subset_convexHull ℝ _ hz
  have hFt : ∀ k, Section34Incident (F k).1 t := by
    intro k
    fin_cases k
    exacts [htri hsacd ha hc hd, htri hsabc ha hb hc, htri hsbcd hb hc hd, htri hsabd ha hb hd]
  have hDsrc : ∀ k, tgtD (F k) ⊆ chart.source := fun k => hDchart (F k) (hFt k)
  have hinter : ∀ {P Q : Set M₂}, P ⊆ chart.source → Q ⊆ chart.source →
      chart '' (P ∩ Q) = chart '' P ∩ chart '' Q := fun hP hQ => chart.injOn.image_inter hP hQ
  have hdisjImage : ∀ {P Q : Set M₂}, P ⊆ chart.source → Q ⊆ chart.source →
      Disjoint P Q → Disjoint (chart '' P) (chart '' Q) := by
    intro P Q hP hQ hPQ
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' : y = x := chart.injOn (hQ hy) (hP hx) hyx
    exact Set.disjoint_left.mp hPQ hx (hyx' ▸ hy)
  have h12 : C₁ ∩ C₂ = ⋃ k, DH k := by
    change chart '' B₁ ∩ chart '' B₂ = ⋃ k, chart '' E k
    rw [← hinter hB₁src hB₂src, h12M, image_iUnion]
  have hH₁ : ∀ k, DH k ⊆ frontier C₁ := by
    intro k
    rw [← hfr₁]
    exact image_mono (hH₁M k)
  have hH₂ : ∀ k, DH k ⊆ frontier C₂ := by
    intro k
    rw [← hfr₂]
    exact image_mono (hH₂M k)
  have hrHex : ∀ k, ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (DH k) ∧
        chart '' Eb k = r '' stdSimplexBoundary 2 := fun k =>
    (hcut.isPLCellOn_splitDiskImage hf₁ (eH k)).exists_isPLHomeomorphOn_image_chart
      hchart (hEsrc k)
  choose rH hrH hrHb using hrHex
  obtain ⟨hD1, -, hD3, hD4, hD5, -⟩ := id hdisk
  have hqDex : ∀ k, ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D k) ∧
        chart '' tgtDBd (F k) = q '' stdSimplexBoundary 2 := fun k =>
    (hD1 (F k)).exists_isPLHomeomorphOn_image_chart hchart (hDsrc k)
  choose qD hqD hqDb using hqDex
  have hHdisj : Pairwise fun k l => Disjoint (DH k) (DH l) := fun k l hkl =>
    hdisjImage (hEsrc k) (hEsrc l) (hcut.disjoint_splitDiskImage hf₁.injOn (hinj k l hkl))
  have hHint : ∀ k, DH k \ rH k '' stdSimplexBoundary 2 ⊆ interior (C₁ ∪ C₂) := by
    intro k z hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    have hxb : x ∉ Eb k := fun hxb => hz.2 (hrHb k ▸ mem_image_of_mem chart hxb)
    have hxi : x ∈ interior (B₁ ∪ B₂) := hHintM k ⟨hx, hxb⟩
    have hi : chart '' interior (B₁ ∪ B₂) ⊆ interior (chart '' (B₁ ∪ B₂)) :=
      interior_maximal (image_mono interior_subset)
        (chart.isOpen_image_of_subset_source isOpen_interior
          (interior_subset.trans (union_subset hB₁src hB₂src)))
    rw [image_union] at hi
    exact hi (mem_image_of_mem chart hxi)
  have hne : ∀ {s s' : Section34SimplexIndex 𝒦 3} {u : Ea}, u ∈ s.1 → u ∉ s'.1 →
      s ≠ s' := fun hu hu' h => hu' (h ▸ hu)
  have hmem : ∀ {s : Finset Ea} {x y z u : Ea}, s = {x, y, z} → (u = x ∨ u = y ∨ u = z) →
      u ∈ s := by
    intro s x y z u hs hu
    rw [hs]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hu
  have hnmem : ∀ {s : Finset Ea} {x y z u : Ea}, s = {x, y, z} → u ≠ x → u ≠ y → u ≠ z →
      u ∉ s := by
    intro s x y z u hs hx hy hz hu
    rw [hs] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  have h01 : sacd ≠ sabc := hne (hmem hsabc (Or.inr (Or.inl rfl)) : b ∈ sabc.1)
    (hnmem hsacd hab.symm hbc hbd) |>.symm
  have h02 : sacd ≠ sbcd := hne (hmem hsacd (Or.inl rfl) : a ∈ sacd.1) (hnmem hsbcd hab hac had)
  have h03 : sacd ≠ sabd := hne (hmem hsacd (Or.inr (Or.inl rfl)) : c ∈ sacd.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have h12' : sabc ≠ sbcd := hne (hmem hsabc (Or.inl rfl) : a ∈ sabc.1) (hnmem hsbcd hab hac had)
  have h13 : sabc ≠ sabd := hne (hmem hsabc (Or.inr (Or.inr rfl)) : c ∈ sabc.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have h23 : sbcd ≠ sabd := hne (hmem hsbcd (Or.inr (Or.inl rfl)) : c ∈ sbcd.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have hFinj : ∀ k l : Fin 4, k ≠ l → F k ≠ F l := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h03 | exact h03.symm
      | exact h12' | exact h12'.symm | exact h13 | exact h13.symm | exact h23 | exact h23.symm
  have hDdisj : Pairwise fun k l => Disjoint (D k) (D l) := fun k l hkl =>
    hdisjImage (hDsrc k) (hDsrc l) (hD5 (F k) (F l) (hFinj k l hkl))
  have hγ₁ : ∀ k, IsPLHomeomorphOn (γ₁ k) (Icc 0 1) (D k ∩ C₁) := by
    intro k
    rw [← hinter (hDsrc k) hB₁src]
    exact (hg₁ k).1
  have hγ₂ : ∀ k, IsPLHomeomorphOn (γ₂ k) (Icc 0 1) (D k ∩ C₂) := by
    intro k
    rw [← hinter (hDsrc k) hB₂src]
    exact (hg₂ k).1
  have hDb : ∀ k, qD k '' stdSimplexBoundary 2 = D k ∩ C₁ ∪ D k ∩ C₂ := by
    intro k
    rw [← hqDb k, hDbM k, image_union, hinter (hDsrc k) hB₁src,
      hinter (hDsrc k) hB₂src]
  have hint : ∀ k, D k ∩ C₁ ∩ (D k ∩ C₂) = {chart (pin k), chart (pout k)} := by
    intro k
    rw [← hinter (hDsrc k) hB₁src, ← hinter (hDsrc k) hB₂src,
      ← hinter (inter_subset_left.trans (hDsrc k)) (inter_subset_left.trans (hDsrc k)),
      hintM k, image_pair]
  have hBV : ∀ x y x' y' : Ea, section34ClawBall V x y x' y' ⊆ ⋃ w, V w :=
    fun _ _ _ _ => iUnion₂_subset fun w _ => subset_iUnion V w
  have hDfrM : ∀ (s : Section34SimplexIndex 𝒦 3) {B : Set M₂}, B ⊆ ⋃ w, V w →
      tgtD s ∩ B ⊆ frontier B := by
    intro s B hB z hz
    have hzDb : z ∈ tgtDBd s := by
      rw [← hD3 s]
      exact ⟨hz.1, hB hz.2⟩
    exact ⟨subset_closure hz.2, fun hzi => (hD4 s hzDb).2 (interior_mono hB hzi)⟩
  have hDfr₁ : ∀ k, D k ∩ C₁ ⊆ frontier C₁ := by
    intro k
    rw [← hfr₁, ← hinter (hDsrc k) hB₁src]
    exact image_mono (hDfrM (F k) (hBV _ _ _ _))
  have hDfr₂ : ∀ k, D k ∩ C₂ ⊆ frontier C₂ := by
    intro k
    rw [← hfr₂, ← hinter (hDsrc k) hB₂src]
    exact image_mono (hDfrM (F k) (hBV _ _ _ _))
  have hout : ∀ k, D k ∩ DH k = {γ₁ k 1} := by
    intro k
    rw [← hinter (hDsrc k) (hEsrc k), hDj k, image_singleton, (hg₁ k).2.2]
  have hsub1 : ∀ k : Fin 4, k + 1 - 1 = k := fun k => add_sub_cancel_right k 1
  have hin : ∀ k, D (k + 1) ∩ DH k = {γ₁ (k + 1) 0} := by
    intro k
    rw [← hinter (hDsrc (k + 1)) (hEsrc k), (hg₁ (k + 1)).2.1]
    have hi := hDi (k + 1)
    rw [hsub1 k] at hi
    rw [hi, image_singleton]
  have hfar : ∀ k l, l ≠ k → l + 1 ≠ k → D k ∩ DH l = ∅ := by
    intro k l h1 h2
    have hl : l ≠ k - 1 := fun h => h2 (by rw [h, sub_add_cancel])
    rw [← hinter (hDsrc k) (hEsrc l), hDo k l hl h1, image_empty]
  have hbout : ∀ k, γ₁ k 1 ∈ rH k '' stdSimplexBoundary 2 := by
    intro k
    rw [(hg₁ k).2.2, ← hrHb k]
    exact mem_image_of_mem chart (hq k)
  have hbin : ∀ k, γ₁ (k + 1) 0 ∈ rH k '' stdSimplexBoundary 2 := by
    intro k
    rw [(hg₁ (k + 1)).2.1, ← hrHb k]
    have hi := hp (k + 1)
    rw [hsub1 k] at hi
    exact mem_image_of_mem chart hi
  exact exists_isPLBall_frontier_eq_of_four_disks hB₁ hB₂ hrH hHdisj h12 hH₁ hH₂ hHint
    hqD hDdisj hγ₁ hγ₂ hDb
    (fun k => by rw [(hg₁ k).2.1, (hg₁ k).2.2]; exact hint k)
    (fun k => by rw [(hg₂ k).2.1, (hg₂ k).2.2]; exact hint k)
    hDfr₁ hDfr₂ hout hin hfar hbout hbin

end DifferentialGeometry.Topology.PiecewiseLinear
