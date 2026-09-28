/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem section34CompactSimplexIndex_eq_of_incident {t : Finset E3} (ht : t ∈ K.faces)
    {a b c d : E3} (htabcd : t = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : Section34CompactSimplexIndex K 3)
    (hs : Section34Incident s.1 t) :
    s.1 = {a, c, d} ∨ s.1 = {a, b, c} ∨ s.1 = {b, c, d} ∨ s.1 = {a, b, d} := by
  classical
  have hsub : s.1 ⊆ t := by
    intro x hx
    have hxK : ({x} : Finset E3) ∈ K.faces :=
      K.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
    have h := K.inter_subset_convexHull hxK ht
      ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self x)),
        hs (Finset.mem_coe.mpr hx)⟩
    rw [← Finset.coe_inter] at h
    by_contra hxt
    rw [Finset.singleton_inter_of_notMem hxt, Finset.coe_empty, convexHull_empty] at h
    exact h
  rw [htabcd] at hsub
  have hcard3 : ∀ {x y z : E3}, x ≠ y → x ≠ z → y ≠ z → ({x, y, z} : Finset E3).card = 3 :=
    fun hxy hxz hyz => Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩
  have hsub3 : ∀ {x y z : E3}, s.1 ⊆ {x, y, z} → x ≠ y → x ≠ z → y ≠ z → s.1 = {x, y, z} :=
    fun h hxy hxz hyz => Finset.eq_of_subset_of_card_le h (by rw [hcard3 hxy hxz hyz, s.2.2])
  have hmiss : ∀ x ∈ s.1, x = a ∨ x = b ∨ x = c ∨ x = d := fun x hx => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hx
  by_cases hbs : b ∈ s.1
  · by_cases has : a ∈ s.1
    · by_cases hcs : c ∈ s.1
      · refine Or.inr (Or.inl (Finset.eq_of_subset_of_card_le ?_ ?_).symm)
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact has
          · exact hbs
          · exact hcs
        · rw [s.2.2, hcard3 hab hac hbc]
      · refine Or.inr (Or.inr (Or.inr (hsub3 (fun x hx => ?_) hab had hbd)))
        rcases hmiss x hx with rfl | rfl | rfl | rfl
        · simp
        · simp
        · exact absurd hx hcs
        · simp
    · refine Or.inr (Or.inr (Or.inl (hsub3 (fun x hx => ?_) hbc hbd hcd)))
      rcases hmiss x hx with rfl | rfl | rfl | rfl
      · exact absurd hx has
      · simp
      · simp
      · simp
  · refine Or.inl (hsub3 (fun x hx => ?_) hac had hcd)
    rcases hmiss x hx with rfl | rfl | rfl | rfl
    · simp
    · exact absurd hx hbs
    · simp
    · simp

theorem exists_mem_frontier_of_mem_boundary_disk {B P R : Set E3} (hB : IsPLBall 3 B)
    (hRc : IsClosed R) {q : (Fin 3 → ℝ) → E3} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    (hPB : P ⊆ frontier B) (hPR : P ⊆ frontier R) (hRB : frontier R ∩ B ⊆ P)
    (hint : Disjoint (interior R) B) {y : E3} (hy : y ∈ q '' stdSimplexBoundary 2)
    {U : Set E3} (hU : U ∈ 𝓝 y) :
    (∃ z ∈ U, z ∈ frontier B ∧ z ∈ R ∧ z ∉ q '' stdSimplexBoundary 2) ∧
      ∃ z ∈ U, z ∈ frontier B ∧ z ∉ R := by
  have hBc : IsClosed B := hB.isPolyhedron.isClosed
  have hyP : y ∈ P := by
    rw [← hq.image_eq]
    exact image_mono (fun x hx => hx.1) hy
  constructor
  · have hcl : y ∈ closure (P \ q '' stdSimplexBoundary 2) := by
      rw [hq.closure_sdiff_image_stdSimplexBoundary (n := 1)]
      exact hyP
    obtain ⟨z, hzU, hzP, hzb⟩ := mem_closure_iff_nhds.mp hcl U hU
    exact ⟨z, hzU, hPB hzP, hRc.frontier_subset (hPR hzP), hzb⟩
  · have hcl : y ∈ closure (frontier B \ P) := by
      have h := hB.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hPB
      rw [← h] at hy
      exact hy.2
    obtain ⟨z, hzU, hzB, hzP⟩ := mem_closure_iff_nhds.mp hcl U hU
    refine ⟨z, hzU, hzB, fun hzR => ?_⟩
    have hzB' : z ∈ B := hBc.frontier_subset hzB
    by_cases hzi : z ∈ interior R
    · exact Set.disjoint_left.mp hint hzi hzB'
    · exact hzP (hRB ⟨⟨subset_closure hzR, hzi⟩, hzB'⟩)

theorem Section34CompactCutFrame.exists_residualBall
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (t : Section34CompactSimplexIndex K 4) :
    ∃ R : Set E3, IsPLBall 3 R ∧
      (∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
        tgtD s ⊆ frontier R) ∧
      frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
          section34CompactVertexBallImage src f₁ w) ∪
        ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s ∧
      Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
        (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w) ∧
      ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
        (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
        ∀ U ∈ 𝓝 y,
          (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
            z ∉ tgtD a.1.1) ∧
          ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, htabcd⟩ := Finset.card_eq_four.mp t.2.2
  have ht := t.2.1
  have ha : a ∈ t.1 := by rw [htabcd]; simp
  have hb : b ∈ t.1 := by rw [htabcd]; simp
  have hc : c ∈ t.1 := by rw [htabcd]; simp
  have hd : d ∈ t.1 := by rw [htabcd]; simp
  have hpK : ∀ {u v : E3}, u ∈ t.1 → v ∈ t.1 → ({u, v} : Finset E3) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  have htri : ∀ {x y z : E3}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → x ≠ y → x ≠ z → y ≠ z →
      ∃ s : Section34CompactSimplexIndex K 3, s.1 = {x, y, z} := by
    intro x y z hx hy hz hxy hxz hyz
    refine ⟨⟨{x, y, z}, K.down_closed ht ?_ (Finset.insert_nonempty _ _),
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
  obtain ⟨R, A, Ω, hR, hRf, hAB₁, hΩB₂, ⟨qA, hqA, hqAb⟩, ⟨qΩ, hqΩ, hqΩb⟩, hΩB₁, hAB₂, hdisj⟩ :=
    hcut.exists_isPLBall_of_tetra hf₁ hdisk ht htabcd hab hac had hbc hbd hcd hea₁ hea₂ hea
      heb₁ heb₂ heb hec₁ hec₂ hec hed₁ hed₂ hed hsacd hsabc hsbcd hsabd
  set V := section34CompactVertexBallImage src f₁
  set B₁ := section34CompactClawBall V a b c d
  set B₂ := section34CompactClawBall V d c a b
  have hB₁ : IsPLBall 3 B₁ :=
    hcut.isPLBall_section34CompactClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc hcd
  have hB₂ : IsPLBall 3 B₂ :=
    hcut.isPLBall_section34CompactClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
      hbd.symm hac.symm hab
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  obtain ⟨-, -, hK'fin, -⟩ := id hcut
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  obtain ⟨hD1, -, -, -, -, -, hA7, -⟩ := id hdisk
  have hfaces : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      s = sacd ∨ s = sabc ∨ s = sbcd ∨ s = sabd := by
    intro s hs
    rcases section34CompactSimplexIndex_eq_of_incident ht htabcd hab hac had hbc hbd hcd s hs with
      h | h | h | h
    · exact Or.inl (Subtype.ext (h.trans hsacd.symm))
    · exact Or.inr (Or.inl (Subtype.ext (h.trans hsabc.symm)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (h.trans hsbcd.symm))))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (h.trans hsabd.symm))))
  have hsegt : ∀ {u v : E3}, u ∈ t.1 → v ∈ t.1 → segment ℝ u v ⊆ convexHull ℝ (t.1 : Set E3) :=
    fun hu hv => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu)
      (subset_convexHull ℝ _ hv)
  have hFinc : ∀ {s : Section34CompactSimplexIndex K 3} {x y z : E3}, s.1 = {x, y, z} →
      x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → Section34Incident s.1 t.1 := by
    intro s x y z hs hx hy hz u hu
    rw [hs] at hu
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact subset_convexHull ℝ _ hx
    · exact subset_convexHull ℝ _ hy
    · exact subset_convexHull ℝ _ hz
  have hpinc : ∀ {w : Section34CompactVertexIndex K K'} {p : E3}, w.1 = {p} →
      p ∈ convexHull ℝ (t.1 : Set E3) → Section34Incident w.1 t.1 := by
    intro w p hw hp z hz
    rw [hw, Finset.coe_singleton] at hz
    rw [mem_singleton_iff.mp hz]
    exact hp
  have hB₁inc : B₁ ⊆ ⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
      V w := by
    intro z hz
    obtain ⟨w, ⟨p, hw, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨w, hpinc hw ?_, hzw⟩
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt ha hb h
    · exact hsegt ha hc h
    · exact hsegt hb hd h
  have hB₂inc : B₂ ⊆ ⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
      V w := by
    intro z hz
    obtain ⟨w, ⟨p, hw, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨w, hpinc hw ?_, hzw⟩
    rcases hp with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hsegt hd hc h
    · exact hsegt hd ha h
    · exact hsegt hc hb h
  have hDall : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ∩ B₁ ⊆ qA '' stdSimplexBoundary 2 ∧ tgtD s ∩ B₂ ⊆ qΩ '' stdSimplexBoundary 2 := by
    intro s hs
    rcases hfaces s hs with rfl | rfl | rfl | rfl
    · exact ⟨hqAb 0, hqΩb 0⟩
    · exact ⟨hqAb 1, hqΩb 1⟩
    · exact ⟨hqAb 2, hqΩb 2⟩
    · exact ⟨hqAb 3, hqΩb 3⟩
  have hbd : ∀ {P : Set E3} {q : (Fin 3 → ℝ) → E3},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P → q '' stdSimplexBoundary 2 ⊆ P :=
    fun hq => by
      rw [← hq.image_eq]
      exact image_mono fun x hx => hx.1
  have hiacd := hFinc hsacd ha hc hd
  have hiabc := hFinc hsabc ha hb hc
  have hibcd := hFinc hsbcd hb hc hd
  have hiabd := hFinc hsabd ha hb hd
  have hDface : ∀ {z : E3}, z ∈ tgtD sacd ∪ tgtD sabc ∪ tgtD sbcd ∪ tgtD sabd →
      ∃ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 ∧ z ∈ tgtD s := by
    rintro z (((h | h) | h) | h)
    · exact ⟨sacd, hiacd, h⟩
    · exact ⟨sabc, hiabc, h⟩
    · exact ⟨sbcd, hibcd, h⟩
    · exact ⟨sabd, hiabd, h⟩
  have hAR : A ⊆ frontier R := by
    rw [hRf]
    exact subset_union_left.trans subset_union_left
  have hΩR : Ω ⊆ frontier R := by
    rw [hRf]
    exact subset_union_right
  have hRB₁ : frontier R ∩ B₁ ⊆ A := by
    rw [hRf]
    rintro z ⟨(hzA | hzD) | hzΩ, hzB⟩
    · exact hzA
    · obtain ⟨s, hs, hzs⟩ := hDface hzD
      exact hbd hqA ((hDall s hs).1 ⟨hzs, hzB⟩)
    · exact hΩB₁ ⟨hzΩ, hzB⟩
  have hRB₂ : frontier R ∩ B₂ ⊆ Ω := by
    rw [hRf]
    rintro z ⟨(hzA | hzD) | hzΩ, hzB⟩
    · exact hAB₂ ⟨hzA, hzB⟩
    · obtain ⟨s, hs, hzs⟩ := hDface hzD
      exact hbd hqΩ ((hDall s hs).2 ⟨hzs, hzB⟩)
    · exact hzΩ
  refine ⟨R, hR, fun s hs => ?_, ?_, ?_, ?_⟩
  · rw [hRf]
    intro z hz
    rcases hfaces s hs with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl hz))))
    · exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr hz))))
    · exact Or.inl (Or.inr (Or.inl (Or.inr hz)))
    · exact Or.inl (Or.inr (Or.inr hz))
  · rw [hRf]
    rintro z ((hzA | hzD) | hzΩ)
    · exact Or.inl (hB₁inc (hB₁.isPolyhedron.isClosed.frontier_subset (hAB₁ hzA)))
    · obtain ⟨s, hs, hzs⟩ := hDface hzD
      exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hzs⟩)
    · exact Or.inl (hB₂inc (hB₂.isPolyhedron.isClosed.frontier_subset (hΩB₂ hzΩ)))
  · refine Set.disjoint_left.mpr fun z hz hzV => ?_
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp hdisj hz (vertexBallImage_subset_clawBall_union ht htabcd hw hzw)
  · intro arc hs y hy hyE U hU
    have hws : Section34Incident arc.1.2.1 arc.1.1.1 := arc.2
    have hwt : Section34Incident arc.1.2.1 t.1 := fun z hz =>
      convexHull_min hs (convex_convexHull ℝ _) (hws hz)
    have hyDV : y ∈ tgtDBd arc.1.1 ∩ V arc.1.2 := by
      rw [hA7 arc]
      exact hy
    have hyD : y ∈ tgtD arc.1.1 := (hD1 arc.1.1).boundary_subset hyDV.1
    have hVc : ∀ u, IsClosed (V u) := fun u =>
      (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
    have hO : IsOpen (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ arc.1.2), V u)ᶜ :=
      (isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ => hVc u).isOpen_compl
    have hyO : y ∈ (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ arc.1.2), V u)ᶜ := by
      intro hyu
      obtain ⟨u, hu, hyu'⟩ := mem_iUnion₂.mp hyu
      obtain ⟨e, he⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ (Ne.symm hu) hyDV.2 hyu'
      exact hyE e he
    have hU' := Filter.inter_mem hU (hO.mem_nhds hyO)
    have hfrV : ∀ {B : Set E3} {z : E3}, IsClosed B → (∀ z ∈ B, ∃ u, z ∈ V u) →
        V arc.1.2 ⊆ B → z ∈ frontier B →
        z ∈ (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ arc.1.2), V u)ᶜ →
        z ∈ frontier (V arc.1.2) := by
      intro B z hBc hcov hVB hzB hzO
      obtain ⟨u, hzu⟩ := hcov z (hBc.frontier_subset hzB)
      by_cases huw : u = arc.1.2
      · rw [huw] at hzu
        exact ⟨subset_closure hzu, fun hzi => hzB.2 (interior_mono hVB hzi)⟩
      · exact absurd (mem_iUnion₂.mpr ⟨u, huw, hzu⟩) hzO
    have hcov₁ : ∀ z ∈ B₁, ∃ u, z ∈ V u := fun z hz => by
      obtain ⟨u, -, hzu⟩ := mem_iUnion₂.mp hz
      exact ⟨u, hzu⟩
    have hcov₂ : ∀ z ∈ B₂, ∃ u, z ∈ V u := fun z hz => by
      obtain ⟨u, -, hzu⟩ := mem_iUnion₂.mp hz
      exact ⟨u, hzu⟩
    have hB₁c : IsClosed B₁ := hB₁.isPolyhedron.isClosed
    have hB₂c : IsClosed B₂ := hB₂.isPolyhedron.isClosed
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp arc.1.2.2.2.1
    have hpw : p ∈ (arc.1.2.1 : Set E3) := by
      rw [hp]
      exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
    obtain ⟨x, hx, y', hy', hpxy⟩ := exists_mem_segment_of_mem_convexHull_graphSkeleton ht
      (hwt hpw) (arc.1.2.2.2.2 (subset_convexHull ℝ _ hpw))
    rcases mem_claw_or_mem_claw_of_mem_segment htabcd hx hy' hpxy with hcl | hcl
    · have hVB : V arc.1.2 ⊆ B₁ := fun z hz => mem_iUnion₂.mpr ⟨arc.1.2, ⟨p, hp, hcl⟩, hz⟩
      have hyq : y ∈ qA '' stdSimplexBoundary 2 := (hDall arc.1.1 hs).1 ⟨hyD, hVB hyDV.2⟩
      obtain ⟨⟨z, hzU, hzB, hzR, hzq⟩, ⟨z', hz'U, hz'B, hz'R⟩⟩ :=
        exists_mem_frontier_of_mem_boundary_disk hB₁ hRc hqA hAB₁ hAR hRB₁
          (hdisj.mono_right subset_union_left) hyq hU'
      refine ⟨⟨z, hzU.1, hfrV hB₁c hcov₁ hVB hzB hzU.2, hzR, fun hzD => hzq ?_⟩,
        ⟨z', hz'U.1, hfrV hB₁c hcov₁ hVB hz'B hz'U.2, hz'R⟩⟩
      exact (hDall arc.1.1 hs).1 ⟨hzD, hB₁c.frontier_subset hzB⟩
    · have hVB : V arc.1.2 ⊆ B₂ := fun z hz => mem_iUnion₂.mpr ⟨arc.1.2, ⟨p, hp, hcl⟩, hz⟩
      have hyq : y ∈ qΩ '' stdSimplexBoundary 2 := (hDall arc.1.1 hs).2 ⟨hyD, hVB hyDV.2⟩
      obtain ⟨⟨z, hzU, hzB, hzR, hzq⟩, ⟨z', hz'U, hz'B, hz'R⟩⟩ :=
        exists_mem_frontier_of_mem_boundary_disk hB₂ hRc hqΩ hΩB₂ hΩR hRB₂
          (hdisj.mono_right subset_union_right) hyq hU'
      refine ⟨⟨z, hzU.1, hfrV hB₂c hcov₂ hVB hzB hzU.2, hzR, fun hzD => hzq ?_⟩,
        ⟨z', hz'U.1, hfrV hB₂c hcov₂ hVB hz'B hz'U.2, hz'R⟩⟩
      exact (hDall arc.1.1 hs).2 ⟨hzD, hB₂c.frontier_subset hzB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
