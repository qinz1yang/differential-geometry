/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualTiling

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactCutFrame.exists_boundaryTriangle_pair
    (hcut : Section34CompactCutFrame C K K' src srcBd) (e : Section34CompactEdgeIndex K K')
    (he : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space) :
    ∃ s₁ s₂ : Section34CompactSimplexIndex K 3, s₁ ≠ s₂ ∧
      convexHull ℝ (s₁.1 : Set E3) ⊆ frontier K.space ∧
      convexHull ℝ (s₂.1 : Set E3) ⊆ frontier K.space ∧
      Section34Incident e.1 s₁.1 ∧ Section34Incident e.1 s₂.1 ∧
      ∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space →
        Section34Incident e.1 s.1 → s = s₁ ∨ s = s₂ := by
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨-, hK, -, hman, hsub, -⟩ := id hcut
  let _ : Finite K.faces := hK.to_subtype
  let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hfr := frontier_space_eq_boundaryComplex_space (n := 2) hman
  have hne : e.1.Nonempty := Finset.card_pos.mp (by rw [e.2.2.1]; norm_num)
  have hm := centroid_mem_openSimplex hne
  have hmconv : e.1.centroid ℝ id ∈ convexHull ℝ (e.1 : Set E3) :=
    openSimplex_subset_convexHull e.1 hm
  have hmB : e.1.centroid ℝ id ∈ (boundaryComplex 3 K).space := by
    rw [← hfr]
    exact he hmconv
  obtain ⟨σ, hσ, hmσ⟩ := exists_face_mem_openSimplex K (boundaryComplex_space_subset 3 K hmB)
  have hσB : σ ∈ (boundaryComplex 3 K).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) hσ hmσ hmB
  have heσ : convexHull ℝ (e.1 : Set E3) ⊆ convexHull ℝ (σ : Set E3) :=
    hsub.convexHull_subset_of_mem_openSimplex hσ e.2.1 hm (openSimplex_subset_convexHull σ hmσ)
  have hσ2 : σ.card = 1 + 1 := by
    obtain ⟨σ', ⟨hσ', hσ'card⟩, hmσ'⟩ := mem_iUnion₂.mp (e.2.2.2 hmconv)
    have hle := Finset.card_le_card (face_subset_of_mem_openSimplex_of_mem_convexHull K hσ hσ'
      hmσ hmσ')
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hσ)
    by_contra hne2
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (by omega : σ.card = 1)
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp e.2.2.1
    have ha : a ∈ convexHull ℝ (({u} : Finset E3) : Set E3) :=
      heσ (subset_convexHull ℝ _ (by rw [heab]; simp))
    have hb : b ∈ convexHull ℝ (({u} : Finset E3) : Set E3) :=
      heσ (subset_convexHull ℝ _ (by rw [heab]; simp))
    rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at ha hb
    exact hab (ha.trans hb.symm)
  have hL := isCombinatorialManifold_boundaryComplex (n := 2) K hman
  obtain ⟨a, b, hab, hcof⟩ := hL.codimension_one_cofaces (boundaryComplex 3 K) hσB hσ2
  have haσ : a ∉ σ ∧ insert a σ ∈ (boundaryComplex 3 K).faces := by
    have h : a ∈ {w | w ∉ σ ∧ insert w σ ∈ (boundaryComplex (2 + 1) K).faces} := by
      rw [hcof]
      exact mem_insert a {b}
    exact h
  have hbσ : b ∉ σ ∧ insert b σ ∈ (boundaryComplex 3 K).faces := by
    have h : b ∈ {w | w ∉ σ ∧ insert w σ ∈ (boundaryComplex (2 + 1) K).faces} := by
      rw [hcof]
      exact mem_insert_of_mem a (mem_singleton b)
    exact h
  let s₁ : Section34CompactSimplexIndex K 3 := ⟨insert a σ, boundaryComplex_faces_subset 3 K haσ.2,
    by rw [Finset.card_insert_of_notMem haσ.1, hσ2]⟩
  let s₂ : Section34CompactSimplexIndex K 3 := ⟨insert b σ, boundaryComplex_faces_subset 3 K hbσ.2,
    by rw [Finset.card_insert_of_notMem hbσ.1, hσ2]⟩
  have hinc : ∀ x : E3, Section34Incident e.1 (insert x σ) := fun x z hz =>
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert x σ))
      (heσ (subset_convexHull ℝ _ hz))
  refine ⟨s₁, s₂, fun h => ?_, ?_, ?_, hinc a, hinc b, fun s hs hes => ?_⟩
  · have ha' : a ∈ insert b σ := by
      change a ∈ s₂.1
      rw [← h]
      exact Finset.mem_insert_self a σ
    exact hab ((Finset.mem_insert.mp ha').resolve_right haσ.1)
  · rw [hfr]
    exact (boundaryComplex 3 K).convexHull_subset_space haσ.2
  · rw [hfr]
    exact (boundaryComplex 3 K).convexHull_subset_space hbσ.2
  · have hσs : σ ⊆ s.1 := face_subset_of_mem_openSimplex_of_mem_convexHull K hσ s.2.1 hmσ
      (convexHull_min hes (convex_convexHull ℝ _) hmconv)
    have hsB : s.1 ∈ (boundaryComplex 3 K).faces := by
      apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) s.2.1
        (centroid_mem_openSimplex (K.nonempty_of_mem_faces s.2.1))
      rw [← hfr]
      exact hs (s.1.centroid_mem_convexHull (K.nonempty_of_mem_faces s.2.1))
    obtain ⟨x, hxσ, hxs⟩ := Finset.exists_eq_insert_iff.mpr ⟨hσs, by rw [hσ2, s.2.2]⟩
    have hx : x ∈ {w | w ∉ σ ∧ insert w σ ∈ (boundaryComplex (2 + 1) K).faces} :=
      ⟨hxσ, by rw [hxs]; exact hsB⟩
    rw [hcof] at hx
    rcases hx with hx | hx
    · refine Or.inl (Subtype.ext ?_)
      rw [← hxs, hx]
    · refine Or.inr (Subtype.ext ?_)
      rw [← hxs, mem_singleton_iff.mp hx]

theorem closure_sdiff_eq_of_arc_pair {X Y S U : Set E3} {p₁ p₂ : E3} {γY : ℝ → E3}
    (hγY : IsPLHomeomorphOn γY (Icc 0 1) Y) (hγY0 : γY 0 = p₁) (hγY1 : γY 1 = p₂)
    (hXY : X ∪ Y = S) (hXYi : X ∩ Y = {p₁, p₂}) (hXcl : closure (X \ {p₁, p₂}) = X)
    (hUc : IsClosed U) (hXU : X \ {p₁, p₂} ⊆ U) (hYU : Disjoint (Y \ {p₁, p₂}) U) :
    closure (S \ U) = Y := by
  have hXU' : X ⊆ U := by
    rw [← hXcl]
    exact closure_minimal hXU hUc
  have hpX : ({p₁, p₂} : Set E3) ⊆ X := by
    rw [← hXYi]
    exact inter_subset_left
  have heq : S \ U = Y \ {p₁, p₂} := by
    apply Subset.antisymm
    · rintro z ⟨hzS, hzU⟩
      rw [← hXY] at hzS
      rcases hzS with hzX | hzY
      · exact absurd (hXU' hzX) hzU
      · exact ⟨hzY, fun hzp => hzU (hXU' (hpX hzp))⟩
    · intro z hz
      refine ⟨?_, Set.disjoint_left.mp hYU hz⟩
      rw [← hXY]
      exact Or.inr hz.1
  rw [heq, ← hγY0, ← hγY1]
  exact hγY.closure_sdiff_endpoints zero_lt_one

theorem Section34CompactCutFrame.exists_residual_outerArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    (e : Section34CompactEdgeIndex K K')
    (he : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space) :
    ∃ δ : ℝ → E3, IsPLHomeomorphOn δ (Icc 0 1)
        (closure (section34CompactSplitDiskImage srcBd f₁ e \
          ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
            Rf t ∩ section34CompactSplitDiskImage src f₁ e)) ∧
      ({δ 0, δ 1} : Set E3) = ⋃ (p : Section34CompactMarkIndex K K')
        (_ : p.1.2 = e ∧ convexHull ℝ (p.1.1.1 : Set E3) ⊆ frontier K.space), tgtP p := by
  obtain ⟨-, hKfin, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hex⟩ := id hcut
  have _ := finite_section34CompactSimplexIndex hKfin 4
  obtain ⟨-, -, -, -, hD5, -⟩ := id hdisk
  have hmark := hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁ e
  have hS : IsPLSphere 1 (section34CompactSplitDiskImage srcBd f₁ e) :=
    hEcell.isPLSphere_one_of_two
  have hEbE : section34CompactSplitDiskImage srcBd f₁ e ⊆ section34CompactSplitDiskImage src f₁ e :=
    hEcell.boundary_subset
  have hEc : IsClosed (section34CompactSplitDiskImage src f₁ e) := hEcell.isCompact.isClosed
  have hUc : IsClosed (⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
      Rf t ∩ section34CompactSplitDiskImage src f₁ e) :=
    isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
      (hR t).isPolyhedron.isClosed.inter hEc
  have hUS : (⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
      Rf t ∩ section34CompactSplitDiskImage src f₁ e) ⊆ section34CompactSplitDiskImage srcBd f₁ e :=
    iUnion₂_subset fun t _ =>
      hcut.residual_inter_splitDiskImage_subset hf₁ (hR t) (hint t) (h7 t) e
  obtain ⟨s₁, s₂, hs12, hs1b, hs2b, hes1, hes2, hsuniq⟩ := hcut.exists_boundaryTriangle_pair e he
  obtain ⟨p₁, hp₁, hp₁b⟩ :=
    hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ s₁ e hes1
  obtain ⟨p₂, hp₂, hp₂b⟩ :=
    hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ s₂ e hes2
  have hp₁D : p₁ ∈ tgtD s₁ := (hp₁.symm.subset (mem_singleton p₁)).1
  have hp₂D : p₂ ∈ tgtD s₂ := (hp₂.symm.subset (mem_singleton p₂)).1
  have hp12 : p₁ ≠ p₂ := fun h => Set.disjoint_left.mp (hD5 s₁ s₂ hs12) hp₁D (by rw [h]; exact hp₂D)
  obtain ⟨t₁, hst₁⟩ := hex s₁
  have het₁ : Section34Incident e.1 t₁.1 := fun x hx =>
    convexHull_min hst₁ (convex_convexHull ℝ _) (hes1 hx)
  obtain ⟨γ₁, hγ₁, hγ₁b⟩ := hcut.exists_residualEdgeArc hf₁ hdisk (hR t₁) (hDR t₁) (hfr t₁)
    (hint t₁) (hio t₁) (h7 t₁) het₁
  have hmarkI : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident e.1 s.1 → ∀ x : E3,
      tgtD s ∩ section34CompactSplitDiskImage src f₁ e = {x} → x ∈ Rf t₁ →
      x ∈ ({γ₁ 0, γ₁ 1} : Set E3) := by
    intro s hes x hx hxR
    have hxD : x ∈ tgtD s := (hx.symm.subset (mem_singleton x)).1
    have hst : Section34Incident s.1 t₁.1 := by
      by_contra h
      have h0 : x ∈ Rf t₁ ∩ tgtD s := ⟨hxR, hxD⟩
      rw [h9 t₁ s h] at h0
      exact h0
    rw [hγ₁b]
    refine mem_iUnion₂.mpr ⟨⟨(s, e), hes⟩, ⟨rfl, hst⟩, (hmark _).subset ?_⟩
    change x ∈ tgtD s ∩ section34CompactSplitDiskImage src f₁ e
    rw [hx]
    exact mem_singleton x
  have hp₁I : p₁ ∈ ({γ₁ 0, γ₁ 1} : Set E3) :=
    hmarkI s₁ hes1 p₁ hp₁ ((hR t₁).isPolyhedron.isClosed.frontier_subset (hDR t₁ s₁ hst₁ hp₁D))
  have hI₁S : Rf t₁ ∩ section34CompactSplitDiskImage src f₁ e ⊆
      section34CompactSplitDiskImage srcBd f₁ e :=
    hcut.residual_inter_splitDiskImage_subset hf₁ (hR t₁) (hint t₁) (h7 t₁) e
  have hout : ∃ x ∈ section34CompactSplitDiskImage srcBd f₁ e,
      x ∉ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
    obtain ⟨δ, hδ, hδ0, hδ1, -, -⟩ := hS.exists_isPLHomeomorphOn_closure_sdiff hγ₁ hI₁S
    have hp₁cl : p₁ ∈ closure (section34CompactSplitDiskImage srcBd f₁ e \
        (Rf t₁ ∩ section34CompactSplitDiskImage src f₁ e)) := by
      rcases hp₁I with h | h
      · rw [h, ← hδ0]
        exact hδ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
      · rw [mem_singleton_iff.mp h, ← hδ1]
        exact hδ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
    have hFc : IsClosed (⋃ (t : Section34CompactSimplexIndex K 4) (_ : t ≠ t₁), Rf t) :=
      isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
        (hR t).isPolyhedron.isClosed
    have hp₁F : p₁ ∉ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : t ≠ t₁), Rf t := by
      intro h
      obtain ⟨t, htt, hp₁R⟩ := mem_iUnion₂.mp h
      have hs1t : ¬ Section34Incident s₁.1 t.1 := fun h' =>
        htt (hcut.tetra_eq_of_boundary_triangle s₁ hs1b h' hst₁)
      have h0 : p₁ ∈ Rf t ∩ tgtD s₁ := ⟨hp₁R, hp₁D⟩
      rw [h9 t s₁ hs1t] at h0
      exact h0
    obtain ⟨x, hxF, hxS, hxI⟩ := mem_closure_iff_nhds.mp hp₁cl _ (hFc.isOpen_compl.mem_nhds hp₁F)
    refine ⟨x, hxS, fun hxU => ?_⟩
    obtain ⟨t, -, hxR, hxE⟩ := mem_iUnion₂.mp hxU
    by_cases htt : t = t₁
    · rw [htt] at hxR
      exact hxI ⟨hxR, hxE⟩
    · exact hxF (mem_iUnion₂.mpr ⟨t, htt, hxR⟩)
  have hin : ∃ y ∈ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
      Rf t ∩ section34CompactSplitDiskImage src f₁ e, y ∉ ({p₁, p₂} : Set E3) := by
    have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hy : γ₁ (1 / 2) ∈ Rf t₁ ∩ section34CompactSplitDiskImage src f₁ e :=
      hγ₁.bijOn.mapsTo hhalf
    have hyend : γ₁ (1 / 2) ∉ ({γ₁ 0, γ₁ 1} : Set E3) := by
      rintro (h | h)
      · have := hγ₁.bijOn.injOn hhalf ⟨le_rfl, zero_le_one⟩ h
        norm_num at this
      · have := hγ₁.bijOn.injOn hhalf ⟨zero_le_one, le_rfl⟩ (mem_singleton_iff.mp h)
        norm_num at this
    refine ⟨γ₁ (1 / 2), mem_iUnion₂.mpr ⟨t₁, het₁, hy⟩, ?_⟩
    rintro (h | h)
    · exact hyend (by rw [h]; exact hp₁I)
    · rw [mem_singleton_iff] at h
      refine hyend ?_
      rw [h]
      exact hmarkI s₂ hes2 p₂ hp₂ (by rw [← h]; exact hy.1)
  obtain ⟨A, B, γA, γB, hγA, hγB, hγA0, hγA1, hγB0, hγB1, hAB, hABi⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp₁b hp₂b hp12
  have hAS : A ⊆ section34CompactSplitDiskImage srcBd f₁ e := by
    rw [← hAB]
    exact subset_union_left
  have hBS : B ⊆ section34CompactSplitDiskImage srcBd f₁ e := by
    rw [← hAB]
    exact subset_union_right
  have hAcl : closure (A \ {p₁, p₂}) = A := by
    rw [← hγA0, ← hγA1]
    exact hγA.closure_sdiff_endpoints zero_lt_one
  have hBcl : closure (B \ {p₁, p₂}) = B := by
    rw [← hγB0, ← hγB1]
    exact hγB.closure_sdiff_endpoints zero_lt_one
  have hAconn : IsConnected (A \ {p₁, p₂}) := by
    rw [← hγA0, ← hγA1]
    exact hγA.isConnected_sdiff_endpoints zero_lt_one
  have hBconn : IsConnected (B \ {p₁, p₂}) := by
    rw [← hγB0, ← hγB1]
    exact hγB.isConnected_sdiff_endpoints zero_lt_one
  have hopen : ∀ z ∈ section34CompactSplitDiskImage srcBd f₁ e,
      z ∈ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34CompactSplitDiskImage src f₁ e →
      z ∉ ({p₁, p₂} : Set E3) →
      ∃ V ∈ 𝓝 z, V ∩ section34CompactSplitDiskImage srcBd f₁ e ⊆
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
    intro z hzb hzU hzp
    obtain ⟨t, het, hzR, hzE⟩ := mem_iUnion₂.mp hzU
    obtain ⟨w, w', hww', hew, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    have hwe : w.1 ⊆ e.1 := by
      have h : (w.1 : Set E3) ⊆ e.1 := by
        rw [hew]
        exact subset_union_left
      exact Finset.coe_subset.mp h
    have hw'e : w'.1 ⊆ e.1 := by
      have h : (w'.1 : Set E3) ⊆ e.1 := by
        rw [hew]
        exact subset_union_right
      exact Finset.coe_subset.mp h
    have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
      (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
    have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
    have hEbW : section34CompactSplitDiskImage srcBd f₁ e ⊆
        frontier (section34CompactVertexBallImage src f₁ w ∪
          section34CompactVertexBallImage src f₁ w') :=
      boundary_subset_frontier_union_of_inter_eq (hVball w) (hVball w') hEcell hinter
        (hcut.splitDiskImage_subset_frontier hf₁ hwe)
    obtain ⟨V, hV, hVR⟩ := hcut.exists_mem_nhds_frontier_pair_subset_iUnion_residual hf₁ hdisk
      hR hDR hfr hint hio h7 h9 hww' hwe hw'e hzb (fun s hes hzs hsb => by
        rcases hsuniq s hsb hes with h | h
        · rw [h] at hzs
          have hz : z ∈ tgtD s₁ ∩ section34CompactSplitDiskImage src f₁ e := ⟨hzs, hzE⟩
          rw [hp₁] at hz
          exact hzp (Or.inl hz)
        · rw [h] at hzs
          have hz : z ∈ tgtD s₂ ∩ section34CompactSplitDiskImage src f₁ e := ⟨hzs, hzE⟩
          rw [hp₂] at hz
          exact hzp (Or.inr hz)) het hzR
    refine ⟨V, hV, fun q hq => ?_⟩
    obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp (hVR ⟨hq.1, hEbW hq.2⟩)
    exact mem_iUnion₂.mpr ⟨t', het', hqR, hEbE hq.2⟩
  have hloc : ∀ (Z : Set E3), Z ⊆ section34CompactSplitDiskImage srcBd f₁ e →
      ∀ y ∈ Z \ {p₁, p₂},
      y ∈ ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
        Rf t ∩ section34CompactSplitDiskImage src f₁ e →
      ∃ V ∈ 𝓝 y, V ∩ (Z \ {p₁, p₂}) ⊆
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
    intro Z hZ y hy hyU
    obtain ⟨V, hV, hVU⟩ := hopen y (hZ hy.1) hyU hy.2
    exact ⟨V, hV, fun q hq => hVU ⟨hq.1, hZ hq.2.1⟩⟩
  have hAU := subset_or_disjoint_of_isPreconnected_of_locally_subset hAconn.isPreconnected hUc
    (hloc A hAS)
  have hBU := subset_or_disjoint_of_isPreconnected_of_locally_subset hBconn.isPreconnected hUc
    (hloc B hBS)
  have hBd : ({p₁, p₂} : Set E3) = ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = e ∧ convexHull ℝ (p.1.1.1 : Set E3) ⊆ frontier K.space), tgtP p := by
    apply Subset.antisymm
    · rintro y (hy | hy)
      · refine mem_iUnion₂.mpr ⟨⟨(s₁, e), hes1⟩, ⟨rfl, hs1b⟩, (hmark _).subset ?_⟩
        change y ∈ tgtD s₁ ∩ section34CompactSplitDiskImage src f₁ e
        rw [hp₁, hy]
        exact mem_singleton p₁
      · refine mem_iUnion₂.mpr ⟨⟨(s₂, e), hes2⟩, ⟨rfl, hs2b⟩, (hmark _).subset ?_⟩
        change y ∈ tgtD s₂ ∩ section34CompactSplitDiskImage src f₁ e
        rw [hp₂, mem_singleton_iff.mp hy]
        exact mem_singleton p₂
    · intro y hy
      obtain ⟨p, ⟨hpe, hpb⟩, hyp⟩ := mem_iUnion₂.mp hy
      rw [← hmark] at hyp
      have hes : Section34Incident e.1 p.1.1.1 := by
        rw [← hpe]
        exact p.2
      rw [hpe] at hyp
      rcases hsuniq p.1.1 hpb hes with h | h
      · rw [h, hp₁] at hyp
        exact Or.inl hyp
      · rw [h, hp₂] at hyp
        exact Or.inr hyp
  rcases hAU with hAU | hAU <;> rcases hBU with hBU | hBU
  · exfalso
    obtain ⟨x, hxS, hxU⟩ := hout
    apply hxU
    rw [← hAB] at hxS
    rcases hxS with hx | hx
    · rw [← hAcl] at hx
      exact closure_minimal hAU hUc hx
    · rw [← hBcl] at hx
      exact closure_minimal hBU hUc hx
  · refine ⟨γB, ?_, by rw [hγB0, hγB1]; exact hBd⟩
    rw [closure_sdiff_eq_of_arc_pair hγB hγB0 hγB1 hAB hABi hAcl hUc hAU hBU]
    exact hγB
  · refine ⟨γA, ?_, by rw [hγA0, hγA1]; exact hBd⟩
    rw [closure_sdiff_eq_of_arc_pair hγA hγA0 hγA1 (by rw [union_comm]; exact hAB)
      (by rw [inter_comm]; exact hABi) hBcl hUc hBU hAU]
    exact hγA
  · exfalso
    obtain ⟨y, hyU, hyp⟩ := hin
    have hyS := hUS hyU
    rw [← hAB] at hyS
    rcases hyS with hy | hy
    · exact Set.disjoint_left.mp hAU ⟨hy, hyp⟩ hyU
    · exact Set.disjoint_left.mp hBU ⟨hy, hyp⟩ hyU

end DifferentialGeometry.Topology.PiecewiseLinear
