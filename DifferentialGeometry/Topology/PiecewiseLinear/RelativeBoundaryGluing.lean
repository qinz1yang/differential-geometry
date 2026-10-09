/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereGluing
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink
import DifferentialGeometry.Topology.PiecewiseLinear.CellAttachment
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem boundaryComplex_space_eq_of_isPLBall_of_subset {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall n K.space) (hL : IsPLBall n L.space)
    (hsub : (boundaryComplex n K).space ⊆ (boundaryComplex n L).space) :
    (boundaryComplex n K).space = (boundaryComplex n L).space := by
  cases n with
  | zero =>
    have hempty (A : Geometry.SimplicialComplex ℝ E) : (boundaryComplex 0 A).space = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨s, ⟨-, t, ht, -, hcard, -⟩, -⟩ := (boundaryComplex 0 A).mem_space_iff.mp hx
      have := Finset.card_pos.mpr (A.nonempty_of_mem_faces ht)
      omega
    rw [hempty K, hempty L]
  | succ n =>
    have hBK := isPLSphere_boundaryComplex_space_of_isPLBall K hK
    have hBL := isPLSphere_boundaryComplex_space_of_isPLBall L hL
    cases n with
    | zero =>
      obtain ⟨a, b, hab, hAB⟩ := isPLSphere_zero_iff.mp hBK
      obtain ⟨c, d, -, hCD⟩ := isPLSphere_zero_iff.mp hBL
      rw [hAB, hCD] at hsub ⊢
      have ha := hsub (mem_insert a {b})
      have hb := hsub (mem_insert_of_mem a (mem_singleton b))
      simp only [mem_insert_iff, mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · rfl
      · exact pair_comm _ _
      · exact (hab rfl).elim
    | succ n => exact eq_of_subset_of_isPLSphere hBK hBL hsub

open Classical in
private theorem not_mem_boundaryComplex_unionComplex_of_boundary_mem_nhdsWithin {n : ℕ}
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (h : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hU : IsCombinatorialManifoldWithBoundary (n + 1) (unionComplex K L h))
    (hIK : K.space ∩ L.space ⊆ (boundaryComplex (n + 1) K).space)
    (hIL : K.space ∩ L.space ⊆ (boundaryComplex (n + 1) L).space)
    {x : E} (hxL : {x} ∈ (boundaryComplex (n + 1) L).faces)
    (hnhds : K.space ∈ 𝓝[(boundaryComplex (n + 1) L).space] x) :
    x ∉ (boundaryComplex (n + 1) (unionComplex K L h)).space := by
  classical
  let I := restrict K L.space
  let KL := SimplicialComplex.geometricLink K {x}
  let LL := SimplicialComplex.geometricLink L {x}
  let _ : Finite KL.faces :=
    (Set.toFinite K.faces |>.subset (geometricLink_faces_subset K {x})).to_subtype
  let _ : Finite LL.faces :=
    (Set.toFinite L.faces |>.subset (geometricLink_faces_subset L {x})).to_subtype
  let _ : Finite (unionComplex K L h).faces :=
    (unionComplex_faces_finite K L h (Set.toFinite K.faces) (Set.toFinite L.faces)).to_subtype
  have hIKU : K.faces ⊆ (unionComplex K L h).faces := fun _ hs => Or.inl hs
  have hILU : L.faces ⊆ (unionComplex K L h).faces := fun _ hs => Or.inr hs
  have hIspace : I.space = K.space ∩ L.space :=
    restrict_space_eq_inter_of_faces_subset (unionComplex K L h) K L hIKU hILU
  have hIfaces {s : Finset E} : s ∈ I.faces ↔ s ∈ K.faces ∧ s ∈ L.faces :=
    mem_restrict_faces_iff_of_faces_subset (unionComplex K L h) K L hIKU hILU
  have hxLb : x ∈ (boundaryComplex (n + 1) L).space :=
    (boundaryComplex (n + 1) L).subset_space hxL (Finset.mem_singleton_self x)
  have hxK : x ∈ K.space := mem_of_mem_nhdsWithin hxLb hnhds
  have hKface : {x} ∈ K.faces := by
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
    have hxLface := boundaryComplex_faces_subset (n + 1) L hxL
    have hxinter := h s hs {x} hxLface ⟨hxs, by simp⟩
    have hxmem : x ∈ s := by
      by_contra hn
      have he : (s : Set E) ∩ (({x} : Finset E) : Set E) = ∅ := by simp [hn]
      rw [he, convexHull_empty] at hxinter
      exact hxinter
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hxmem) (Finset.singleton_nonempty x)
  have hIx : {x} ∈ I.faces := hIfaces.mpr
    ⟨hKface, boundaryComplex_faces_subset (n + 1) L hxL⟩
  have hface (A : Geometry.SimplicialComplex ℝ E)
      (hIA : I.faces ⊆ A.faces)
      (hi : I.space ⊆ (boundaryComplex (n + 1) A).space) :
      I.faces ⊆ (boundaryComplex (n + 1) A).faces := by
    intro s hs
    have hp := centroid_mem_openSimplex_of_mem_faces A s (hIA hs)
    exact mem_faces_of_mem_openSimplex_of_mem_space
      (boundaryComplex_faces_subset (n + 1) A) (hIA hs) hp
      (hi (I.convexHull_subset_space hs (openSimplex_subset_convexHull s hp)))
  have hIKface : I.faces ⊆ (boundaryComplex (n + 1) K).faces :=
    hface K (fun _ hs => (hIfaces.mp hs).1) (by rw [hIspace]; exact hIK)
  have hILface : I.faces ⊆ (boundaryComplex (n + 1) L).faces :=
    hface L (fun _ hs => (hIfaces.mp hs).2) (by rw [hIspace]; exact hIL)
  have hKball : IsPLBall n KL.space := by
    simpa [KL] using ((hK.mem_boundaryComplex_faces_iff K).mp (hIKface hIx)).2.2
  have hLball : IsPLBall n LL.space := by
    simpa [LL] using ((hL.mem_boundaryComplex_faces_iff L).mp hxL).2.2
  have hlinkCompat : ∀ s ∈ KL.faces, ∀ t ∈ LL.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact h s (geometricLink_faces_subset K {x} hs) t (geometricLink_faces_subset L {x} ht)
  have hinter : KL.space ∩ LL.space = (SimplicialComplex.geometricLink I {x}).space := by
    rw [geometricLink_restrict_space_of_faces_subset (unionComplex K L h) K L hIKU hILU]
    exact (restrict_space_eq_inter_of_faces_subset
      (SimplicialComplex.geometricLink (unionComplex K L h) {x}) KL LL
      (fun _ hs => ⟨hs.1, hs.2.1, Or.inl hs.2.2⟩)
      (fun _ hs => ⟨hs.1, hs.2.1, Or.inr hs.2.2⟩)).symm
  have hlinkSub (A : Geometry.SimplicialComplex ℝ E)
      (hIA : I.faces ⊆ (boundaryComplex (n + 1) A).faces) :
      (SimplicialComplex.geometricLink I {x}).space ⊆
        (boundaryComplex n (SimplicialComplex.geometricLink A {x})).space := by
    rw [← geometricLink_boundaryComplex]
    exact space_mono_of_faces_subset fun _ hs => ⟨hs.1, hs.2.1, hIA hs.2.2⟩
  have hILnhds : I.space ∈ 𝓝[(boundaryComplex (n + 1) L).space] x := by
    rw [hIspace]
    exact Filter.inter_mem hnhds
      (Filter.mem_of_superset self_mem_nhdsWithin (boundaryComplex_space_subset (n + 1) L))
  have hlinkEq := geometricLink_eq_of_space_mem_nhdsWithin hILface hILnhds
  have hmeetL : KL.space ∩ LL.space = (boundaryComplex n LL).space := by
    rw [hinter, hlinkEq, geometricLink_boundaryComplex]
  have hboundSub : (boundaryComplex n LL).space ⊆ (boundaryComplex n KL).space := by
    rw [← hmeetL, hinter]
    exact hlinkSub K hIKface
  have hmeetK : KL.space ∩ LL.space = (boundaryComplex n KL).space :=
    hmeetL.trans (boundaryComplex_space_eq_of_isPLBall_of_subset LL KL hLball hKball hboundSub)
  have hS : IsPLSphere n (SimplicialComplex.geometricLink (unionComplex K L h) {x}).space := by
    have heq : SimplicialComplex.geometricLink (unionComplex K L h) {x} =
        unionComplex KL LL hlinkCompat := by
      ext s
      simp only [mem_geometricLink_faces_iff, mem_unionComplex_faces_iff, KL, LL]
      tauto
    rw [heq, unionComplex_space]
    exact isPLSphere_union_of_isPLBall KL LL hKball hLball hmeetK hmeetL
  intro hxU
  have hball := (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
    (unionComplex K L h) (unionComplex K L h) hU (IsSubdivision.refl _)
    (show {x} ∈ (unionComplex K L h).faces from Or.inl hKface)).mpr hxU
  exact hball.not_isPLSphere hS

open Classical in
theorem not_mem_boundaryComplex_of_boundary_mem_nhdsWithin {n : ℕ}
    (K L N : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite N.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hN : IsCombinatorialManifoldWithBoundary (n + 1) N)
    (hNspace : N.space = K.space ∪ L.space)
    (hIK : K.space ∩ L.space ⊆ (boundaryComplex (n + 1) K).space)
    (hIL : K.space ∩ L.space ⊆ (boundaryComplex (n + 1) L).space)
    {x : E} (hxL : x ∈ (boundaryComplex (n + 1) L).space)
    (hnhds : K.space ∈ 𝓝[(boundaryComplex (n + 1) L).space] x) :
    x ∉ (boundaryComplex (n + 1) N).space := by
  classical
  have hKN : K.space ⊆ N.space := hNspace.symm ▸ subset_union_left
  have hLN : L.space ⊆ N.space := hNspace.symm ▸ subset_union_right
  have hxN := hLN (boundaryComplex_space_subset (n + 1) L hxL)
  obtain ⟨T₀, hT₀, hT₀fin, hxT₀⟩ := exists_isSubdivision_singleton_mem N hxN
  let _ : Finite T₀.faces := hT₀fin.to_subtype
  obtain ⟨T₁, hT₁, hT₁fin, hT₁K⟩ := exists_isSubdivision_restrict_isSubdivision T₀ K
    (hT₀.space_eq.symm ▸ hKN)
  let _ : Finite T₁.faces := hT₁fin.to_subtype
  obtain ⟨T₂, hT₂, hT₂fin, hT₂L⟩ := exists_isSubdivision_restrict_isSubdivision T₁ L
    ((hT₁.trans hT₀).space_eq.symm ▸ hLN)
  let _ : Finite T₂.faces := hT₂fin.to_subtype
  let A := restrict T₂ K.space
  let B := restrict T₂ L.space
  let _ : Finite A.faces := (restrict_faces_finite T₂ K.space).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite T₂ L.space).to_subtype
  have hA : IsSubdivision A K := by
    have ha := (hT₂.restrict (restrict T₁ K.space) (restrict_faces_subset T₁ K.space)).trans hT₁K
    rwa [hT₁K.space_eq] at ha
  have hB : IsSubdivision B L := hT₂L
  have hAm := hK.of_isSubdivision hA
  have hBm := hL.of_isSubdivision hB
  have hcompat : ∀ s ∈ A.faces, ∀ t ∈ B.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) :=
    fun _ hs _ ht => T₂.inter_subset_convexHull hs.1 ht.1
  let U := unionComplex A B hcompat
  let _ : Finite U.faces :=
    (unionComplex_faces_finite A B hcompat (Set.toFinite A.faces) (Set.toFinite B.faces)).to_subtype
  have hUspace : U.space = N.space := by
    rw [unionComplex_space, hA.space_eq, hB.space_eq, hNspace]
  have hid : IsPLHomeomorphOn (id : E → E) N.space U.space := by
    rw [hUspace]
    exact (isPolyhedron_space N).isPLHomeomorphOn_id
  have hUm := hN.of_isPLHomeomorphOn hid
  have hUbd : (boundaryComplex (n + 1) U).space = (boundaryComplex (n + 1) N).space := by
    simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn N U hN hid
  have hAbd := boundaryComplex_space_of_isSubdivision K A hK hA
  have hBbd := boundaryComplex_space_of_isSubdivision L B hL hB
  have hxB : {x} ∈ B.faces :=
    ⟨hT₂.singleton_mem (hT₁.singleton_mem hxT₀), by
      simpa using boundaryComplex_space_subset (n + 1) L hxL⟩
  have hxBdB : {x} ∈ (boundaryComplex (n + 1) B).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset (n + 1) B) hxB
      (mem_openSimplex_singleton x) (hBbd.symm ▸ hxL)
  rw [← hUbd]
  exact not_mem_boundaryComplex_unionComplex_of_boundary_mem_nhdsWithin A B hcompat hAm hBm
    hUm (by rwa [hA.space_eq, hB.space_eq, hAbd])
    (by rwa [hA.space_eq, hB.space_eq, hBbd]) hxBdB
    (by rwa [hA.space_eq, hBbd])

open Classical in
theorem boundaryComplex_space_of_relative_gluing {n : ℕ}
    (K L N : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] [Finite N.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hN : IsCombinatorialManifoldWithBoundary (n + 1) N)
    (hNspace : N.space = K.space ∪ L.space) {B F : Set E}
    (hB : K.space ∩ L.space = B)
    (hBK : B ⊆ (boundaryComplex (n + 1) K).space)
    (hBL : (boundaryComplex (n + 1) L).space = B ∪ F)
    (hF : IsClosed F) (hFdense : F ⊆ closure (F \ B)) :
    (boundaryComplex (n + 1) N).space =
      ((boundaryComplex (n + 1) K).space \ (B \ F)) ∪ F := by
  classical
  let _ : Finite (boundaryComplex (n + 1) N).faces :=
    (boundaryComplex_faces_finite (n + 1) N).to_subtype
  have hKN : K.space ⊆ N.space := hNspace.symm ▸ subset_union_left
  have hLN : L.space ⊆ N.space := hNspace.symm ▸ subset_union_right
  have hBbdL : B ⊆ (boundaryComplex (n + 1) L).space := hBL.symm ▸ subset_union_left
  have hFbdL : F ⊆ (boundaryComplex (n + 1) L).space := hBL.symm ▸ subset_union_right
  have hFsubL := hFbdL.trans (boundaryComplex_space_subset (n + 1) L)
  have hoff (A D : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite D.faces]
      (hA : IsCombinatorialManifoldWithBoundary (n + 1) A)
      (hAN : A.space ⊆ N.space) (hunion : N.space = A.space ∪ D.space)
      {x : E} (hxA : x ∈ A.space) (hxD : x ∉ D.space) :
      x ∈ (boundaryComplex (n + 1) A).space ↔ x ∈ (boundaryComplex (n + 1) N).space := by
    apply mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin N A hN hA hAN hxA
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((isPolyhedron_space D).isClosed.isOpen_compl.mem_nhds hxD)]
      with y hyN hyD
    exact (hunion ▸ hyN).resolve_right hyD
  have hFbdN : F ⊆ (boundaryComplex (n + 1) N).space := by
    apply hFdense.trans
    apply closure_minimal
    · rintro x ⟨hxF, hxB⟩
      have hxK : x ∉ K.space := fun hx => hxB (hB ▸ ⟨hx, hFsubL hxF⟩)
      exact (hoff L K hL hLN (by rw [hNspace, union_comm]) (hFsubL hxF) hxK).mp (hFbdL hxF)
    · exact (isPolyhedron_space (boundaryComplex (n + 1) N)).isClosed
  have hcancel : Disjoint (B \ F) (boundaryComplex (n + 1) N).space := by
    rw [disjoint_left]
    rintro x ⟨hxB, hxF⟩
    apply not_mem_boundaryComplex_of_boundary_mem_nhdsWithin K L N hK hL hN hNspace
      (hB.subset.trans hBK) (hB.subset.trans hBbdL) (hBbdL hxB)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hF.isOpen_compl.mem_nhds hxF)] with y hyL hyF
    have hyB := (hBL ▸ hyL).resolve_right hyF
    exact (hB.symm ▸ hyB).1
  ext x
  constructor
  · intro hx
    have hxN := boundaryComplex_space_subset (n + 1) N hx
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · have hxB : x ∉ B := fun h => disjoint_left.mp hcancel ⟨h, hxF⟩ hx
      have hxL : x ∉ L.space := by
        intro hxL
        have hxK : x ∉ K.space := fun hxK => hxB (hB ▸ ⟨hxK, hxL⟩)
        have hxBdL := (hoff L K hL hLN (by rw [hNspace, union_comm]) hxL hxK).mpr hx
        exact hxB ((hBL ▸ hxBdL).resolve_right hxF)
      have hxK : x ∈ K.space := (hNspace ▸ hxN).resolve_right hxL
      exact Or.inl ⟨(hoff K L hK hKN hNspace hxK hxL).mpr hx, fun h => hxB h.1⟩
  · rintro (⟨hxK, hxBF⟩ | hxF)
    · by_cases hxF : x ∈ F
      · exact hFbdN hxF
      · have hxL : x ∉ L.space := fun hxL => hxBF
          ⟨hB ▸ ⟨boundaryComplex_space_subset (n + 1) K hxK, hxL⟩, hxF⟩
        exact (hoff K L hK hKN hNspace
          (boundaryComplex_space_subset (n + 1) K hxK) hxL).mp hxK
    · exact hFbdN hxF

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLCellAttachmentWith.boundaryComplex_space {n : ℕ}
    {P B V : Set F} {K N : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] [Finite N.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hN : IsCombinatorialManifoldWithBoundary (n + 1) N) {C : Set E} {g : F → E}
    (hatt : IsPLCellAttachmentWith (n + 1) P B K C N.space g)
    (Q : Geometry.SimplicialComplex ℝ F) [Finite Q.faces] (hQspace : Q.space = P)
    (hQboundary : (boundaryComplex (n + 1) Q).space = B ∪ V)
    (hV : IsClosed V) (hVdense : V ⊆ closure (V \ B)) :
    (boundaryComplex (n + 1) N).space =
      ((boundaryComplex (n + 1) K).space \ g '' (B \ V)) ∪ g '' V := by
  classical
  obtain ⟨hP, hBP, hg, hgB, φ, -, hφg, hφbd, e, helow, hecell⟩ := hatt
  have hNspace : N.space = K.space ∪ C := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep (e.symm ⟨x, hx⟩)
      have hqe : e (Quot.mk (adjunctionRel Subtype.val φ) q) = ⟨x, hx⟩ := by
        rw [hq, e.apply_symm_apply]
      cases q with
      | inl z =>
        have heq : (e (adjunctionCell Subtype.val φ z) : E) = x := congrArg Subtype.val hqe
        exact Or.inr (heq ▸ hecell z ▸ hg.bijOn.mapsTo z.property)
      | inr z =>
        have heq : (e (adjunctionLower φ z) : E) = x := congrArg Subtype.val hqe
        exact Or.inl (heq ▸ helow z ▸ z.property)
    · rintro x (hx | hx)
      · have hxN := (e (adjunctionLower φ ⟨x, hx⟩)).property
        rwa [helow ⟨x, hx⟩] at hxN
      · obtain ⟨z, hz, rfl⟩ := hg.bijOn.surjOn hx
        have hzN := (e (adjunctionCell Subtype.val φ ⟨z, hz⟩)).property
        rwa [hecell ⟨z, hz⟩] at hzN
  have hBboundary : g '' B ⊆ (boundaryComplex (n + 1) K).space := by
    rintro x ⟨z, hz, rfl⟩
    have hh := hφbd ⟨⟨z, hBP hz⟩, hz⟩
    rwa [hφg ⟨⟨z, hBP hz⟩, hz⟩] at hh
  have hCball : IsPLBall (n + 1) C := hP.of_isPLHomeomorphOn hg
  obtain ⟨L, hLfin, hLspace⟩ := hCball.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hLball : IsPLBall (n + 1) L.space := hLspace.symm ▸ hCball
  have hQball : IsPLBall (n + 1) Q.space := hQspace.symm ▸ hP
  have hgQL : IsPLHomeomorphOn g Q.space L.space := by rwa [hQspace, hLspace]
  have hLboundary : (boundaryComplex (n + 1) L).space = g '' B ∪ g '' V := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn Q L hQball.isCombinatorialManifoldWithBoundary
      hgQL, hQboundary, image_union]
  have hVP : V ⊆ P := by
    rw [← hQspace]
    exact (hQboundary.symm ▸ subset_union_right).trans (boundaryComplex_space_subset (n + 1) Q)
  have himageDiff (X Y : Set F) (hX : X ⊆ P) (hY : Y ⊆ P) :
      g '' (X \ Y) = g '' X \ g '' Y := by
    rw [(hg.bijOn.injOn.mono hX).image_sdiff, hg.bijOn.injOn.image_inter hX hY]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hVclosed : IsClosed (g '' V) :=
    ((hP.isPolyhedron.isCompact.of_isClosed_subset hV hVP).image_of_continuousOn
      (hg.isPiecewiseAffineOn.continuousOn.mono hVP)).isClosed
  have hVimageDense : g '' V ⊆ closure (g '' V \ g '' B) := by
    rw [← himageDiff V B hVP hBP,
      ← hg.image_closure hP.isPolyhedron.isCompact (sdiff_subset.trans hVP)]
    exact image_mono hVdense
  rw [himageDiff B V hBP hVP]
  exact boundaryComplex_space_of_relative_gluing K L N hK
    hLball.isCombinatorialManifoldWithBoundary hN (by rwa [hLspace])
    (by rw [hLspace, inter_comm]; exact hgB.image_eq.symm) hBboundary
    hLboundary hVclosed hVimageDense

end General

private theorem isClosed_stdSimplexBoundary (n : ℕ) : IsClosed (stdSimplexBoundary n) := by
  have hc : IsClosed (⋃ i : Fin (n + 1), {x : Fin (n + 1) → ℝ | x i = 0}) :=
    isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_apply i) continuous_const
  convert (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin (n + 1))).isClosed.inter hc using 1
  ext x
  simp [stdSimplexBoundary]

open Classical in
private theorem boundaryComplex_space_stdSimplex_prism
    [d : DecidableEq ((Fin 3 → ℝ) × ℝ)]
    (Q : Geometry.SimplicialComplex ℝ ((Fin 3 → ℝ) × ℝ)) [Finite Q.faces]
    (hQspace : Q.space = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) :
    (boundaryComplex 3 Q).space =
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ∪
        stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
  classical
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  obtain ⟨D, hDfin, hDspace⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  have hDball : IsPLBall 2 D.space := hDspace.symm ▸ isPLBall_stdSimplex 2
  have hid := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  have hDbd : (boundaryComplex 2 D).space = stdSimplexBoundary 2 := by
    simpa only [image_id] using (hid.image_stdSimplexBoundary_eq_boundaryComplex D hDspace).symm
  have hQ : Q.space = D.space ×ˢ Icc (0 : ℝ) 1 := by rwa [hDspace]
  rw [boundaryComplex_space_prism D hDball (by norm_num : (0 : ℝ) < 1) Q hQ,
    hDspace, hDbd]

private theorem stdSimplex_prism_ends_sdiff_side :
    (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) \
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ) := by
  ext ⟨x, t⟩
  constructor
  · rintro ⟨⟨hx, ht⟩, hn⟩
    refine ⟨⟨hx, fun hJ => hn ⟨hJ, ?_⟩⟩, ht⟩
    rcases ht with rfl | rfl <;> norm_num
  · rintro ⟨⟨hx, hn⟩, ht⟩
    exact ⟨⟨hx, ht⟩, fun h => hn h.1⟩

private theorem stdSimplex_prism_side_sdiff_ends :
    (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) \
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) =
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
  ext ⟨x, t⟩
  constructor
  · rintro ⟨⟨hx, ht⟩, hn⟩
    have ht0 : t ≠ 0 := fun h => hn ⟨hx.1, Or.inl h⟩
    have ht1 : t ≠ 1 := fun h => hn ⟨hx.1, Or.inr h⟩
    exact ⟨hx, lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  · rintro ⟨hx, ht⟩
    refine ⟨⟨hx, ht.1.le, ht.2.le⟩, ?_⟩
    rintro ⟨-, ht0 | ht1⟩
    · exact ht.1.ne ht0.symm
    · exact ht.2.ne ht1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem boundaryComplex_space_of_isPLCellAttachmentWith_one [FiniteDimensional ℝ E]
    {L N' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite N'.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L)
    (hN' : IsCombinatorialManifoldWithBoundary 3 N') {C : Set E} {g : (Fin 3 → ℝ) × ℝ → E}
    (hatt : IsPLCellAttachmentWith 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) L C N'.space g) :
    (boundaryComplex 3 N').space =
      ((boundaryComplex 3 L).space \
          g '' ((Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ))) ∪
        g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let _ : DecidableEq ((Fin 3 → ℝ) × ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := hatt.1.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hclosed : IsClosed (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    (isClosed_stdSimplexBoundary 2).prod isClosed_Icc
  have hdense : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ⊆
      closure ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) \
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ))) := by
    rw [stdSimplex_prism_side_sdiff_ends, closure_prod_eq,
      (isClosed_stdSimplexBoundary 2).closure_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have h := hatt.boundaryComplex_space hL hN' Q hQspace
    (boundaryComplex_space_stdSimplex_prism Q hQspace) hclosed hdense
  rwa [stdSimplex_prism_ends_sdiff_side] at h

open Classical in
theorem boundaryComplex_space_of_isPLCellAttachmentWith_two [FiniteDimensional ℝ E]
    {L N' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite N'.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L)
    (hN' : IsCombinatorialManifoldWithBoundary 3 N') {C : Set E} {g : (Fin 3 → ℝ) × ℝ → E}
    (hatt : IsPLCellAttachmentWith 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) L C N'.space g) :
    (boundaryComplex 3 N').space =
      ((boundaryComplex 3 L).space \ g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) ∪
        g '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) := by
  classical
  let _ : DecidableEq ((Fin 3 → ℝ) × ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := hatt.1.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hZclosed : IsClosed ({0, 1} : Set ℝ) :=
    (Set.Finite.insert 0 (finite_singleton 1)).isClosed
  have hclosed : IsClosed (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) :=
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).isClosed.prod hZclosed
  have hdense : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) ⊆
      closure ((Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) \
        (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) := by
    have hid := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
    have hcl : closure (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) =
        Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
      simpa only [image_id] using hid.closure_sdiff_image_stdSimplexBoundary
    rw [stdSimplex_prism_ends_sdiff_side, closure_prod_eq, hcl, hZclosed.closure_eq]
  have hQbd : (boundaryComplex 3 Q).space =
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ∪
        Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ) := by
    rw [boundaryComplex_space_stdSimplex_prism Q hQspace, union_comm]
  have h := hatt.boundaryComplex_space hL hN' Q hQspace hQbd hclosed hdense
  rwa [stdSimplex_prism_side_sdiff_ends] at h

open Classical in
theorem boundaryComplex_space_of_isPLCellAttachmentWith_three [FiniteDimensional ℝ E]
    {L N' : Geometry.SimplicialComplex ℝ E} [Finite L.faces] [Finite N'.faces]
    (hL : IsCombinatorialManifoldWithBoundary 3 L)
    (hN' : IsCombinatorialManifoldWithBoundary 3 N') {C : Set E} {g : (Fin 4 → ℝ) → E}
    (hatt : IsPLCellAttachmentWith 3 (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) (stdSimplexBoundary 3) L C
      N'.space g) :
    (boundaryComplex 3 N').space = (boundaryComplex 3 L).space \ g '' stdSimplexBoundary 3 := by
  classical
  let _ : DecidableEq (Fin 4 → ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := hatt.1.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hid := (isPLBall_stdSimplex 3).isPolyhedron.isPLHomeomorphOn_id
  have hQbd : (boundaryComplex 3 Q).space = stdSimplexBoundary 3 ∪ ∅ := by
    simpa only [image_id, union_empty] using
      (hid.image_stdSimplexBoundary_eq_boundaryComplex Q hQspace).symm
  have h := hatt.boundaryComplex_space hL hN' Q hQspace hQbd isClosed_empty (empty_subset _)
  simpa only [sdiff_empty, image_empty, union_empty] using h

end DifferentialGeometry.Topology.PiecewiseLinear
