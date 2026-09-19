/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodEdge
import DifferentialGeometry.Topology.PiecewiseLinear.BallIntersectionDensity
import DifferentialGeometry.Topology.PiecewiseLinear.PrismSide

/-! Triangle cells as PL prisms attached along their lateral annuli. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem exists_two_cofaces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) :
    ∃ q r : Finset E, q ∈ K.faces ∧ r ∈ K.faces ∧ q.card = 4 ∧ r.card = 4 ∧
      q ≠ r ∧ s ⊂ q ∧ s ⊂ r ∧ ∀ t ∈ K.faces, s ⊂ t → t = q ∨ t = r := by
  classical
  obtain ⟨a, b, hab, hpair⟩ := hK.codimension_one_cofaces K hs hcard
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact mem_insert _ _
  have hb : b ∉ s ∧ insert b s ∈ K.faces := by
    change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact mem_insert_of_mem _ (mem_singleton _)
  have hne : insert a s ≠ insert b s := by
    intro h
    have hamem : a ∈ insert b s := h ▸ Finset.mem_insert_self a s
    exact hab ((Finset.mem_insert.mp hamem).resolve_right ha.1)
  refine ⟨insert a s, insert b s, ha.2, hb.2, ?_, ?_, hne, ?_, ?_, ?_⟩
  · simp [Finset.card_insert_of_notMem ha.1, hcard]
  · simp [Finset.card_insert_of_notMem hb.1, hcard]
  · exact Finset.ssubset_insert ha.1
  · exact Finset.ssubset_insert hb.1
  · intro t ht hst
    have htc : t.card = s.card + 1 := by
      have hle := hK.card_le K ht
      have hlt := Finset.card_lt_card hst
      omega
    obtain ⟨w, hws, htw⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst.le, htc.symm⟩
    have hw : w ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := ⟨hws, htw.symm ▸ ht⟩
    rw [hpair] at hw
    rcases hw with hwa | hwb
    · exact Or.inl (htw.symm.trans (congrArg (fun v => insert v s) hwa))
    · exact Or.inr (htw.symm.trans (congrArg (fun v => insert v s) hwb))

open Classical in
theorem exists_isPLHomeomorphOn_derivedNeighborhoodCell_triangle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : ∀ t ∈ L.faces, t.card ≤ 3) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) (hsL : s ∉ L.faces)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    ∃ g : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3) ×ˢ Icc 0 1)
        (derivedNeighborhoodCell K s).space ∧
      IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc 0 1)
        ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space) := by
  classical
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  let C := derivedNeighborhoodCell K s
  let N := derivedNeighborhood K L
  let B := boundaryComplex 3 C
  let A := C.space ∩ N.space
  let _ : Finite C.faces := (derivedNeighborhoodCell_faces_finite K s).to_subtype
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K L).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 C).to_subtype
  have hKw := hK.isCombinatorialManifoldWithBoundary
  have hC : IsPLBall 3 C.space := hKw.isPLBall_derivedNeighborhoodCell hs
  obtain ⟨q, r, hq, hr, hqc, hrc, hqr, hsq, hsr, hco⟩ := exists_two_cofaces K hK hs hcard
  let D₀ := C.space ∩ (derivedNeighborhoodCell K q).space
  let D₁ := C.space ∩ (derivedNeighborhoodCell K r).space
  have hD₀ : IsPLBall 2 D₀ :=
    hKw.isPLBall_derivedNeighborhoodCell_inter hs hq hsq.ne (Or.inl hsq.le)
  have hD₁ : IsPLBall 2 D₁ :=
    hKw.isPLBall_derivedNeighborhoodCell_inter hs hr hsr.ne (Or.inl hsr.le)
  have hD₀B : D₀ ⊆ B.space :=
    hKw.derivedNeighborhoodCell_inter_subset_boundaryComplex hs hq hsq.ne
  have hD₁B : D₁ ⊆ B.space :=
    hKw.derivedNeighborhoodCell_inter_subset_boundaryComplex hs hr hsr.ne
  have hdis : Disjoint D₀ D₁ :=
    (disjoint_derivedNeighborhoodCell_of_card_eq K hq hr (hqc.trans hrc.symm) hqr).mono
      inter_subset_right inter_subset_right
  have hAeq : A = ⋃ t ∈ (simplexBoundary s (K.indep hs)).faces,
      C.space ∩ (derivedNeighborhoodCell K t).space :=
    derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion K L hLK hs hsL
      (fun t ht => hcard.symm ▸ hL t ht) hproper
  have hAB : A ⊆ B.space := by
    intro x hx
    rw [hAeq] at hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact hKw.derivedNeighborhoodCell_inter_subset_boundaryComplex hs
      (K.down_closed hs ht.1 ht.2.1) ht.2.2.symm hxt
  have hcover : B.space = A ∪ D₀ ∪ D₁ := by
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ C.space ∩ ⋃ t ∈ K.faces \ {s}, (derivedNeighborhoodCell K t).space :=
        boundaryComplex_derivedNeighborhoodCell_space K hK hs ▸ hx
      obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx'.2
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
        hs ht.1 ⟨x, hx'.1, hxt⟩ with hst | hts
      · rcases hco t ht.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hst, fun h => ht.2 h.symm⟩) with h | h
        · exact Or.inl (Or.inr ⟨hx'.1, h ▸ hxt⟩)
        · exact Or.inr ⟨hx'.1, h ▸ hxt⟩
      · left
        left
        rw [hAeq]
        exact mem_iUnion₂.mpr ⟨t, ⟨hts, K.nonempty_of_mem_faces ht.1, ht.2⟩, hx'.1, hxt⟩
    · exact union_subset (union_subset hAB hD₀B) hD₁B
  have hBs : IsPLSphere 2 B.space := isPLSphere_boundaryComplex_space_of_isPLBall C hC
  have hBm : IsCombinatorialManifoldWithBoundary 2 B :=
    hBs.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  have hdense : A ⊆ closure (B.space \ (D₀ ∪ D₁)) := by
    intro x hx
    rw [hAeq] at hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    have htK := K.down_closed hs ht.1 ht.2.1
    have hts : t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, ht.2.2⟩
    let T := C.space ∩ (derivedNeighborhoodCell K t).space
    have hT : IsPLBall 2 T :=
      hKw.isPLBall_derivedNeighborhoodCell_inter hs htK hts.ne.symm (Or.inr hts.le)
    have hTB : T ⊆ B.space :=
      hKw.derivedNeighborhoodCell_inter_subset_boundaryComplex hs htK hts.ne.symm
    have hI (u : Finset E) (hu : u ∈ K.faces) (hsu : s ⊂ u) :
        IsPLBall 1 (T ∩ (C.space ∩ (derivedNeighborhoodCell K u).space)) := by
      have h := hKw.isPLBall_derivedNeighborhoodCell_inter_inter hs htK hu
        hts.ne.symm hsu.ne (hts.trans hsu).ne
        (Or.inr hts.le) (Or.inl hsu.le) (Or.inl (hts.le.trans hsu.le))
      convert h using 1
      ext y
      simp only [T, C, mem_inter_iff]
      tauto
    have hden := hBm.subset_closure_sdiff_iUnion_of_isPLBall_inter hT hTB
      (fun i : Bool => if i then D₁ else D₀)
      (fun i => by cases i <;> assumption)
      (fun i => by cases i <;> assumption)
      (fun i => by
        cases i with
        | false => exact hI q hq hsq
        | true => exact hI r hr hsr)
    have hu : (⋃ i : Bool, if i then D₁ else D₀) = D₀ ∪ D₁ := by
      ext y
      simp
    rw [hu] at hden
    exact hden hxt
  have hAcl : A = closure (B.space \ (D₀ ∪ D₁)) := by
    refine Subset.antisymm hdense (closure_minimal ?_
      ((isPolyhedron_space C).isClosed.inter (isPolyhedron_space N).isClosed))
    rintro x ⟨hxB, hxD⟩
    rw [hcover] at hxB
    rcases hxB with (hxA | hx₀) | hx₁
    · exact hxA
    · exact (hxD (Or.inl hx₀)).elim
    · exact (hxD (Or.inr hx₁)).elim
  let P : Set (Fin 3 → ℝ) := stdSimplex ℝ (Fin 3)
  have hP : IsPLBall 2 P := isPLBall_stdSimplex 2
  obtain ⟨f, hf⟩ := hD₀
  obtain ⟨g, hg, hg0, hg1⟩ := exists_isPLHomeomorphOn_prism_map_ends hP zero_lt_one C hC
    hD₀B hD₁ hD₁B hdis hf
  have hg0image : g '' (P ×ˢ {0}) = D₀ := by
    have h0 : EqOn (g ∘ fun x => (x, (0 : ℝ))) f P := hg0
    rw [← hP.isPolyhedron.isPLHomeomorphOn_prod_const (0 : ℝ) |>.image_eq, image_image]
    exact h0.image_eq.trans hf.image_eq
  obtain ⟨R, hRfin, hRspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (boundaryComplex 2 R).faces := (boundaryComplex_faces_finite 2 R).to_subtype
  have hR : IsPLBall 2 R.space := hRspace.symm ▸ hP
  have hid : IsPLHomeomorphOn (id : (Fin 3 → ℝ) → _) P R.space :=
    hRspace.symm ▸ hP.isPolyhedron.isPLHomeomorphOn_id
  have hRB : (boundaryComplex 2 R).space = stdSimplexBoundary 2 := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex R hid
    rw [simplexBoundary_stdVertices_space, image_id] at h
    exact h
  have hgR : IsPLHomeomorphOn g (R.space ×ˢ Icc 0 1) C.space := by
    rwa [hRspace]
  have hside := hgR.image_prism_side R hR C zero_lt_one
  rw [hRB, hRspace, hg0image, hg1, ← hAcl] at hside
  have hpoly : IsPolyhedron (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    (hRB ▸ isPolyhedron_space (boundaryComplex 2 R)).prod
      (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).isPolyhedron
  refine ⟨g, hg, ?_⟩
  change IsPLHomeomorphOn g (stdSimplexBoundary 2 ×ˢ Icc 0 1) A
  rw [← hside]
  exact hg.restrict hpoly (prod_mono (fun _ hx => hx.1) Subset.rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
