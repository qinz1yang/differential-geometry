import DifferentialGeometry.Topology.PiecewiseLinear.ConeIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCorner
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem simplexComplex_erase_faces_subset_simplexBoundary [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T) :
    (simplexComplex (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).faces ⊆
      (simplexBoundary T hT).faces := by
  rintro s ⟨hne, hs⟩
  refine ⟨hs.trans (Finset.erase_subset a T), hne, ?_⟩
  intro he
  exact Finset.notMem_erase a T (hs (he ▸ ha))

theorem simplexAvoiding_erase_faces_subset_simplexBoundary [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (a : E) :
    (simplexAvoiding T hT {T.erase a}).faces ⊆ (simplexBoundary T hT).faces := by
  rintro s ⟨hne, hsT, havoid⟩
  refine ⟨hsT, hne, ?_⟩
  intro he
  exact havoid _ (Finset.mem_singleton_self _) (he ▸ Finset.erase_subset a T)

theorem coneComplex_simplexAvoiding_inter_convexHull [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) {p : E} (hpopen : p ∈ openSimplex T)
    (hp : IsConeBase p (simplexAvoiding T hT {T.erase a})) :
    (coneComplex hp).space ∩ convexHull ℝ ((insert p (T.erase a) : Finset E) : Set E) =
      (coneComplex (hp.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a))).space := by
  have hne : (T.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  let hK := isConeBase_simplexBoundary hT hcard hpopen
  let hL := simplexAvoiding_erase_faces_subset_simplexBoundary T hT a
  let hM := simplexComplex_erase_faces_subset_simplexBoundary T hT ha
  have hinter : (simplexAvoiding T hT {T.erase a}).space ∩
      (simplexComplex (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
    rw [simplexComplex_space _ _ hne]
    exact simplexAvoiding_space_inter_convexHull_erase T hT a
  have h := coneComplex_space_inter hK hL hM
    (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a) hinter
  rw [coneComplex_simplexComplex_space _ _ hne] at h
  exact h

theorem coneComplex_simplexAvoiding_inter_opposite_face [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) {p : E} (hpopen : p ∈ openSimplex T)
    (hp : IsConeBase p (simplexAvoiding T hT {T.erase a})) :
    (coneComplex hp).space ∩ convexHull ℝ ((T.erase a : Finset E) : Set E) =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
  have hne : (T.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem ha]
    omega
  have hinter : (simplexAvoiding T hT {T.erase a}).space ∩
      (simplexComplex (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
    rw [simplexComplex_space _ _ hne]
    exact simplexAvoiding_space_inter_convexHull_erase T hT a
  have h := coneComplex_space_inter_base (isConeBase_simplexBoundary hT hcard hpopen)
    (simplexAvoiding_erase_faces_subset_simplexBoundary T hT a)
    (simplexComplex_erase_faces_subset_simplexBoundary T hT ha) hinter
  rw [simplexComplex_space _ _ hne] at h
  exact h

theorem convexHull_insert_eq_union_coneComplex_simplexAvoiding [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T)
    {q : E} (hqF : q ∉ T.erase a)
    (hind : AffineIndependent ℝ ((↑) : ↥(insert q (T.erase a) : Finset E) → E))
    (haopen : a ∈ openSimplex (insert q (T.erase a)))
    (hq : IsConeBase q (simplexAvoiding T hT {T.erase a})) :
    convexHull ℝ ((insert q (T.erase a) : Finset E) : Set E) =
      convexHull ℝ (T : Set E) ∪ (coneComplex hq).space := by
  have hCT : convexHull ℝ (T : Set E) ⊆
      convexHull ℝ ((insert q (T.erase a) : Finset E) : Set E) := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro v hv
    by_cases hva : v = a
    · rw [hva]
      exact openSimplex_subset_convexHull _ haopen
    · exact subset_convexHull ℝ _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hva, hv⟩))
  apply Subset.antisymm
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase hind haopen hx
    rcases Finset.mem_insert.mp hv with rfl | hv
    · left
      simpa only [Finset.erase_insert hqF, Finset.insert_erase ha] using hxv
    · right
      have hqv : q ≠ v := (ne_of_mem_of_not_mem hv hqF).symm
      rw [Finset.erase_insert_of_ne hqv, Finset.insert_comm a q] at hxv
      refine (coneComplex hq).convexHull_subset_space
        (Or.inr (Or.inr ⟨insert a ((T.erase a).erase v), ?_, rfl⟩)) hxv
      refine ⟨Finset.insert_nonempty _ _, Finset.insert_subset ha
        ((Finset.erase_subset v _).trans (Finset.erase_subset a T)), ?_⟩
      simp only [Finset.mem_singleton, forall_eq]
      intro h
      rcases Finset.mem_insert.mp (h hv) with hva | hve
      · exact Finset.ne_of_mem_erase hv hva
      · exact Finset.notMem_erase v (T.erase a) hve
  · apply union_subset hCT
    intro x hx
    rcases (mem_coneComplex_space_iff hq).mp hx with rfl | ⟨z, hz, r, hr, hr', rfl⟩
    · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    · rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))
        (hCT (simplexAvoiding_space_subset T hT _ hz)) (sub_nonneg.mpr hr') hr.le (by ring)

theorem frontier_convexHull_insert_eq_union_coneComplex [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hne : T.Nonempty)
    {p : E} (hpT : p ∉ T)
    (hind : AffineIndependent ℝ ((↑) : ↥(insert p T : Finset E) → E))
    (hspan : affineSpan ℝ ((insert p T : Finset E) : Set E) = ⊤)
    (hp : IsConeBase p (simplexBoundary T hT)) :
    frontier (convexHull ℝ ((insert p T : Finset E) : Set E)) =
      convexHull ℝ (T : Set E) ∪ (coneComplex hp).space := by
  rw [frontier_convexHull_eq_biUnion_erase _ hind hspan]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl (by simpa only [Finset.erase_insert hpT] using hxv)
    · have hpv : p ≠ v := (ne_of_mem_of_not_mem hv hpT).symm
      rw [Finset.erase_insert_of_ne hpv] at hxv
      rcases (T.erase v).eq_empty_or_nonempty with he | he
      · rw [he, Finset.insert_empty, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hxv
        exact Or.inr (hxv ▸ apex_mem_coneComplex_space hp)
      · refine Or.inr ((coneComplex hp).convexHull_subset_space
          (Or.inr (Or.inr ⟨T.erase v, ?_, rfl⟩)) hxv)
        refine ⟨Finset.erase_subset v T, he, ?_⟩
        intro heq
        apply Finset.notMem_erase v T
        rw [heq]
        exact hv
  · rintro x (hx | hx)
    · exact mem_iUnion₂.mpr ⟨p, Finset.mem_insert_self p T, by
        simpa only [Finset.erase_insert hpT] using hx⟩
    · rcases (mem_coneComplex_space_iff hp).mp hx with hxp | ⟨z, hz, s, hs, hs', rfl⟩
      · obtain ⟨v, hv⟩ := hne
        refine mem_iUnion₂.mpr ⟨v, Finset.mem_insert_of_mem hv, ?_⟩
        rw [hxp]
        exact subset_convexHull ℝ _ (Finset.mem_erase.mpr
          ⟨(ne_of_mem_of_not_mem hv hpT).symm, Finset.mem_insert_self p T⟩)
      · obtain ⟨σ, hσ, hzσ⟩ := (simplexBoundary T hT).mem_space_iff.mp hz
        obtain ⟨v, hv, hvσ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσ.1, hσ.2.2⟩)
        refine mem_iUnion₂.mpr ⟨v, Finset.mem_insert_of_mem hv, ?_⟩
        apply convexHull_mono (Finset.coe_subset.mpr ?_) (mem_convexHull_insert_of_combo hzσ hs.le hs')
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact Finset.mem_erase.mpr ⟨(ne_of_mem_of_not_mem hv hpT).symm, Finset.mem_insert_self _ T⟩
        · exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hu hvσ, Finset.mem_insert_of_mem (hσ.1 hu)⟩

theorem frontier_coneComplex_simplexAvoiding_union_subset [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {p q : E} (hpopen : p ∈ openSimplex T)
    (hp : IsConeBase p (simplexAvoiding T hT {T.erase a}))
    (hq : IsConeBase q (simplexAvoiding T hT {T.erase a}))
    (hqind : AffineIndependent ℝ ((↑) : ↥(insert q (T.erase a) : Finset E) → E))
    (haopen : a ∈ openSimplex (insert q (T.erase a)))
    (hqinter : (coneComplex hq).space ∩ convexHull ℝ (T : Set E) =
      (simplexAvoiding T hT {T.erase a}).space) :
    frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
      (coneComplex (hp.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a))).space ∪
      (coneComplex (hq.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a))).space := by
  let F := T.erase a
  let hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  let L := simplexAvoiding T hT {F}
  let B := simplexBoundary F hF
  let hBL := simplexBoundary_erase_faces_subset_simplexAvoiding T hT a
  let P := (coneComplex hp).space
  let Q := (coneComplex hq).space
  let C := convexHull ℝ (T : Set E)
  let Cp := convexHull ℝ ((insert p F : Finset E) : Set E)
  let Cq := convexHull ℝ ((insert q F : Finset E) : Set E)
  let D := convexHull ℝ (F : Set E)
  let Sp := (coneComplex (hp.of_faces_subset hBL)).space
  let Sq := (coneComplex (hq.of_faces_subset hBL)).space
  have hFne : F.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [F]
    rw [Finset.card_erase_of_mem ha]
    omega
  have hpF : p ∉ F := notMem_erase_of_mem_openSimplex hT hpopen ha
  have hqF : q ∉ F := by
    intro hqmem
    have hqC : q ∈ C := subset_convexHull ℝ _ (Finset.mem_of_mem_erase hqmem)
    exact hq.notMem_space (hqinter ▸ ⟨apex_mem_coneComplex_space hq, hqC⟩)
  let hK := isConeBase_simplexBoundary hT hcard hpopen
  have hpind : AffineIndependent ℝ ((↑) : ↥(insert p F : Finset E) → E) := by
    have h := hK.indep F (erase_mem_simplexBoundary_faces hT hcard ha)
    rw [← Finset.coe_insert] at h
    exact h
  have hfull {r : E} (hr : r ∉ F)
      (hrind : AffineIndependent ℝ ((↑) : ↥(insert r F : Finset E) → E)) :
      affineSpan ℝ ((insert r F : Finset E) : Set E) = ⊤ := by
    have hdim : Fintype.card T = Module.finrank ℝ E + 1 :=
      hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp (by
        have hrange : range ((↑) : T → E) = (T : Set E) := Subtype.range_coe
        rw [hrange]
        exact hspan)
    have hsize : (insert r F).card = T.card := by
      rw [Finset.card_insert_of_notMem hr]
      dsimp [F]
      rw [Finset.card_erase_of_mem ha]
      omega
    have h := hrind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, hsize] using hdim)
    have hrange : range ((↑) : ↥(insert r F : Finset E) → E) =
        ((insert r F : Finset E) : Set E) := Subtype.range_coe
    rwa [hrange] at h
  have hfrontp : frontier Cp = D ∪ Sp :=
    frontier_convexHull_insert_eq_union_coneComplex F hF hFne hpF hpind (hfull hpF hpind)
      (hp.of_faces_subset hBL)
  have hfrontq : frontier Cq = D ∪ Sq :=
    frontier_convexHull_insert_eq_union_coneComplex F hF hFne hqF hqind (hfull hqF hqind)
      (hq.of_faces_subset hBL)
  have hPCp : P ∪ Cp = C := coneComplex_simplexAvoiding_union_convexHull T hT ha hpopen hp
  have hCQ : C ∪ Q = Cq :=
    (convexHull_insert_eq_union_coneComplex_simplexAvoiding T hT ha hqF hqind haopen hq).symm
  have hPC : P ⊆ C := (subset_union_left : P ⊆ P ∪ Cp).trans_eq hPCp
  have hCpC : Cp ⊆ C := (subset_union_right : Cp ⊆ P ∪ Cp).trans_eq hPCp
  have hCCq : C ⊆ Cq := (subset_union_left : C ⊆ C ∪ Q).trans_eq hCQ
  have hQCq : Q ⊆ Cq := (subset_union_right : Q ⊆ C ∪ Q).trans_eq hCQ
  have hPCq : P ∪ Q ⊆ Cq := union_subset (hPC.trans hCCq) hQCq
  have hPinter : P ∩ Cp = Sp := coneComplex_simplexAvoiding_inter_convexHull T hT hcard ha hpopen hp
  have hPD : P ∩ D = B.space := coneComplex_simplexAvoiding_inter_opposite_face T hT hcard ha hpopen hp
  have hLD : L.space ∩ D = B.space := simplexAvoiding_space_inter_convexHull_erase T hT a
  have hLCp : Cp ∩ L.space = B.space := by
    have hLM : (simplexComplex F hF).space ∩ L.space = B.space := by
      rw [simplexComplex_space _ _ hFne, inter_comm]
      exact hLD
    have h := coneComplex_space_inter_base hK
      (simplexComplex_erase_faces_subset_simplexBoundary T hT ha)
      (simplexAvoiding_erase_faces_subset_simplexBoundary T hT a) hLM
    have hMF := hK.of_faces_subset (simplexComplex_erase_faces_subset_simplexBoundary T hT ha)
    have hcone := coneComplex_simplexComplex_space F hF hFne hMF
    rw [hcone] at h
    exact h
  have hNinter : (P ∪ Q) ∩ Cp ⊆ Sp := by
    rintro x ⟨hxP | hxQ, hxCp⟩
    · exact hPinter ▸ ⟨hxP, hxCp⟩
    · have hxL : x ∈ L.space := hqinter ▸ ⟨hxQ, hCpC hxCp⟩
      have hxB : x ∈ B.space := hLCp ▸ ⟨hxCp, hxL⟩
      exact space_subset_coneComplex_space _ hxB
  have hND : (P ∪ Q) ∩ D ⊆ B.space := by
    rintro x ⟨hxP | hxQ, hxD⟩
    · exact hPD ▸ ⟨hxP, hxD⟩
    · have hxC : x ∈ C := convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset a T)) hxD
      have hxL : x ∈ L.space := hqinter ▸ ⟨hxQ, hxC⟩
      exact hLD ▸ ⟨hxL, hxD⟩
  have hcover : Cq \ Cp ⊆ P ∪ Q := by
    intro x hx
    have hxCQ : x ∈ C ∪ Q := hCQ.symm ▸ hx.1
    rcases hxCQ with hxC | hxQ
    · have hxPCp : x ∈ P ∪ Cp := hPCp.symm ▸ hxC
      exact Or.inl (hxPCp.resolve_right hx.2)
    · exact Or.inr hxQ
  have : Finite L.faces := (simplexAvoiding_faces_finite T hT {F}).to_subtype
  have : Finite (coneComplex hp).faces := (coneComplex_faces_finite hp (Set.toFinite L.faces)).to_subtype
  have : Finite (coneComplex hq).faces := (coneComplex_faces_finite hq (Set.toFinite L.faces)).to_subtype
  have hNclosed : IsClosed (P ∪ Q) := (isPolyhedron_space (coneComplex hp)).isClosed.union
    (isPolyhedron_space (coneComplex hq)).isClosed
  have hCpclosed : IsClosed Cp := ((insert p F : Finset E).finite_toSet.isCompact_convexHull ℝ).isClosed
  intro x hx
  have hxN : x ∈ P ∪ Q := hNclosed.closure_subset (frontier_subset_closure hx)
  have hDside (hxD : x ∈ D) : x ∈ Sp ∪ Sq :=
    Or.inl (space_subset_coneComplex_space _ (hND ⟨hxN, hxD⟩))
  by_cases hxp : x ∈ frontier Cp
  · rw [hfrontp] at hxp
    exact hxp.elim hDside Or.inl
  have hxCp : x ∉ Cp := fun hxCp => hxp (hfrontp.symm ▸ Or.inr (hNinter ⟨hxN, hxCp⟩))
  by_cases hxq : x ∈ frontier Cq
  · rw [hfrontq] at hxq
    exact hxq.elim hDside Or.inr
  have hxCqi : x ∈ interior Cq := by
    by_contra hxint
    exact hxq ⟨subset_closure (hPCq hxN), hxint⟩
  have hU : IsOpen (interior Cq \ Cp) := isOpen_interior.sdiff hCpclosed
  have hUsub : interior Cq \ Cp ⊆ P ∪ Q :=
    (sdiff_subset_sdiff_left interior_subset).trans hcover
  exact (hx.2 ((interior_maximal hUsub hU) ⟨hxCqi, hxCp⟩)).elim

theorem exists_isConeBase_simplexAvoiding_with_frontier [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ (p q : E) (hp : IsConeBase p (simplexAvoiding T hT {T.erase a}))
      (hq : IsConeBase q (simplexAvoiding T hT {T.erase a})),
      (coneComplex hp).space ∩ (coneComplex hq).space = (simplexAvoiding T hT {T.erase a}).space ∧
      (coneComplex hp).space ⊆ convexHull ℝ (T : Set E) ∧
      (coneComplex hq).space ∩ convexHull ℝ (T : Set E) =
        (simplexAvoiding T hT {T.erase a}).space ∧
      (coneComplex hp).space ∪ (coneComplex hq).space ⊆ U ∧
      frontier ((coneComplex hp).space ∪ (coneComplex hq).space) ⊆
        (coneComplex (hp.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a))).space ∪
        (coneComplex (hq.of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a))).space := by
  obtain ⟨p, q, hpopen, -, hqind, haopen, hp, hq, hinter, hpT, hqinter, hUsub⟩ :=
    exists_isConeBase_simplexAvoiding_in_neighborhood T hT hcard ha hU hTU
  exact ⟨p, q, hp, hq, hinter, hpT, hqinter, hUsub,
    frontier_coneComplex_simplexAvoiding_union_subset T hT hcard hspan ha hpopen hp hq hqind haopen hqinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
