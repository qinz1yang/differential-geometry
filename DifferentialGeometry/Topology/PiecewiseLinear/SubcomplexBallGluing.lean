import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem inter_subset_boundaryComplex_of_isPLBall
    {n : ℕ} (R A B : Geometry.SimplicialComplex ℝ E)
    [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hA : IsPLBall (n + 1) A.space) (hB : IsPLBall (n + 1) B.space)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces)
    (hI : IsPLBall n (A.space ∩ B.space)) :
    A.space ∩ B.space ⊆ (boundaryComplex (n + 1) A).space := by
  classical
  let I := restrict A B.space
  let _ : Finite I.faces := (restrict_faces_finite A B.space).to_subtype
  have hfaces (s : Finset E) : s ∈ I.faces ↔ s ∈ A.faces ∧ s ∈ B.faces := by
    constructor
    · intro hs
      refine ⟨hs.1, ?_⟩
      have hx := centroid_mem_openSimplex (A.nonempty_of_mem_faces hs.1)
      exact mem_faces_of_mem_openSimplex_of_mem_space hBR (hAR hs.1) hx
        (hs.2 (openSimplex_subset_convexHull _ hx))
    · rintro ⟨hsA, hsB⟩
      exact ⟨hsA, B.convexHull_subset_space hsB⟩
  have hspace : I.space = A.space ∩ B.space := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨space_mono_of_faces_subset (restrict_faces_subset A B.space) hx,
        restrict_space_subset A B.space hx⟩
    · rintro x ⟨hxA, hxB⟩
      obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex A hxA
      have hsB := mem_faces_of_mem_openSimplex_of_mem_space hBR (hAR hs) hxs hxB
      exact I.convexHull_subset_space ((hfaces s).mpr ⟨hs, hsB⟩)
        (openSimplex_subset_convexHull _ hxs)
  have hIball : IsPLBall n I.space := hspace.symm ▸ hI
  have hfacet (s : Finset E) (hs : s ∈ I.faces) (hsc : s.card = n + 1) :
      s ∈ (boundaryComplex (n + 1) A).faces := by
    obtain ⟨hsA, hsB⟩ := (hfaces s).mp hs
    obtain ⟨u, hu, hsu, huc⟩ := exists_face_superset_card_eq_of_isPLBall B hB hsB
    obtain ⟨b, hbs, hub⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsu, by omega⟩
    have hbB : insert b s ∈ B.faces := hub.symm ▸ hu
    have hbA : insert b s ∉ A.faces := by
      intro hb
      have hc := card_le_of_isPLBall I hIball ((hfaces _).mpr ⟨hb, hbB⟩)
      rw [Finset.card_insert_of_notMem hbs, hsc] at hc
      omega
    apply (hA.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface A hsc).mpr
    rcases hA.isCombinatorialManifoldWithBoundary.codimension_one_cofaces A hsA hsc with
      h | ⟨a, c, hac, hAc⟩
    · exact h
    · have ha : a ∉ s ∧ insert a s ∈ A.faces := by
        change a ∈ {w | w ∉ s ∧ insert w s ∈ A.faces}
        rw [hAc]
        exact mem_insert _ _
      have hc : c ∉ s ∧ insert c s ∈ A.faces := by
        change c ∈ {w | w ∉ s ∧ insert w s ∈ A.faces}
        rw [hAc]
        exact mem_insert_of_mem _ (mem_singleton _)
      have hba : b ≠ a := fun heq => hbA (heq.symm ▸ ha.2)
      have hbc : b ≠ c := fun heq => hbA (heq.symm ▸ hc.2)
      have haR : a ∈ {w | w ∉ s ∧ insert w s ∈ R.faces} := ⟨ha.1, hAR ha.2⟩
      have hcR : c ∈ {w | w ∉ s ∧ insert w s ∈ R.faces} := ⟨hc.1, hAR hc.2⟩
      have hbR : b ∈ {w | w ∉ s ∧ insert w s ∈ R.faces} := ⟨hbs, hBR hbB⟩
      rcases hR.codimension_one_cofaces R (hAR hsA) hsc with ⟨v, hv⟩ | ⟨v, w, -, hvw⟩
      · rw [hv] at haR hcR
        exact (hac (haR.trans hcR.symm)).elim
      · simp only [hvw, mem_insert_iff, mem_singleton_iff] at haR hcR hbR
        rcases haR with rfl | rfl <;> rcases hcR with rfl | rfl <;>
          rcases hbR with rfl | rfl <;> contradiction
  intro x hx
  obtain ⟨s, hs, hxs⟩ := I.mem_space_iff.mp (hspace.symm ▸ hx)
  obtain ⟨t, ht, hst, htc⟩ := exists_face_superset_card_eq_of_isPLBall I hIball hs
  exact (boundaryComplex (n + 1) A).convexHull_subset_space (hfacet t ht htc)
    (convexHull_mono (Finset.coe_subset.mpr hst) hxs)

open Classical in
theorem isPLBall_union_of_subcomplexes_inter_isPLBall_two
    (R A B : Geometry.SimplicialComplex ℝ E)
    [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hA : IsPLBall 3 A.space) (hB : IsPLBall 3 B.space)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces)
    (hI : IsPLBall 2 (A.space ∩ B.space)) : IsPLBall 3 (A.space ∪ B.space) := by
  apply isPLBall_union_of_boundary_disk A B hA hB hI
  · exact inter_subset_boundaryComplex_of_isPLBall R A B hR hA hB hAR hBR hI
  · rw [inter_comm] at hI ⊢
    exact inter_subset_boundaryComplex_of_isPLBall R B A hR hB hA hBR hAR hI

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_of_inter_isPLBall_two
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {C D : Set E}
    (hC : IsPLBall 3 C) (hD : IsPLBall 3 D) (hCK : C ⊆ K.space) (hDK : D ⊆ K.space)
    (hI : IsPLBall 2 (C ∩ D)) : IsPLBall 3 (C ∪ D) := by
  classical
  obtain ⟨R, hR, hfin, hcover⟩ := exists_isSubdivision_subcomplexes K
    (fun b : Bool => if b then C else D)
    (fun b => by
      cases b with
      | false => exact hD.isPolyhedron
      | true => exact hC.isPolyhedron)
    (fun b => by
      cases b with
      | false => exact hDK
      | true => exact hCK)
  let _ : Finite R.faces := hfin.to_subtype
  let A := restrict R C
  let B := restrict R D
  let _ : Finite A.faces := (restrict_faces_finite R C).to_subtype
  let _ : Finite B.faces := (restrict_faces_finite R D).to_subtype
  have hA : A.space = C := restrict_space_of_eq_biUnion R C (by simpa using hcover true)
  have hB : B.space = D := restrict_space_of_eq_biUnion R D (by simpa using hcover false)
  rw [← hA] at hC
  rw [← hB] at hD
  rw [← hA, ← hB] at hI ⊢
  exact isPLBall_union_of_subcomplexes_inter_isPLBall_two R A B (hK.of_isSubdivision hR)
    hC hD (restrict_faces_subset R C) (restrict_faces_subset R D) hI

theorem IsCombinatorialManifoldWithBoundary.isPLBall_union_iUnion_of_pairwiseDisjoint
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {ι : Type*} {C : Set E}
    (hC : IsPLBall 3 C) (hCK : C ⊆ K.space)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 3 (A i))
    (hAK : ∀ i ∈ d, A i ⊆ K.space) (hI : ∀ i ∈ d, IsPLBall 2 (C ∩ A i))
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (A i) (A j)) :
    IsPLBall 3 (C ∪ ⋃ i ∈ d, A i) := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hC
  | @insert i d hi ih =>
    have hA' : ∀ j ∈ d, IsPLBall 3 (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hAK' : ∀ j ∈ d, A j ⊆ K.space := fun j hj => hAK j (Finset.mem_insert_of_mem hj)
    have hI' : ∀ j ∈ d, IsPLBall 2 (C ∩ A j) := fun j hj => hI j (Finset.mem_insert_of_mem hj)
    have hdis' : ∀ j ∈ d, ∀ k ∈ d, j ≠ k → Disjoint (A j) (A k) :=
      fun j hj k hk hjk => hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    have hprev := ih hA' hAK' hI' hdis'
    have hprevK : (C ∪ ⋃ j ∈ d, A j) ⊆ K.space :=
      union_subset hCK (iUnion₂_subset hAK')
    have hinter : (C ∪ ⋃ j ∈ d, A j) ∩ A i = C ∩ A i := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxi⟩
        · exact ⟨hx, hxi⟩
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact ((hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
            (ne_of_mem_of_not_mem hj hi)).le_bot ⟨hxj, hxi⟩).elim
      · rintro x ⟨hx, hxi⟩
        exact ⟨Or.inl hx, hxi⟩
    have h := hK.isPLBall_union_of_inter_isPLBall_two hprev
      (hA i (Finset.mem_insert_self _ _)) hprevK (hAK i (Finset.mem_insert_self _ _))
      (hinter.symm ▸ hI i (Finset.mem_insert_self _ _))
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.inter_subset_boundaryComplex_of_isPLBall
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces]
    (hA : IsPLBall (n + 1) A.space) (hAK : A.space ⊆ K.space)
    {D : Set E} (hD : IsPLBall (n + 1) D) (hDK : D ⊆ K.space)
    (hI : IsPLBall n (A.space ∩ D)) :
    A.space ∩ D ⊆ (boundaryComplex (n + 1) A).space := by
  classical
  obtain ⟨R, hR, hfin, hcover⟩ := exists_isSubdivision_subcomplexes K
    (fun b : Bool => if b then A.space else D)
    (fun b => by cases b with
      | false => exact hD.isPolyhedron
      | true => exact hA.isPolyhedron)
    (fun b => by cases b with
      | false => exact hDK
      | true => exact hAK)
  let _ : Finite R.faces := hfin.to_subtype
  let A' := restrict R A.space
  let B' := restrict R D
  let _ : Finite A'.faces := (restrict_faces_finite R A.space).to_subtype
  let _ : Finite B'.faces := (restrict_faces_finite R D).to_subtype
  have hA' : A'.space = A.space := restrict_space_of_eq_biUnion R A.space
    (by simpa using hcover true)
  have hB' : B'.space = D := restrict_space_of_eq_biUnion R D (by simpa using hcover false)
  have hI' : IsPLBall n (A'.space ∩ B'.space) := by rwa [hA', hB']
  have hsub := PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall R A' B' (hK.of_isSubdivision hR)
    (hA'.symm ▸ hA) (hB'.symm ▸ hD) (restrict_faces_subset R A.space)
    (restrict_faces_subset R D) hI'
  have hid : IsPLHomeomorphOn (id : E → E) A.space A'.space := by
    rw [hA']
    exact hA.isPolyhedron.isPLHomeomorphOn_id
  have hbd := boundaryComplex_space_of_isPLHomeomorphOn A A'
    hA.isCombinatorialManifoldWithBoundary hid
  rw [image_id] at hbd
  rwa [hA', hB', hbd] at hsub
end DifferentialGeometry.Topology.PiecewiseLinear
