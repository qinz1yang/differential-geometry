/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.closure_sdiff_eq_of_inter_isPLBall {n m : ℕ} {A B : Set E}
    (hA : IsPLBall (n + 1) A) (hI : IsPLBall m (A ∩ B)) (hm : m < n + 1) :
    closure (A \ B) = A := by
  have heq : A \ B = A \ (A ∩ B) := by ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
  rw [heq]
  exact hA.closure_sdiff_eq_of_isPLBall hI inter_subset_left hm

open Classical in
theorem boundary_contact_after_ball_deletion
    (K C R Z : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite C.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hC : IsPLBall 3 C.space)
    (hZ : IsPLBall 3 Z.space) (hCK : C.space ⊆ K.space) (hZK : Z.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary 3 R)
    (hRspace : R.space = closure (K.space \ C.space))
    (hZB : IsPLBall 2 (Z.space ∩ (boundaryComplex 3 K).space))
    (hI : Disjoint Z.space C.space ∨
      IsPLBall 2 (Z.space ∩ C.space) ∧
        IsPLBall 1 (Z.space ∩ C.space ∩ (boundaryComplex 3 K).space)) :
    Z.space ⊆ R.space ∧ Z.space ∩ (boundaryComplex 3 R).space =
      (Z.space ∩ (boundaryComplex 3 K).space) ∪ (Z.space ∩ C.space) := by
  have hbd := boundaryComplex_space_of_closure_sdiff K C R hK
    hC.isCombinatorialManifoldWithBoundary hCK hR hRspace
  have hclosedK : IsClosed (boundaryComplex 3 K).space :=
    let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
    (isPolyhedron_space (boundaryComplex 3 K)).isClosed
  have hclosedC : IsClosed (boundaryComplex 3 C).space :=
    let _ : Finite (boundaryComplex 3 C).faces := (boundaryComplex_faces_finite 3 C).to_subtype
    (isPolyhedron_space (boundaryComplex 3 C)).isClosed
  have hsubK : closure ((boundaryComplex 3 K).space \ C.space) ⊆
      (boundaryComplex 3 K).space := closure_minimal sdiff_subset hclosedK
  have hsubC : closure ((boundaryComplex 3 C).space \ (boundaryComplex 3 K).space) ⊆ C.space :=
    (closure_minimal sdiff_subset hclosedC).trans (boundaryComplex_space_subset 3 C)
  have hleft : Z.space ∩ (boundaryComplex 3 R).space ⊆
      (Z.space ∩ (boundaryComplex 3 K).space) ∪ (Z.space ∩ C.space) := by
    rw [hbd]
    rintro x ⟨hxZ, hx | hx⟩
    · exact Or.inl ⟨hxZ, hsubK hx⟩
    · exact Or.inr ⟨hxZ, hsubC hx⟩
  rcases hI with hdis | ⟨hI, hIB⟩
  · refine ⟨?_, Subset.antisymm hleft ?_⟩
    · rw [hRspace]
      exact fun x hx => subset_closure ⟨hZK hx, fun hxC => disjoint_left.mp hdis hx hxC⟩
    · rw [hbd]
      rintro x (⟨hxZ, hxB⟩ | ⟨hxZ, hxC⟩)
      · exact ⟨hxZ, Or.inl (subset_closure
          ⟨hxB, fun hxC => disjoint_left.mp hdis hxZ hxC⟩)⟩
      · exact (disjoint_left.mp hdis hxZ hxC).elim
  · have hZdense := hZ.closure_sdiff_eq_of_inter_isPLBall hI (by omega)
    have hZd : Z.space ⊆ R.space := by
      rw [hRspace, ← hZdense]
      exact closure_mono (sdiff_subset_sdiff_left hZK)
    have hIdC : Z.space ∩ C.space ⊆ (boundaryComplex 3 C).space := by
      rw [inter_comm] at hI ⊢
      exact hK.inter_subset_boundaryComplex_of_isPLBall C hC hCK hZ hZK hI
    have hIdense := hI.closure_sdiff_eq_of_inter_isPLBall hIB (by omega)
    have hZIB : IsPLBall 1 ((Z.space ∩ (boundaryComplex 3 K).space) ∩ C.space) := by
      convert hIB using 1
      ext x
      simp only [mem_inter_iff]
      tauto
    have hBdense := hZB.closure_sdiff_eq_of_inter_isPLBall hZIB (by omega)
    refine ⟨hZd, Subset.antisymm hleft ?_⟩
    rw [hbd]
    rintro x (hxB | hxI)
    · refine ⟨hxB.1, Or.inl ?_⟩
      have hsub : Z.space ∩ (boundaryComplex 3 K).space ⊆
          closure ((boundaryComplex 3 K).space \ C.space) := by
        rw [← hBdense]
        exact closure_mono (sdiff_subset_sdiff_left inter_subset_right)
      exact hsub hxB
    · refine ⟨hxI.1, Or.inr ?_⟩
      have hsub : Z.space ∩ C.space ⊆
          closure ((boundaryComplex 3 C).space \ (boundaryComplex 3 K).space) := by
        rw [← hIdense]
        exact closure_mono (sdiff_subset_sdiff_left hIdC)
      exact hsub hxI

open Classical in
theorem isPLBall_boundary_contact_union_of_ball_family
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {ι : Type*}
    (C : ι → Geometry.SimplicialComplex ℝ E) [∀ i, Finite (C i).faces]
    (hC : ∀ i, IsPLBall 3 (C i).space) (hCK : ∀ i, (C i).space ⊆ K.space)
    (hB : ∀ i, IsPLBall 2 ((C i).space ∩ (boundaryComplex 3 K).space))
    (hI : ∀ i j, i ≠ j → Disjoint (C i).space (C j).space ∨
      IsPLBall 2 ((C i).space ∩ (C j).space) ∧
        IsPLBall 1 ((C i).space ∩ (C j).space ∩ (boundaryComplex 3 K).space))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (C i).space ∩ (C j).space ∩ (C k).space = ∅)
    (d : Finset ι) {i : ι} (hi : i ∉ d) :
    IsPLBall 2 (((C i).space ∩ (boundaryComplex 3 K).space) ∪
      ⋃ j ∈ d, (C i).space ∩ (C j).space) := by
  classical
  let a := d.filter fun j => ¬Disjoint (C i).space (C j).space
  let S := boundaryComplex 3 (C i)
  let A := (C i).space ∩ (boundaryComplex 3 K).space
  let D := fun j => (C i).space ∩ (C j).space
  let _ : Finite S.faces := (boundaryComplex_faces_finite 3 (C i)).to_subtype
  have hne (j : ι) (hj : j ∈ d) : i ≠ j := fun hij => hi (hij ▸ hj)
  have hpair (j : ι) (hj : j ∈ a) :
      IsPLBall 2 (D j) ∧ IsPLBall 1 (D j ∩ (boundaryComplex 3 K).space) :=
    (hI i j (hne j (Finset.mem_filter.mp hj).1)).resolve_left (Finset.mem_filter.mp hj).2
  have hAB : A ⊆ S.space := inter_boundaryComplex_space_subset_of_subset K (C i) hK
    (hC i).isCombinatorialManifoldWithBoundary (hCK i)
  have hDB (j : ι) (hj : j ∈ a) : D j ⊆ S.space :=
    hK.inter_subset_boundaryComplex_of_isPLBall (C i) (hC i) (hCK i)
      (hC j) (hCK j) (hpair j hj).1
  have hDI (j : ι) (hj : j ∈ a) : IsPLBall 1 (A ∩ D j) := by
    convert (hpair j hj).2 using 1
    ext x
    simp only [A, D, mem_inter_iff]
    tauto
  have hdis (j : ι) (hj : j ∈ a) (k : ι) (hk : k ∈ a) (hjk : j ≠ k) :
      Disjoint (D j) (D k) := by
    apply disjoint_left.mpr
    rintro x ⟨hxC, hxj⟩ ⟨-, hxk⟩
    have hx : x ∈ (C i).space ∩ (C j).space ∩ (C k).space := ⟨⟨hxC, hxj⟩, hxk⟩
    rw [htriple i j k (hne j (Finset.mem_filter.mp hj).1)
      (hne k (Finset.mem_filter.mp hk).1) hjk] at hx
    exact hx
  have heq : (⋃ j ∈ a, D j) = ⋃ j ∈ d, D j := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun j hj => subset_iUnion₂_of_subset j
        (Finset.mem_filter.mp hj).1 subset_rfl
    · rintro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr
        ⟨hj, fun hdis => disjoint_left.mp hdis hxj.1 hxj.2⟩, hxj⟩
  have hS₀ : IsCombinatorialManifold 2 S :=
    isCombinatorialManifold_boundaryComplex (C i) (hC i).isCombinatorialManifoldWithBoundary
  have hS := hS₀.isCombinatorialManifoldWithBoundary
  have h := hS.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface (hB i) hAB a D
    (fun j hj => (hpair j hj).1) hDB hDI hdis
  rwa [heq] at h

open Classical in
theorem exists_isPLBall_complement_of_finite_boundary_ball_family
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {ι : Type*} (C : ι → Geometry.SimplicialComplex ℝ E) [∀ i, Finite (C i).faces]
    (hC : ∀ i, IsPLBall 3 (C i).space) (hCK : ∀ i, (C i).space ⊆ K.space)
    (hB : ∀ i, IsPLBall 2 ((C i).space ∩ (boundaryComplex 3 K).space))
    (hI : ∀ i j, i ≠ j → Disjoint (C i).space (C j).space ∨
      IsPLBall 2 ((C i).space ∩ (C j).space) ∧
        IsPLBall 1 ((C i).space ∩ (C j).space ∩ (boundaryComplex 3 K).space))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (C i).space ∩ (C j).space ∩ (C k).space = ∅) (d : Finset ι) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧ IsPLBall 3 R.space ∧
      R.space = closure (K.space \ ⋃ i ∈ d, (C i).space) ∧
      ∀ i ∉ d, (C i).space ⊆ R.space ∧
        (C i).space ∩ (boundaryComplex 3 R).space =
          ((C i).space ∩ (boundaryComplex 3 K).space) ∪
            ⋃ j ∈ d, (C i).space ∩ (C j).space := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      refine ⟨K, Set.toFinite K.faces, hK, ?_, fun i _ => ⟨hCK i, ?_⟩⟩
      · simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty]
        exact hK.isPolyhedron.isClosed.closure_eq.symm
      · simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
  | @insert a d had ih =>
      obtain ⟨R, hRfin, hR, hRspace, hcontacts⟩ := ih
      let _ : Finite R.faces := hRfin.to_subtype
      have haR := (hcontacts a had).1
      have haB : IsPLBall 2 ((C a).space ∩ (boundaryComplex 3 R).space) := by
        rw [(hcontacts a had).2]
        exact isPLBall_boundary_contact_union_of_ball_family K
          hK.isCombinatorialManifoldWithBoundary C hC hCK hB hI htriple d had
      have hball := isPLBall_closure_sdiff_of_boundary_disk R hR (hC a) haR haB
      obtain ⟨S, hSfin, hSspace⟩ := hball.isPolyhedron.exists_simplicialComplex
      let _ : Finite S.faces := hSfin.to_subtype
      have hS : IsPLBall 3 S.space := hSspace.symm ▸ hball
      have hspace : S.space = closure (K.space \ ⋃ i ∈ insert a d, (C i).space) := by
        rw [hSspace, hRspace]
        have hclose : closure (closure (K.space \ ⋃ i ∈ d, (C i).space) \ (C a).space) =
            closure ((K.space \ ⋃ i ∈ d, (C i).space) \ (C a).space) := by
          apply Subset.antisymm
          · apply closure_minimal
            · intro x hx
              have hx' := (hC a).isPolyhedron.isClosed.isOpen_compl.inter_closure
                ⟨hx.2, hx.1⟩
              simpa only [sdiff_eq, inter_comm] using hx'
            · exact isClosed_closure
          · exact closure_mono (sdiff_subset_sdiff_left subset_closure)
        rw [hclose]
        congr 1
        ext x
        simp only [mem_sdiff, mem_iUnion, Finset.mem_insert]
        aesop
      refine ⟨S, hSfin, hS, hspace, fun i hi => ?_⟩
      have hid : i ∉ d := fun hid => hi (Finset.mem_insert_of_mem hid)
      have hia : i ≠ a := fun hia => hi (hia ▸ Finset.mem_insert_self a d)
      have hpair : Disjoint (C i).space (C a).space ∨
          IsPLBall 2 ((C i).space ∩ (C a).space) ∧
            IsPLBall 1 ((C i).space ∩ (C a).space ∩ (boundaryComplex 3 R).space) := by
        rcases hI i a hia with hdis | ⟨hIa, hIaB⟩
        · exact Or.inl hdis
        · refine Or.inr ⟨hIa, ?_⟩
          have heq : (C i).space ∩ (C a).space ∩ (boundaryComplex 3 R).space =
              (C i).space ∩ (C a).space ∩ (boundaryComplex 3 K).space := by
            ext x
            constructor
            · rintro ⟨⟨hxi, hxa⟩, hxR⟩
              rcases (hcontacts i hid).2.subset ⟨hxi, hxR⟩ with hx | hx
              · exact ⟨⟨hxi, hxa⟩, hx.2⟩
              · obtain ⟨j, hj, hxij⟩ := mem_iUnion₂.mp hx
                have hx : x ∈ (C i).space ∩ (C a).space ∩ (C j).space :=
                  ⟨⟨hxi, hxa⟩, hxij.2⟩
                rw [htriple i a j hia (fun hij => hid (hij ▸ hj))
                  (fun haj => had (haj ▸ hj))] at hx
                exact hx.elim
            · rintro ⟨⟨hxi, hxa⟩, hxK⟩
              exact ⟨⟨hxi, hxa⟩, ((hcontacts i hid).2.symm.subset (Or.inl ⟨hxi, hxK⟩)).2⟩
          rw [heq]
          exact hIaB
      have hiB : IsPLBall 2 ((C i).space ∩ (boundaryComplex 3 R).space) := by
        rw [(hcontacts i hid).2]
        exact isPLBall_boundary_contact_union_of_ball_family K
          hK.isCombinatorialManifoldWithBoundary C hC hCK hB hI htriple d hid
      obtain ⟨hiS, hiB⟩ := boundary_contact_after_ball_deletion R (C a) S (C i)
        hR.isCombinatorialManifoldWithBoundary (hC a) (hC i) haR (hcontacts i hid).1
        hS.isCombinatorialManifoldWithBoundary hSspace hiB hpair
      refine ⟨hiS, ?_⟩
      rw [hiB, (hcontacts i hid).2]
      simp only [Finset.set_biUnion_insert]
      ac_rfl

end DifferentialGeometry.Topology.PiecewiseLinear
