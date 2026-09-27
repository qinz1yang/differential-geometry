/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceIntersectionBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U)

theorem LocallyFinitePLPieceIn.isPLBall_union_of_inter_isPLBall_two
    {A B : Set E} (hA : IsPLBall 3 A) (hB : IsPLBall 3 B)
    (hAK : A ⊆ T.complex.space) (hBK : B ⊆ T.complex.space)
    (hI : IsPLBall 2 (A ∩ B)) : IsPLBall 3 (A ∪ B) := by
  classical
  obtain ⟨K, hKfin, hKA⟩ := hA.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hIK : A ∩ B ⊆ (boundaryComplex 3 K).space :=
    T.inter_subset_boundaryComplex_of_isPLBall K hKA hA hB hAK hBK hI
  have hIL : A ∩ B ⊆ (boundaryComplex 3 L).space := by
    have h := T.inter_subset_boundaryComplex_of_isPLBall L hLB hB hA hBK hAK
      (show IsPLBall 2 (B ∩ A) by simpa only [inter_comm] using hI)
    simpa only [inter_comm] using h
  rw [← hKA, ← hLB] at hI hIK hIL ⊢
  exact isPLBall_union_of_boundary_disk K L (hKA.symm ▸ hA) (hLB.symm ▸ hB) hI hIK hIL

theorem LocallyFinitePLPieceIn.isPLBall_union_iUnion_of_disk_intersections
    {ι : Type*} {R : Set E} (hR : IsPLBall 3 R)
    (s : Finset ι) (A : ι → Set E) (hRK : R ⊆ T.complex.space)
    (hA : ∀ i ∈ s, IsPLBall 3 (A i)) (hAK : ∀ i ∈ s, A i ⊆ T.complex.space)
    (hAR : ∀ i ∈ s, IsPLBall 2 (A i ∩ R))
    (hAA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (A i ∩ A j).Nonempty → IsPLBall 2 (A i ∩ A j))
    (hARA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (A i ∩ A j).Nonempty → IsPLBall 1 ((A i ∩ R) ∩ A j))
    (htriple : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
      i ≠ j → i ≠ k → j ≠ k → (A i ∩ A j) ∩ A k = ∅) :
    IsPLBall 3 (R ∪ ⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hR
  | @insert i s hi ih =>
    have hm (j : ι) (hj : j ∈ s) : j ∈ insert i s := Finset.mem_insert_of_mem hj
    have hi' : i ∈ insert i s := Finset.mem_insert_self _ _
    have hij (j : ι) (hj : j ∈ s) : i ≠ j := fun h => hi (h.symm ▸ hj)
    have hprev := ih (fun j hj => hA j (hm j hj)) (fun j hj => hAK j (hm j hj))
      (fun j hj => hAR j (hm j hj))
      (fun j hj k hk hne => hAA j (hm j hj) k (hm k hk) hne)
      (fun j hj k hk hne => hARA j (hm j hj) k (hm k hk) hne)
      (fun j hj k hk l hl hjk hjl hkl =>
        htriple j (hm j hj) k (hm k hk) l (hm l hl) hjk hjl hkl)
    have hprevK : (R ∪ ⋃ j ∈ s, A j) ⊆ T.complex.space :=
      union_subset hRK (iUnion₂_subset fun j hj => hAK j (hm j hj))
    obtain ⟨K, hKfin, hKA⟩ := (hA i hi').isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hKfin.to_subtype
    let L := boundaryComplex 3 K
    let _ : Finite L.faces := (boundaryComplex_faces_finite 3 K).to_subtype
    have hLSphere : IsPLSphere 2 L.space :=
      isPLSphere_boundaryComplex_space_of_isPLBall K (hKA.symm ▸ hA i hi')
    have hL : IsCombinatorialManifoldWithBoundary 2 L :=
      (IsPLSphere.isCombinatorialManifold (n := 1) hLSphere).isCombinatorialManifoldWithBoundary
    have hPL : A i ∩ R ⊆ L.space :=
      T.inter_subset_boundaryComplex_of_isPLBall K hKA (hA i hi') hR (hAK i hi') hRK
        (hAR i hi')
    let D : ι → Set E := fun j => A i ∩ A j
    let d := s.filter fun j => (D j).Nonempty
    have hd (j : ι) (hj : j ∈ d) : j ∈ s ∧ (D j).Nonempty := Finset.mem_filter.mp hj
    have hD (j : ι) (hj : j ∈ d) : IsPLBall 2 (D j) :=
      hAA i hi' j (hm j (hd j hj).1) (hij j (hd j hj).1) (hd j hj).2
    have hDL (j : ι) (hj : j ∈ d) : D j ⊆ L.space :=
      T.inter_subset_boundaryComplex_of_isPLBall K hKA (hA i hi')
        (hA j (hm j (hd j hj).1)) (hAK i hi') (hAK j (hm j (hd j hj).1)) (hD j hj)
    have hPD (j : ι) (hj : j ∈ d) : IsPLBall 1 ((A i ∩ R) ∩ D j) := by
      have heq : (A i ∩ R) ∩ D j = (A i ∩ R) ∩ A j := by
        ext x
        simp only [D, mem_inter_iff]
        tauto
      rw [heq]
      exact hARA i hi' j (hm j (hd j hj).1) (hij j (hd j hj).1) (hd j hj).2
    have hdis (j : ι) (hj : j ∈ d) (k : ι) (hk : k ∈ d) (hjk : j ≠ k) :
        Disjoint (D j) (D k) := by
      apply disjoint_left.mpr
      intro x hxj hxk
      exact (eq_empty_iff_forall_notMem.mp
        (htriple i hi' j (hm j (hd j hj).1) k (hm k (hd k hk).1)
          (hij j (hd j hj).1) (hij k (hd k hk).1) hjk)) x ⟨hxj, hxk.2⟩
    have hattach := hL.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface
      (hAR i hi') hPL d D hD hDL hPD hdis
    have hDU : (⋃ j ∈ d, D j) = ⋃ j ∈ s, D j := by
      ext x
      constructor
      · rintro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨j, (hd j hj).1, hxj⟩
      · rintro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, x, hxj⟩, hxj⟩
    rw [hDU] at hattach
    have hmeet : IsPLBall 2 (A i ∩ (R ∪ ⋃ j ∈ s, A j)) := by
      simpa only [inter_union_distrib_left, inter_iUnion, D] using hattach
    have hball := T.isPLBall_union_of_inter_isPLBall_two (hA i hi') hprev
      (hAK i hi') hprevK hmeet
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using hball

end DifferentialGeometry.Topology.PiecewiseLinear
