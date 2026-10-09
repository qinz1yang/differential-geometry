/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteCollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem inter_interior_eq_inter_interior_of_inter_eq {Y : Type*} [TopologicalSpace Y]
    {O A B : Set Y} (hO : IsOpen O) (h : O ∩ A = O ∩ B) :
    O ∩ interior A = O ∩ interior B := by
  have key : ∀ C D : Set Y, O ∩ C = O ∩ D → O ∩ interior C ⊆ O ∩ interior D := by
    intro C D hCD
    refine subset_inter inter_subset_left (interior_maximal ?_ (hO.inter isOpen_interior))
    intro y hy
    have hyC : y ∈ O ∩ C := ⟨hy.1, interior_subset hy.2⟩
    rw [hCD] at hyC
    exact hyC.2
  exact Subset.antisymm (key A B h) (key B A h.symm)

theorem isCombinatorialManifoldWithBoundary_bot {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (m : ℕ) :
    IsCombinatorialManifoldWithBoundary m (⊥ : Geometry.SimplicialComplex ℝ E) := by
  cases m with
  | zero => exact fun _ hv => False.elim hv
  | succ k => exact fun _ hv => False.elim hv

section Empty

variable {n m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [Nonempty X]

theorem isLocallyFinitePolyhedralManifoldWithBoundary_empty :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m (∅ : Set X) := by
  refine (isPolyhedralManifoldWithBoundary_of_pieceIn
    (PLPieceIn.empty (n := n) (X := X) (EuclideanSpace ℝ (Fin 0))) ?_).isLocallyFinite
  exact isCombinatorialManifoldWithBoundary_bot m

theorem isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_of_isOpen {K : Set X}
    (hK : IsOpen K) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m (K \ interior K) := by
  rw [hK.interior_eq, Set.sdiff_self]
  exact isLocallyFinitePolyhedralManifoldWithBoundary_empty

end Empty

section Tower

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}

theorem LocallyFinitePieceTower.subset_interior_union_compl (T : LocallyFinitePieceTower n X U)
    (i : ℕ) : T.N i ⊆ interior (T.N (i + 1) ∪ Uᶜ) := by
  intro x hx
  obtain ⟨V, hV, hVN⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (T.subset_nhdsWithin i x hx)
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset hV fun y hy => ?_
  by_cases hyU : y ∈ U
  · exact Or.inl (hVN ⟨hy, hyU⟩)
  · exact Or.inr hyU

end Tower

section Frontier

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

namespace IsPolyhedralManifoldWithBoundary

theorem isLocallyFinite_sdiff_interior {K : Set X}
    (hK : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) m (K \ interior K) := by
  have hcl : IsClosed K := hK.isCompact.isClosed
  rw [← hcl.frontier_eq]
  exact hK.isPolyhedralManifold_frontier.isPolyhedralManifoldWithBoundary.isLocallyFinite

end IsPolyhedralManifoldWithBoundary

namespace IsLocallyFinitePolyhedralManifoldWithBoundary

omit [T2Space X] in
theorem exists_isOpen_inter_eq_of_isCompact {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {C : Set X}
    (hC : IsCompact C) (hCK : C ⊆ K) :
    ∃ O : Set X, IsOpen O ∧ C ⊆ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧ O ∩ K = O ∩ P := by
  obtain ⟨T, hT⟩ := hK
  obtain ⟨j, hj⟩ := T.exists_core_of_isCompact hC hCK
  refine ⟨interior (T.N (j + 1) ∪ Kᶜ), isOpen_interior, ?_, T.N (j + 1),
    ⟨T.piece (j + 1), hT (j + 1)⟩, T.subset (j + 1), ?_⟩
  · intro x hx
    exact T.subset_interior_union_compl j (T.core_space_subset j (hj hx))
  · refine Subset.antisymm (fun y hy => ⟨hy.1, ?_⟩) fun y hy => ⟨hy.1, T.subset (j + 1) hy.2⟩
    rcases interior_subset hy.1 with h | h
    · exact h
    · exact absurd hy.2 h

theorem exists_isOpen_inter_sdiff_interior_eq_of_isCompact {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {C : Set X}
    (hC : IsCompact C) (hCK : C ⊆ K) :
    ∃ O : Set X, IsOpen O ∧ C ⊆ O ∧ ∃ S : Set X, IsPolyhedralManifold (n := m + 1) m S ∧
      O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨O, hO, hCO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq_of_isCompact hC hCK
  refine ⟨O, hO, hCO, frontier P, hP.isPolyhedralManifold_frontier, ?_⟩
  have hint := inter_interior_eq_inter_interior_of_inter_eq hO hOP
  have hKP : ∀ y ∈ O, (y ∈ K ↔ y ∈ P) := fun y hy =>
    ⟨fun hyK => (hOP.subset ⟨hy, hyK⟩).2, fun hyP => (hOP.symm.subset ⟨hy, hyP⟩).2⟩
  have hIP : ∀ y ∈ O, (y ∈ interior K ↔ y ∈ interior P) := fun y hy =>
    ⟨fun hyK => (hint.subset ⟨hy, hyK⟩).2, fun hyP => (hint.symm.subset ⟨hy, hyP⟩).2⟩
  rw [hP.isCompact.isClosed.frontier_eq]
  ext y
  simp only [mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨hyO, hyK, hyni⟩
    exact ⟨hyO, (hKP y hyO).mp hyK, fun hyi => hyni ((hIP y hyO).mpr hyi)⟩
  · rintro ⟨hyO, hyP, hyni⟩
    exact ⟨hyO, (hKP y hyO).mpr hyP, fun hyi => hyni ((hIP y hyO).mp hyi)⟩

theorem exists_isCompact_exhaustion_sdiff_interior {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    ∃ A : ℕ → Set X, Monotone A ∧ (∀ i, IsCompact (A i)) ∧ ⋃ i, A i = K \ interior K ∧
      (∀ i, ∀ x ∈ A i, A (i + 1) ∈ 𝓝[K \ interior K] x) ∧
        ∀ i, ∃ O : Set X, IsOpen O ∧ A i ⊆ O ∧ ∃ S : Set X,
          IsPolyhedralManifold (n := m + 1) m S ∧ A i ⊆ S ∧
            O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨T, -⟩ := id hK
  refine ⟨fun i => T.N i \ interior K, fun i j hij => Set.sdiff_subset_sdiff_left (T.monotone hij),
    fun i => (T.isCompact i).diff isOpen_interior, ?_, ?_, ?_⟩
  · ext y
    simp only [mem_iUnion, Set.mem_sdiff]
    constructor
    · rintro ⟨i, hy, hyi⟩
      exact ⟨T.subset i hy, hyi⟩
    · rintro ⟨hy, hyi⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hy)
      exact ⟨i, hi, hyi⟩
  · intro i x hx
    have h1 : T.N (i + 1) ∈ 𝓝[K \ interior K] x :=
      nhdsWithin_mono x Set.sdiff_subset (T.subset_nhdsWithin i x hx.1)
    refine Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) ?_
    rintro y ⟨hy, -, hyi⟩
    exact ⟨hy, hyi⟩
  · intro i
    obtain ⟨O, hO, hAO, S, hS, hOS⟩ :=
      hK.exists_isOpen_inter_sdiff_interior_eq_of_isCompact
        ((T.isCompact i).diff isOpen_interior) fun y hy => T.subset i hy.1
    exact ⟨O, hO, hAO, S, hS, fun y hy => (hOS.subset ⟨hAO hy, T.subset i hy.1, hy.2⟩).2, hOS⟩

end IsLocallyFinitePolyhedralManifoldWithBoundary

end Frontier

section Witness

theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_boundary_nonempty :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧
        (K \ interior K).Nonempty ∧
          IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 2 (K \ interior K) := by
  obtain ⟨K, hK, hfr⟩ := exists_isPolyhedralManifoldWithBoundary_frontier_nonempty
  have hcl : IsClosed K := hK.isCompact.isClosed
  refine ⟨K, hK.isLocallyFinite, ?_, hK.isLocallyFinite_sdiff_interior (m := 2)⟩
  rw [← hcl.frontier_eq]
  exact hfr

end Witness

end DifferentialGeometry.Topology.PiecewiseLinear
