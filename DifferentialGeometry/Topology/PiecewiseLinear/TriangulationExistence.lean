/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartGlue

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPiece.exists_union_chart [T2Space X] [HasGroupoid X (plGroupoid n)] {Y : Set X}
    (T : PLPiece n X Y) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) : Nonempty (PLPiece n X (Y ∪ e.symm '' C)) := by
  obtain ⟨T'⟩ := T.piece.exists_glue_chart e he hC hCe
  exact T'.exists_pLPiece

theorem exists_pLPiece_biUnion [T2Space X] [Nonempty X] [HasGroupoid X (plGroupoid n)]
    (V : X → Set X)
    (hV : ∀ x, ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope C ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∧
      V x = (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C)
    (t : Finset X) : Nonempty (PLPiece n X (⋃ x ∈ t, V x)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hempty : (⋃ x ∈ (∅ : Finset X), V x) = ∅ := by simp
    rw [hempty]
    exact ⟨⟨0, PLPieceIn.empty _⟩⟩
  | @insert a t _ ih =>
    obtain ⟨T⟩ := ih
    obtain ⟨C, hC, hCe, hVa⟩ := hV a
    obtain ⟨T'⟩ := T.exists_union_chart _ (chart_mem_atlas _ a) hC hCe
    rw [Finset.set_biUnion_insert, union_comm, hVa]
    exact ⟨T'⟩

theorem exists_pLPiece_univ [CompactSpace X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid n)] : Nonempty (PLPiece n X univ) := by
  classical
  choose C hC hCe hCnhds using exists_isHPolytope_image_symm_mem_nhds (n := n) (X := X)
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x) fun x _ => hCnhds x
  obtain ⟨T⟩ := exists_pLPiece_biUnion
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x)
    (fun x => ⟨C x, hC x, hCe x, rfl⟩) t
  have huniv : (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x) = univ :=
    eq_univ_of_univ_subset hcover
  rw [huniv] at T
  exact ⟨T⟩

theorem exists_pLTriangulation [CompactSpace X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid n)] : Nonempty (PLTriangulation n X) := by
  obtain ⟨T⟩ := exists_pLPiece_univ (n := n) (X := X)
  exact ⟨T.toPLTriangulation⟩

end DifferentialGeometry.Topology.PiecewiseLinear
