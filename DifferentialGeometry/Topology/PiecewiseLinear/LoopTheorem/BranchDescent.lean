/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem natCard_subtype_add_natCard_subtype_not {α : Type*} [Finite α] (p : α → Prop) :
    Nat.card {a : α // p a} + Nat.card {a : α // ¬p a} = Nat.card α := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl p)

theorem natCard_subtype_notMem_add_card {α : Type*} [Finite α] (s : Finset α) :
    Nat.card {a : α // a ∉ s} + s.card = Nat.card α := by
  have hmem : Nat.card {a : α // a ∈ s} = s.card := Nat.card_eq_finsetCard s
  have hsplit := natCard_subtype_add_natCard_subtype_not fun a : α => a ∈ s
  rw [hmem] at hsplit
  omega

theorem natCard_lt_of_injective_of_notMem {α β : Type*} [Finite β] (f : α → β)
    (hf : Function.Injective f) {b : β} (hb : b ∉ Set.range f) :
    Nat.card α < Nat.card β := by
  have _hα : Finite α := Finite.of_injective f hf
  have _iα := Fintype.ofFinite α
  have _iβ := Fintype.ofFinite β
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hf hb

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

theorem finite_branch (T : NormalSingularSetTriangulation D BdM) : Finite T.Branch := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite T.complex.vertices :=
    (SimplicialComplex.finite_vertices T.complex).to_subtype
  infer_instance

theorem complexity_eq_natCard_branch (T : NormalSingularSetTriangulation D BdM) :
    T.complexity = Nat.card T.Branch := by
  let _ : Finite T.Branch := T.finite_branch
  simp only [complexity, closedBranchCount, boundaryBranchCount]
  rw [Nat.add_comm]
  exact natCard_subtype_add_natCard_subtype_not _

theorem complexity_lt_of_injective_origin (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (origin : T'.Branch → T.Branch) (hinj : Function.Injective origin)
    (hmiss : ∀ c', origin c' ≠ c) :
    T'.complexity < T.complexity := by
  let _ : Finite T.Branch := T.finite_branch
  rw [T.complexity_eq_natCard_branch, T'.complexity_eq_natCard_branch]
  refine natCard_lt_of_injective_of_notMem origin hinj (b := c) ?_
  rintro ⟨c', hc'⟩
  exact hmiss c' hc'

theorem complexity_add_card_eq_of_equiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (O : Finset T.Branch)
    (R : Finset T'.Branch) (e : {c' : T'.Branch // c' ∉ R} ≃ {c : T.Branch // c ∉ O}) :
    T'.complexity + O.card = T.complexity + R.card := by
  let _ : Finite T.Branch := T.finite_branch
  let _ : Finite T'.Branch := T'.finite_branch
  have hO := natCard_subtype_notMem_add_card O
  have hR := natCard_subtype_notMem_add_card R
  have he : Nat.card {c' : T'.Branch // c' ∉ R} = Nat.card {c : T.Branch // c ∉ O} :=
    Nat.card_congr e
  rw [T.complexity_eq_natCard_branch, T'.complexity_eq_natCard_branch]
  omega

theorem complexity_lt_of_card_lt_of_equiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') (O : Finset T.Branch)
    (R : Finset T'.Branch) (e : {c' : T'.Branch // c' ∉ R} ≃ {c : T.Branch // c ∉ O})
    (hcard : R.card < O.card) :
    T'.complexity < T.complexity := by
  have h := complexity_add_card_eq_of_equiv_compl T T' O R e
  omega

end NormalSingularSetTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
