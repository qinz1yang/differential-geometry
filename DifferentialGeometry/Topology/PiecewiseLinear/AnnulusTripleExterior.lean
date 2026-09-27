/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.UnboundedComplement
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_exterior_pair_of_annuli (h267 : Moise267) (M : Fin 3 → Set E3)
    {J₀ J₁ : Set E3} (hM : ∀ i, IsPLAnnulusWithEnds (M i) J₀ J₁)
    (hmeet : ∀ i j, i ≠ j → M i ∩ M j = J₀ ∪ J₁) :
    ∃ x, x ∉ ⋃ i, M i ∧ ¬ Bornology.IsBounded (connectedComponentIn (⋃ i, M i)ᶜ x) ∧
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        frontier (connectedComponentIn (⋃ i, M i)ᶜ x) = M i ∪ M j ∧
        ∀ y ∈ M k \ (J₀ ∪ J₁),
          Bornology.IsBounded (connectedComponentIn (M i ∪ M j)ᶜ y) := by
  choose K hKfin hK hKconn hspace hboundary using fun i => (hM i).exists_complex
  have hcompact : IsCompact (⋃ i, M i) := isCompact_iUnion fun i => by
    let _ : Finite (K i).faces := (hKfin i).to_subtype
    exact (hspace i) ▸ (isPolyhedron_space (K i)).isCompact
  obtain ⟨x, hx, hunbounded⟩ :=
    DifferentialGeometry.Topology.IsCompact.exists_not_isBounded_connectedComponentIn_compl
      hcompact (by rw [← Module.finrank_eq_rank']; simp)
  have hboundaryNe : (boundaryComplex 2 (K 0)).space.Nonempty := by
    rw [hboundary]
    obtain ⟨Q, ρ, hQ, -, h₀, -⟩ := hM 0
    rw [h₀]
    exact ((hQ.nonempty.prod (singleton_nonempty (0 : ℝ))).image ρ).mono subset_union_left
  have hdis (i j : Fin 3) (hij : i ≠ j) :
      Disjoint ((K i).space \ (boundaryComplex 2 (K i)).space)
        ((K j).space \ (boundaryComplex 2 (K j)).space) := by
    rw [hspace, hspace, hboundary, hboundary]
    exact disjoint_left.mpr fun _ hi hj => hi.2 ((hmeet i j hij).subset ⟨hi.1, hj.1⟩)
  have hunion : (⋃ i, (K i).space) = ⋃ i, M i := iUnion_congr hspace
  obtain ⟨i, j, k, hij, hik, hjk, hfront, hbounded⟩ :=
    h267 K hKfin hK hKconn (fun i j => (hboundary i).trans (hboundary j).symm)
      hboundaryNe hdis x (hunion ▸ hx) (hunion ▸ hunbounded)
  refine ⟨x, hx, hunbounded, i, j, k, hij, hik, hjk, ?_, ?_⟩
  · simpa only [hunion, hspace] using hfront
  · simpa only [hspace, hboundary] using hbounded

theorem IsPLAnnulusWithEnds.exists_exterior_complementary_annulus
    {C B₀ B₁ J₀ J₁ : Set E3} (hC : IsPLAnnulusWithEnds C J₀ J₁)
    (h267 : Moise267) (hB₀ : IsPLAnnulusWithEnds B₀ J₀ J₁)
    (hB₁ : IsPLAnnulusWithEnds B₁ J₀ J₁)
    (hC₀ : C ∩ B₀ = J₀ ∪ J₁) (hC₁ : C ∩ B₁ = J₀ ∪ J₁)
    (h₀₁ : B₀ ∩ B₁ = J₀ ∪ J₁) :
    let M : Fin 3 → Set E3 := ![C, B₀, B₁]
    ∃ (B : Set E3) (x : E3) (i j k : Fin 3),
      (B = B₀ ∨ B = B₁) ∧ (B = M i ∨ B = M j) ∧
      x ∉ ⋃ l, M l ∧ ¬ Bornology.IsBounded (connectedComponentIn (⋃ l, M l)ᶜ x) ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      frontier (connectedComponentIn (⋃ l, M l)ᶜ x) = M i ∪ M j ∧
      ∀ y ∈ M k \ (J₀ ∪ J₁),
        Bornology.IsBounded (connectedComponentIn (M i ∪ M j)ᶜ y) := by
  dsimp only
  let M : Fin 3 → Set E3 := ![C, B₀, B₁]
  have hM (i : Fin 3) : IsPLAnnulusWithEnds (M i) J₀ J₁ := by
    fin_cases i
    · exact hC
    · exact hB₀
    · exact hB₁
  have hmeet (i j : Fin 3) (hij : i ≠ j) : M i ∩ M j = J₀ ∪ J₁ := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hC₀
      | exact hC₁
      | exact h₀₁
      | exact (inter_comm _ _).trans hC₀
      | exact (inter_comm _ _).trans hC₁
      | exact (inter_comm _ _).trans h₀₁
  obtain ⟨x, hx, hunbounded, i, j, k, hij, hik, hjk, hfront, hbounded⟩ :=
    exists_exterior_pair_of_annuli h267 M hM hmeet
  have hchoice : ∃ B : Set E3, (B = B₀ ∨ B = B₁) ∧ (B = M i ∨ B = M j) := by
    by_cases hi : i = 0
    · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
      refine ⟨M j, ?_, Or.inr rfl⟩
      fin_cases j <;> simp_all [M]
    · refine ⟨M i, ?_, Or.inl rfl⟩
      fin_cases i <;> simp_all [M]
  obtain ⟨B, hB, hBfront⟩ := hchoice
  exact ⟨B, x, i, j, k, hB, hBfront, hx, hunbounded, hij, hik, hjk, hfront, hbounded⟩

end DifferentialGeometry.Topology.PiecewiseLinear
