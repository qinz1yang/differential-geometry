/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInterior

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isCombinatorialSolidTorus_model_of_cycle_in_ball {B : Set E}
    (hB : IsPLBall 3 B) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCB : ∀ i, C i ⊆ B)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → C i ∩ C j ∩ C k = ∅) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → E),
      IsCombinatorialSolidTorus P ∧ IsPLHomeomorphOn g P (⋃ i, C i) := by
  classical
  obtain ⟨Q, ρ, -, hρ⟩ := exists_isPLHomeomorphOn_euclidean_of_isPLBall hB
  let D := fun i => ρ '' C i
  have hD (i : Fin (n + 3)) : IsPLBall 3 (D i) :=
    (hC i).of_isPLHomeomorphOn (hρ.restrict (hC i).isPolyhedron (hCB i))
  have hinter (i j : Fin (n + 3)) : D i ∩ D j = ρ '' (C i ∩ C j) :=
    (hρ.bijOn.injOn.image_inter (hCB i) (hCB j)).symm
  have hDnext (i j : Fin (n + 3)) (hij : (SimpleGraph.cycleGraph (n + 3)).Adj i j) :
      IsPLBall 2 (D i ∩ D j) := by
    rw [hinter]
    exact (hnext i j hij).of_isPLHomeomorphOn
      (hρ.restrict (hnext i j hij).isPolyhedron (inter_subset_left.trans (hCB i)))
  have hDdis (i j : Fin (n + 3)) (hij : i ≠ j)
      (hnadj : ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j) : Disjoint (D i) (D j) := by
    rw [disjoint_iff_inter_eq_empty, hinter, disjoint_iff_inter_eq_empty.mp (hdis i j hij hnadj),
      image_empty]
  have hDtriple (i j k : Fin (n + 3)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      D i ∩ D j ∩ D k = ∅ := by
    rw [hinter]
    change ρ '' (C i ∩ C j) ∩ ρ '' C k = ∅
    rw [← hρ.bijOn.injOn.image_inter (inter_subset_left.trans (hCB i)) (hCB k),
      htriple i j k hij hik hjk, image_empty]
  have hP := isCombinatorialSolidTorus_iUnion_of_cycle D hD hDnext hDdis hDtriple
  have hρC := hρ.restrict (IsPolyhedron.iUnion fun i => (hC i).isPolyhedron)
    (iUnion_subset hCB)
  have himage : ρ '' (⋃ i, C i) = ⋃ i, D i := image_iUnion
  rw [himage] at hρC
  exact ⟨⋃ i, D i, Function.invFunOn ρ (⋃ i, C i), hP, hρC.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
