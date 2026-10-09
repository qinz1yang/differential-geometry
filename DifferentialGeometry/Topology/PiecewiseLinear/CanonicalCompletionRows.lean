/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeNormalizationSequence

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalTower.exists_marked_annuli_of_bridge_normalizations
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314)
    (hstep : ∀ n, IsCanonicalBridgeNormalization (X n) (X (n + 1))
      (fun i => φ '' S i) S'' T'' I P' a b {-(n : ℤ), (n : ℤ)} ∅) :
    ∃ Jlo Jhi : ℤ → Set E3, ∀ i,
      IsPLAnnulusWithEnds (X (i.natAbs + 1) i).space (Jlo i) (Jhi i) ∧
      (X (i.natAbs + 1) i).space ∩ T'' (2 * i) = Jlo i ∧
      (X (i.natAbs + 1) i).space ∩ T'' (2 * (i + 1)) = Jhi i ∧
      ¬ boundsDiskIn (Jlo i) (T'' (2 * i)) ∧
      ¬ boundsDiskIn (Jhi i) (T'' (2 * (i + 1))) ∧
      (∀ hsub : Jlo i ⊆ S'' (2 * i), ∀ x : Jlo i,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(Jlo i, S'' (2 * i))) x)) ∧
      (∀ hsub : Jhi i ⊆ S'' (2 * (i + 1)), ∀ x : Jhi i,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
            C(Jhi i, S'' (2 * (i + 1)))) x)) := by
  have hmem (i : ℤ) : i ∈ ({-(i.natAbs : ℤ), (i.natAbs : ℤ)} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Int.natAbs_eq i with hi | hi
    · exact Or.inr hi
    · exact Or.inl hi
  choose Jlo Jhi hann hdis hlo hhi hloe hhie hmeetlo hmeethi using
    fun i => (hstep i.natAbs).exists_row_annulus htw h314 i (hmem i)
  refine ⟨Jlo, Jhi, fun i => ⟨hann i, hmeetlo i, hmeethi i, hloe i, hhie i, ?_, ?_⟩⟩
  · have htrace : Jlo i ∈ traceCircles
        ((X (i.natAbs + 1) (i - 1)).space ∪ (X (i.natAbs + 1) i).space) (T'' (2 * i)) :=
      traceCircles_subset_of_inter_subset
        ((hstep i.natAbs).target.surface.adjacentTrace i).traceCover
        (fun _ hx => ⟨Or.inr hx.1, hx.2⟩) (hlo i)
    exact (hstep i.natAbs).target.generators i (Finset.mem_union_left _ (hmem i))
      (Jlo i) htrace
  · have htrace : Jhi i ∈ traceCircles
        ((X (i.natAbs + 1) ((i + 1) - 1)).space ∪ (X (i.natAbs + 1) (i + 1)).space)
        (T'' (2 * (i + 1))) := by
      apply traceCircles_subset_of_inter_subset
        ((hstep i.natAbs).target.surface.adjacentTrace (i + 1)).traceCover ?_ (hhi i)
      rw [add_sub_cancel_right]
      exact fun _ hx => ⟨Or.inl hx.1, hx.2⟩
    exact (hstep i.natAbs).target.generators (i + 1)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hmem i, rfl⟩)) (Jhi i) htrace

end DifferentialGeometry.Topology.PiecewiseLinear
