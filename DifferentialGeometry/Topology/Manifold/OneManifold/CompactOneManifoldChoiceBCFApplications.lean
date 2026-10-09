import DifferentialGeometry.Topology.Manifold.OneManifold.CompactOneManifoldChoiceBCF

/-!
# Consumers of the shared `K₃` kernel K0 (lane B-BCF134)

* `exists_compactOneDomain_line_BCF`: on the one-chart atlas of the real line, the kernel applied to
  `Kset = [0, 1]`, `Fset = {0, 1}` gives a compact smooth one-dimensional domain containing `[0, 1]`,
  with no loop (a loop range would be a nonempty compact open subset of `ℝ`) and at least one arc.
* `SmoothCompactOneDomain_BCF.loop_range_isCompact_BCF`, `…loop_range_nonempty_BCF`: the circle
  components are compact and nonempty (used to exclude them by connectedness in a binding).
-/

set_option autoImplicit false

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

namespace SmoothCompactOneDomain_BCF

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}
  (D : SmoothCompactOneDomain_BCF Bs)

/-- A loop range is compact. -/
theorem loop_range_isCompact_BCF (j : Fin D.l) : IsCompact (range (D.loop j)) := by
  rw [← (D.loop_periodic j).image_Icc one_pos 0]
  exact isCompact_Icc.image (D.loop_smooth j).continuous

/-- A loop range is nonempty. -/
theorem loop_range_nonempty_BCF (j : Fin D.l) : (range (D.loop j)).Nonempty :=
  range_nonempty _

end SmoothCompactOneDomain_BCF

/-- **Consumer of K0**: on the real line the kernel gives a domain containing `[0, 1]` with at least
one arc and no loop. -/
theorem exists_compactOneDomain_line_BCF :
    ∃ D : SmoothCompactOneDomain_BCF (univ : Set ℝ), Icc (0 : ℝ) 1 ⊆ D.carrier ∧ D.l = 0 ∧
      0 < D.m := by
  obtain ⟨D, hD, -⟩ := lineGraphAtlas_BCF.exists_compact_oneManifold_choice74_BCF
    (Q := Icc (0 : ℝ) 1) (F := {0, 1}) isCompact_Icc (subset_univ _)
    ((finite_singleton 1).insert 0)
  have hsub : Icc (0 : ℝ) 1 ⊆ D.carrier := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hD hx
    exact (interior_subset hy : y ∈ Subtype.val ⁻¹' D.carrier)
  have hl : D.l = 0 := by
    by_contra hl
    obtain ⟨j⟩ : Nonempty (Fin D.l) := ⟨⟨0, Nat.pos_of_ne_zero hl⟩⟩
    obtain ⟨G, hG, hGB⟩ := D.loop_relOpen j
    rw [inter_univ] at hGB
    have hclopen : IsClopen (range (D.loop j)) :=
      ⟨(D.loop_range_isCompact_BCF j).isClosed, hGB ▸ hG⟩
    have huniv := hclopen.eq_univ (D.loop_range_nonempty_BCF j)
    have hcpt : IsCompact (univ : Set ℝ) := huniv ▸ D.loop_range_isCompact_BCF j
    exact noncompact_univ ℝ hcpt
  refine ⟨D, hsub, hl, Nat.pos_of_ne_zero fun hm => ?_⟩
  have h0 : (0 : ℝ) ∈ D.carrier := hsub (left_mem_Icc.mpr zero_le_one)
  rw [D.carrier_eq] at h0
  rcases h0 with h0 | h0
  · obtain ⟨k, -⟩ := mem_iUnion.mp h0
    exact (hm ▸ k).elim0
  · obtain ⟨j, -⟩ := mem_iUnion.mp h0
    exact (hl ▸ j).elim0

end DifferentialGeometry.Topology
