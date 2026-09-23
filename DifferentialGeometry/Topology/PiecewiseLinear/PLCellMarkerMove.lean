import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPointTransport
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_excluding_point_preserving_union {M : Type*} [TopologicalSpace M]
    [TopologicalSpace.MetrizableSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {A B Bd U : Set M} (hB : IsPLCellOn 3 B Bd) (hU : IsOpen U) (hc : IsPreconnected U)
    (hUA : U ⊆ interior A) {p q : M} (hp : p ∈ U) (hq : q ∈ U) (hqB : q ∉ B) :
    ∃ C : Set M, IsPLCellOn 3 C (frontier C) ∧ p ∉ C ∧ A ∪ C = A ∪ B ∧
      interior A ∪ interior C = interior A ∪ interior B ∧
      frontier A ∩ frontier C = frontier A ∩ frontier B ∧ C \ U = B \ U ∧
      ((interior A ∩ interior C).Nonempty ↔ (interior A ∩ interior B).Nonempty) := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨K, φ, -, hKU, hφ, hφi, hfix, hφp⟩ :=
    exists_isPL_homeomorph_map_point_eqOn_compl (n := 3) hU hc hp hq
  have hfixU : EqOn φ id Uᶜ := fun x hx => hfix fun hxK => hx (hKU hxK)
  have hfixA : EqOn φ id (interior A)ᶜ :=
    fun x hx => hfixU fun hxU => hx (hUA hxU)
  have hmem (D : Set M) (x : M) : x ∈ φ.symm '' D ↔ φ x ∈ D := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [φ.apply_symm_apply] using hy
    · intro hx
      exact ⟨φ x, hx, φ.symm_apply_apply x⟩
  have hφu : IsPLHomeomorphInto 3 φ.symm univ := by
    refine ⟨fun x _ => hφi x, φ.symm.injective.injOn, fun y _ => ⟨φ, ?_, ?_⟩⟩
    · rw [image_univ, φ.symm.surjective.range_eq]
      exact hφ y
    · exact fun x _ => φ.apply_symm_apply x
  have hcell := hB.image (hφu.mono_of_isPLCellOn hB (subset_univ _))
  refine ⟨φ.symm '' B, hcell.boundary_eq_frontier ▸ hcell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem, hφp]
    exact hqB
  · ext x
    by_cases hx : x ∈ A
    · simp only [mem_union, hx, true_or]
    · have hxI : x ∉ interior A := fun hxI => hx (interior_subset hxI)
      simp only [mem_union, hx, false_or, hmem, hfixA hxI, id_eq]
  · rw [← φ.symm.image_interior]
    ext x
    by_cases hx : x ∈ interior A
    · simp only [mem_union, hx, true_or]
    · simp only [mem_union, hx, false_or, hmem, hfixA hx, id_eq]
  · rw [← φ.symm.image_frontier]
    ext x
    by_cases hx : x ∈ frontier A
    · have hxI : x ∉ interior A := hx.2
      simp only [mem_inter_iff, hx, true_and, hmem, hfixA hxI, id_eq]
    · simp only [mem_inter_iff, hx, false_and]
  · ext x
    by_cases hx : x ∈ U
    · simp only [mem_sdiff, hx, not_true_eq_false, and_false]
    · simp only [mem_sdiff, hx, not_false_eq_true, and_true, hmem, hfixU hx, id_eq]
  · have hAi (x : M) : φ x ∈ interior A ↔ x ∈ interior A := by
      constructor
      · intro hx
        by_contra hn
        exact hn (by simpa only [hfixA hn, id_eq] using hx)
      · intro hx
        by_contra hn
        have he : φ x = x := φ.injective (hfixA hn)
        exact hn (he.symm ▸ hx)
    rw [← φ.symm.image_interior]
    constructor
    · rintro ⟨x, hxA, hxB⟩
      exact ⟨φ x, (hAi x).mpr hxA, (hmem _ _).mp hxB⟩
    · rintro ⟨x, hxA, hxB⟩
      refine ⟨φ.symm x, (hAi _).mp ?_, ⟨x, hxB, rfl⟩⟩
      simpa only [φ.apply_symm_apply] using hxA

end DifferentialGeometry.Topology.PiecewiseLinear
