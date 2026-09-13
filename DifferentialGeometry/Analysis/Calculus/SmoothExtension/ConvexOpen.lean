import DifferentialGeometry.Analysis.Calculus.CompactCutoff

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Set

theorem exists_contDiff_range_subset_eqOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hKU : K ⊆ U) (hne : U.Nonempty) :
    ∃ r : V → V, ContDiff ℝ ∞ r ∧ range r ⊆ U ∧ EqOn r id K := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨χ, hχ, -, hχone, hχsupp, hχrange⟩ := exists_bump_compact hK hU hKU
  refine ⟨fun x => χ x • x + (1 - χ x) • z,
    (hχ.smul contDiff_id).add ((contDiff_const.sub hχ).smul contDiff_const), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : χ x = 0
    · simpa only [hx, zero_smul, sub_zero, one_smul, zero_add] using hz
    · have hχx : χ x ∈ Icc (0 : ℝ) 1 := hχrange ⟨x, rfl⟩
      exact hconv (hχsupp (subset_tsupport χ hx)) hz hχx.1
        (sub_nonneg.mpr hχx.2) (by ring)
  · intro x hx
    simp only [hχone.self_of_nhdsSet hx, Pi.one_apply, one_smul, sub_self,
      zero_smul, add_zero, id_eq]

end DifferentialGeometry.Analysis
