import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialZero
import Mathlib.Analysis.Normed.Operator.Banach

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsHPolytope.isPolyhedron_frontier {P : Set E} (hP : IsHPolytope P) :
    IsPolyhedron (frontier P) := by
  classical
  obtain ⟨ι, hι, l, c, hrepr⟩ := hP.2
  let _ : Finite ι := hι
  have heq : frontier P = ⋃ i : {i // l i ≠ 0}, P ∩ (l i) ⁻¹' {c i} := by
    ext x
    constructor
    · intro hx
      have hxP : x ∈ P := hP.isClosed.frontier_subset hx
      have hxle : ∀ i, l i x ≤ c i := by rwa [hrepr] at hxP
      have hex : ∃ i, l i ≠ 0 ∧ l i x = c i := by
        by_contra! hnot
        have hlocal : ∀ i, ∀ᶠ y in 𝓝 x, l i y ≤ c i := by
          intro i
          by_cases hi : l i = 0
          · have hc : 0 ≤ c i := by simpa only [hi, LinearMap.zero_apply] using hxle i
            exact Filter.Eventually.of_forall fun y => by simpa only [hi, LinearMap.zero_apply] using hc
          · have hlt : l i x < c i := lt_of_le_of_ne (hxle i) (hnot i hi)
            filter_upwards [(isOpen_lt (l i).continuous_of_finiteDimensional continuous_const).mem_nhds hlt] with y hy
            exact hy.le
        have hnhds : P ∈ 𝓝 x := by
          rw [hrepr]
          exact Filter.eventually_all.mpr hlocal
        exact hx.2 (mem_interior_iff_mem_nhds.mpr hnhds)
      obtain ⟨i, hi, hix⟩ := hex
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxP, hix⟩
    · rintro hx
      obtain ⟨i, hxP, hix⟩ := mem_iUnion.mp hx
      refine ⟨subset_closure hxP, ?_⟩
      intro hxint
      have hex : ∃ v, l i v ≠ 0 := by
        by_contra! hzero
        exact i.property (by ext v; exact hzero v)
      obtain ⟨v, hv⟩ := hex
      have hsurj : Function.Surjective (l i) := by
        intro r
        refine ⟨(r / l i v) • v, ?_⟩
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
      have hopen : IsOpenMap (l i) := (l i).toContinuousLinearMap.isOpenMap hsurj
      have hmaps : MapsTo (l i) P (Iic (c i)) := by
        intro y hy
        have hall : ∀ j, l j y ≤ c j := by rwa [hrepr] at hy
        exact hall i
      have hlt : l i x < c i := by
        simpa only [interior_Iic, mem_Iio] using hopen.mapsTo_interior hmaps hxint
      exact hlt.ne hix
  rw [heq]
  exact IsPolyhedron.iUnion fun i =>
    (hP.inter_preimage (isHPolytope_singleton (c i)) (l i).toAffineMap).isPolyhedron

end DifferentialGeometry.Topology.PiecewiseLinear
