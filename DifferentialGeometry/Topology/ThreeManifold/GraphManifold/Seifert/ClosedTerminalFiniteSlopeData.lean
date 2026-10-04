import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Data

/-!
# Closed triangle arithmetic in an arbitrary actual cone order

An equivalence with the actual cone index set preserves both invariant sums. Positive orbifold
characteristic and the proved nonvanishing Euler number give exactly the arithmetic inputs of
the spherical central extension consumer, without imposing an order on the filled ports.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GC.Seifert.SeifertData

private theorem closedTriangle_sum_cones_of_equiv (d : SeifertData)
    (e : Fin 3 ≃ Fin d.cones.length) (f : ℕ × ℤ → ℚ) :
    (d.cones.map f).sum = ∑ i : Fin 3, f d.cones[e i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact (e.sum_comp (fun i => f d.cones[i])).symm

theorem closedTriangle_arithmetic_of_equiv (d : SeifertData) (hc : d.ports = 0)
    (hcones : d.cones.length = 3) (hchi : 0 < d.orbChi)
    (e : Fin 3 ≃ Fin d.cones.length) :
    let p := fun i : Fin 3 => d.cones[e i].1
    let q := fun i : Fin 3 => d.cones[e i].2
    (∀ i, 2 ≤ p i) ∧
      1 < (1 : ℝ) / p 0 + 1 / p 1 + 1 / p 2 ∧
      q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
        q 2 * (p 0 : ℤ) * p 1 ≠ 0 := by
  let p := fun i : Fin 3 => d.cones[e i].1
  let q := fun i : Fin 3 => d.cones[e i].2
  have hp : ∀ i, 2 ≤ p i := by
    intro i
    exact d.two_le_of_mem_cones _ (List.getElem_mem _)
  have hchiQ : 1 < (1 : ℚ) / p 0 + 1 / p 1 + 1 / p 2 := by
    have h := hchi
    rw [orbChi, hc, closedTriangle_sum_cones_of_equiv d e] at h
    simp only [Nat.cast_zero, sub_zero, Fin.sum_univ_three] at h
    change 0 < 2 - (1 - 1 / (p 0 : ℚ) + (1 - 1 / (p 1 : ℚ)) +
      (1 - 1 / (p 2 : ℚ))) at h
    linarith
  have hchiR : 1 < (1 : ℝ) / p 0 + 1 / p 1 + 1 / p 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hchiQ
    simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_div, Rat.cast_natCast] using h
  refine ⟨hp, hchiR, ?_⟩
  intro hnum
  have hpQ : ∀ i, (p i : ℚ) ≠ 0 := by
    intro i
    exact_mod_cast (by have h := hp i; omega : p i ≠ 0)
  have hnumQ : (q 0 : ℚ) * p 1 * p 2 + (q 1 : ℚ) * p 0 * p 2 +
      (q 2 : ℚ) * p 0 * p 1 = 0 := by exact_mod_cast hnum
  have hfrac : (q 0 : ℚ) / p 0 + (q 1 : ℚ) / p 1 + (q 2 : ℚ) / p 2 = 0 := by
    field_simp [hpQ 0, hpQ 1, hpQ 2]
    linear_combination hnumQ
  have hn : d.normals = [] := List.eq_nil_of_length_eq_zero (by
    have hk := d.k_le_three
    have hcount := d.ports_add_length_add_length
    omega)
  apply d.euler_ne_zero_of_three_cones hc hcones hchi
  rw [euler, hn, List.map_nil, List.sum_nil, add_zero,
    closedTriangle_sum_cones_of_equiv d e]
  simp only [Fin.sum_univ_three, neg_eq_zero]
  exact hfrac

end GC.Seifert.SeifertData
