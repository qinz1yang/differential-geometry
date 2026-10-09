import DifferentialGeometry.Geometry.Exponential.Flat.LatticeHolonomyMatrices
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Two parallel periods of the actual integer lattice generate a lattice period with coprime
integer coefficients. Integer basis coordinates and Bezout provide that period internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem parallel_lattice_periods_coprime (b : Basis (Fin 3) ℝ E3) (u v : E3)
    (hu : u ∈ Submodule.span ℤ (Set.range b))
    (hv : v ∈ Submodule.span ℤ (Set.range b)) (hu0 : u ≠ 0)
    (hparallel : ∃ c : ℝ, v = c • u) :
    ∃ (t : E3) (m n : ℤ), t ∈ Submodule.span ℤ (Set.range b) ∧
      u = m • t ∧ v = n • t ∧ Int.gcd m n = 1 := by
  classical
  have huc (i : Fin 3) : ∃ z : ℤ, b.repr u i = (z : ℝ) := by
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ u).mp hu i
    exact ⟨z, by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hz.symm⟩
  have hvc (i : Fin 3) : ∃ z : ℤ, b.repr v i = (z : ℝ) := by
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ v).mp hv i
    exact ⟨z, by simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hz.symm⟩
  choose cu hcu using huc
  choose cv hcv using hvc
  have hi : ∃ i : Fin 3, b.repr u i ≠ 0 := by
    by_contra he
    apply hu0
    apply b.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using not_not.mp ((not_exists.mp he) i)
  obtain ⟨i, hi⟩ := hi
  have ha : cu i ≠ 0 := by
    intro he
    exact hi (by rw [hcu i, he, Int.cast_zero])
  obtain ⟨c, hc⟩ := hparallel
  have hratio : (cv i : ℝ) = c * (cu i : ℝ) := by
    rw [← hcv i, hc, map_smul, Finsupp.smul_apply, hcu i, smul_eq_mul]
  have hab : (cu i : ℝ) • v = (cv i : ℝ) • u := by
    rw [hc, smul_smul, hratio, mul_comm]
  have hgpos : 0 < Int.gcd (cu i) (cv i) := Int.gcd_pos_of_ne_zero_left (cv i) ha
  obtain ⟨m, n, hcop, hm, hn⟩ := Int.exists_gcd_one hgpos
  let d : ℝ := Int.gcd (cu i) (cv i)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact_mod_cast hgpos.ne'
  have hmnreal : (m : ℝ) • v = (n : ℝ) • u := by
    have he : d • ((m : ℝ) • v) = d • ((n : ℝ) • u) := by
      simp only [smul_smul]
      change ((Int.gcd (cu i) (cv i) : ℝ) * (m : ℝ)) • v =
        ((Int.gcd (cu i) (cv i) : ℝ) * (n : ℝ)) • u
      have hmc : (cu i : ℝ) = (m : ℝ) * Int.gcd (cu i) (cv i) := by exact_mod_cast hm
      have hnc : (cv i : ℝ) = (n : ℝ) * Int.gcd (cu i) (cv i) := by exact_mod_cast hn
      rw [mul_comm _ (m : ℝ), mul_comm _ (n : ℝ), ← hmc, ← hnc]
      exact hab
    have hz : d • ((m : ℝ) • v - (n : ℝ) • u) = 0 := by rw [smul_sub, he, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hd)
  have hmn : m • v = n • u := by
    simpa only [Int.cast_smul_eq_zsmul ℝ] using hmnreal
  let A := Int.gcdA m n
  let B := Int.gcdB m n
  let t := A • u + B • v
  have ht : t ∈ Submodule.span ℤ (Set.range b) :=
    (Submodule.span ℤ (Set.range b)).add_mem
      ((Submodule.span ℤ (Set.range b)).smul_mem A hu)
      ((Submodule.span ℤ (Set.range b)).smul_mem B hv)
  have hBez : m * A + n * B = 1 := by
    simpa only [A, B, hcop, Nat.cast_one] using (Int.gcd_eq_gcd_ab m n).symm
  have hmt : m • t = u := by
    change m • (A • u + B • v) = u
    rw [smul_add, smul_comm m A u, smul_comm m B v, hmn]
    rw [smul_smul, smul_smul, ← add_smul, mul_comm A m, mul_comm B n, hBez, one_smul]
  have hnt : n • t = v := by
    change n • (A • u + B • v) = v
    rw [smul_add, smul_comm n A u, smul_comm n B v, ← hmn]
    rw [smul_smul, smul_smul, ← add_smul, mul_comm A m, mul_comm B n, hBez, one_smul]
  exact ⟨t, m, n, ht, hmt.symm, hnt.symm, hcop⟩

end DifferentialGeometry.Geometry.FlatSurface
