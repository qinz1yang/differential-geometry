import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import Mathlib.Tactic.Group

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem not_mem_or_not_mem_of_eq_mul_conj_mul_conj
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x y : G}
    (hl : l = a * (x * b * x⁻¹) * (y * a⁻¹ * y⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem
    (N.mul_mem ha (‹N.Normal›.conj_mem b hb x))
    (‹N.Normal›.conj_mem a⁻¹ (N.inv_mem ha) y)

theorem not_mem_or_not_mem_of_eq_mul_conj_inv_mul
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {l a b x : G}
    (hl : l = a * (x * (b⁻¹ * a) * x⁻¹)) (hlN : l ∉ N) :
    a ∉ N ∨ b ∉ N := by
  by_contra h
  rw [not_or] at h
  have ha : a ∈ N := not_not.mp h.1
  have hb : b ∈ N := not_not.mp h.2
  apply hlN
  rw [hl]
  exact N.mul_mem ha
    (‹N.Normal›.conj_mem (b⁻¹ * a) (N.mul_mem (N.inv_mem hb) ha) x)

theorem four_path_mul_conj_inv_mul_factorization
    {G : Type*} [Group G] (s t u p : G) :
    s * t * u * p =
      (s * u) * ((u⁻¹ * t * u) * ((s * t⁻¹ * u * p⁻¹)⁻¹ * (s * u)) *
        (u⁻¹ * t * u)⁻¹) := by
  group

theorem not_mem_or_not_mem_of_four_path_factorization
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {s t u p : G} (hN : s * t * u * p ∉ N) :
    s * u ∉ N ∨ s * t⁻¹ * u * p⁻¹ ∉ N := by
  apply not_mem_or_not_mem_of_eq_mul_conj_inv_mul N
    (four_path_mul_conj_inv_mul_factorization s t u p) hN

end DifferentialGeometry.Topology.PiecewiseLinear
