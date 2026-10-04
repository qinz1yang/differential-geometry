import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic.Module

/-!
# Finite abelian groups with closed triangle filling relations

The boundary and filling relations annihilate the fibre by the Euler numerator. Positive
cone orders then make all generators torsion, so the generated commutative group is finite.
This algebraic backend does not identify an actual manifold fundamental group or its generators.
-/

set_option autoImplicit false

universe u

namespace GC.Seifert

private theorem closedTriangleEuler_smul_eq_zero
    {A : Type u} [AddCommGroup A] (x : Fin 3 → A) (z : A)
    (p : Fin 3 → ℕ) (q : Fin 3 → ℤ)
    (hboundary : x 0 + x 2 + x 1 = 0)
    (hfill : ∀ i, (p i : ℤ) • x i + q i • z = 0) :
    (q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
      q 2 * (p 0 : ℤ) * p 1) • z = 0 := by
  calc
    (q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
        q 2 * (p 0 : ℤ) * p 1) • z =
        ((p 1 : ℤ) * p 2) • ((p 0 : ℤ) • x 0 + q 0 • z) +
          ((p 0 : ℤ) * p 2) • ((p 1 : ℤ) • x 1 + q 1 • z) +
          ((p 0 : ℤ) * p 1) • ((p 2 : ℤ) • x 2 + q 2 • z) -
          ((p 0 : ℤ) * p 1 * p 2) • (x 0 + x 2 + x 1) := by module
    _ = 0 := by rw [hfill, hfill, hfill, hboundary]; simp

theorem closedTriangleFibre_zpow_euler_eq_one
    {G : Type u} [CommGroup G] (x : Fin 3 → G) (z : G)
    (p : Fin 3 → ℕ) (q : Fin 3 → ℤ)
    (hboundary : x 0 * x 2 * x 1 = 1)
    (hfill : ∀ i, x i ^ p i * z ^ q i = 1) :
    z ^ (q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
      q 2 * (p 0 : ℤ) * p 1) = 1 := by
  have hb : Additive.ofMul (x 0) + Additive.ofMul (x 2) +
      Additive.ofMul (x 1) = 0 := by
    exact congrArg Additive.ofMul hboundary
  have hf : ∀ i, (p i : ℤ) • Additive.ofMul (x i) + q i • Additive.ofMul z = 0 := by
    intro i
    rw [natCast_zsmul]
    exact congrArg Additive.ofMul (hfill i)
  exact congrArg Additive.toMul
    (closedTriangleEuler_smul_eq_zero (fun i => Additive.ofMul (x i))
      (Additive.ofMul z) p q hb hf)

theorem finite_closedTriangleAbelianGroup
    (G : Type u) [CommGroup G] (x : Fin 3 → G) (z : G)
    (p : Fin 3 → ℕ) (q : Fin 3 → ℤ) (hp : ∀ i, 0 < p i)
    (hgen : Subgroup.closure (Set.range x ∪ {z}) = ⊤)
    (hboundary : x 0 * x 2 * x 1 = 1)
    (hfill : ∀ i, x i ^ p i * z ^ q i = 1)
    (heuler : q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
      q 2 * (p 0 : ℤ) * p 1 ≠ 0) : Finite G := by
  have hz : IsOfFinOrder z := isOfFinOrder_iff_zpow_eq_one.mpr
    ⟨_, heuler, closedTriangleFibre_zpow_euler_eq_one x z p q hboundary hfill⟩
  have hx : ∀ i, IsOfFinOrder (x i) := by
    intro i
    obtain ⟨n, hn, hzn⟩ := hz.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨p i * n, Nat.mul_pos (hp i) hn, ?_⟩
    have hznq : (z ^ q i) ^ n = 1 := by
      calc
        (z ^ q i) ^ n = (z ^ q i) ^ (n : ℤ) := (zpow_natCast (z ^ q i) n).symm
        _ = (z ^ (n : ℤ)) ^ q i := zpow_comm z (q i) n
        _ = 1 := by rw [zpow_natCast, hzn, one_zpow]
    have h := congrArg (fun a : G => a ^ n) (hfill i)
    simpa only [mul_pow, hznq, mul_one, ← pow_mul, one_pow] using h
  have htorsion : IsMulTorsion G := by
    have hle : Subgroup.closure (Set.range x ∪ {z}) ≤ CommGroup.torsion G := by
      apply (Subgroup.closure_le (CommGroup.torsion G)).mpr
      intro g hg
      rcases hg with hg | hg
      · obtain ⟨i, rfl⟩ := hg
        exact hx i
      · obtain rfl := hg
        exact hz
    rw [hgen] at hle
    exact CommGroup.torsion_eq_top_iff.mp (top_le_iff.mp hle)
  let : Group.FG G := Group.fg_iff.mpr
    ⟨Set.range x ∪ {z}, hgen, (Set.finite_range x).union (Set.finite_singleton z)⟩
  exact CommGroup.finite_of_fg_isMulTorsion G htorsion

end GC.Seifert
