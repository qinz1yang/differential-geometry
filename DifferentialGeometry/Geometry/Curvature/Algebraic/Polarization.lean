import DifferentialGeometry.Geometry.Curvature.Algebraic.Form

/-!
# Polarization bound for algebraic curvature forms

An algebraic curvature form `B` is controlled by its sectional values `B u w w u`: if
`|B u w w u| ≤ K N(u)² N(w)²` for a subadditive nonnegative gauge `N`, then
`|B x y z w| ≤ 18 K r⁴` whenever `N x, N y, N z, N w ≤ r`
(`IsAlgCurvForm.abs_le_of_abs_sectional_le`). The proof is the quantitative form of
`IsAlgCurvForm.zero_of_diag`: polarize in the third slot, then in the second and fourth slots,
and solve the first Bianchi identity.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {B : V → V → V → V → ℝ}

private theorem two_mul_three (hB : IsAlgCurvForm B) (x y z : V) :
    2 * B x y z y = B (x + z) y (x + z) y - B x y x y - B z y z y := by
  rw [hB.add_left, hB.add_three, hB.add_three, hB.pair_swap z y x y]
  ring

private theorem sub_cyclic (hB : IsAlgCurvForm B) (x y z w : V) :
    B x y z w - B y z x w =
      B x (y + w) z (y + w) - B x y z y - B x w z w := by
  rw [hB.add_two, hB.add_four, hB.add_four, hB.pair_swap x w z y, hB.anti_first z y x w]
  ring

private theorem three_mul (hB : IsAlgCurvForm B) (x y z w : V) :
    3 * B x y z w = 2 * (B x y z w - B y z x w) + (B y z x w - B z x y w) := by
  have h := hB.bianchi x y z w
  linarith

private theorem abs_diag_le (hB : IsAlgCurvForm B) (N : V → ℝ) {K : ℝ}
    (hk : ∀ u w, |B u w w u| ≤ K * N u ^ 2 * N w ^ 2) (x y : V) :
    |B x y x y| ≤ K * N x ^ 2 * N y ^ 2 := by
  rw [hB.anti_last x y x y, abs_neg]
  exact hk x y

private theorem abs_three_le (hB : IsAlgCurvForm B) (N : V → ℝ) (hN : ∀ x, 0 ≤ N x)
    (hNadd : ∀ x y, N (x + y) ≤ N x + N y) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ u w, |B u w w u| ≤ K * N u ^ 2 * N w ^ 2) {x y z : V} {a b c : ℝ}
    (hx : N x ≤ a) (hy : N y ≤ b) (hz : N z ≤ c) :
    |B x y z y| ≤ K * b ^ 2 * ((a + c) ^ 2 + a ^ 2 + c ^ 2) / 2 := by
  have h2 := two_mul_three hB x y z
  have e1 := abs_diag_le hB N hk (x + z) y
  have e2 := abs_diag_le hB N hk x y
  have e3 := abs_diag_le hB N hk z y
  have hxz : N (x + z) ≤ a + c := (hNadd x z).trans (add_le_add hx hz)
  have s1 : N (x + z) ^ 2 ≤ (a + c) ^ 2 := pow_le_pow_left₀ (hN _) hxz 2
  have s2 : N x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (hN _) hx 2
  have s3 : N z ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (hN _) hz 2
  have s4 : N y ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (hN _) hy 2
  have t1 : K * N (x + z) ^ 2 * N y ^ 2 ≤ K * (a + c) ^ 2 * b ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left s1 hK) s4 (sq_nonneg _)
      (mul_nonneg hK (sq_nonneg _))
  have t2 : K * N x ^ 2 * N y ^ 2 ≤ K * a ^ 2 * b ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left s2 hK) s4 (sq_nonneg _)
      (mul_nonneg hK (sq_nonneg _))
  have t3 : K * N z ^ 2 * N y ^ 2 ≤ K * c ^ 2 * b ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left s3 hK) s4 (sq_nonneg _)
      (mul_nonneg hK (sq_nonneg _))
  have habs : |2 * B x y z y| ≤ K * (a + c) ^ 2 * b ^ 2 + K * a ^ 2 * b ^ 2 +
      K * c ^ 2 * b ^ 2 := by
    rw [h2]
    calc |B (x + z) y (x + z) y - B x y x y - B z y z y|
        ≤ |B (x + z) y (x + z) y| + |B x y x y| + |B z y z y| := by
          have := abs_sub (B (x + z) y (x + z) y - B x y x y) (B z y z y)
          have := abs_sub (B (x + z) y (x + z) y) (B x y x y)
          linarith
      _ ≤ _ := by linarith
  rw [abs_mul, abs_two] at habs
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [habs]

/-- **Polarization bound.** An algebraic curvature form whose sectional values satisfy
`|B u w w u| ≤ K N(u)² N(w)²` for a nonnegative subadditive `N` is bounded by `18 K r⁴` on
quadruples with `N ≤ r`. -/
theorem abs_le_of_abs_sectional_le (hB : IsAlgCurvForm B) (N : V → ℝ) (hN : ∀ x, 0 ≤ N x)
    (hNadd : ∀ x y, N (x + y) ≤ N x + N y) {K : ℝ} (hK : 0 ≤ K)
    (hk : ∀ u w, |B u w w u| ≤ K * N u ^ 2 * N w ^ 2) {r : ℝ} {x y z w : V}
    (hx : N x ≤ r) (hy : N y ≤ r) (hz : N z ≤ r) (hw : N w ≤ r) :
    |B x y z w| ≤ 18 * K * r ^ 4 := by
  have hr : 0 ≤ r := (hN x).trans hx
  have hyw : N (y + w) ≤ 2 * r := (hNadd y w).trans (by linarith)
  have hzw : N (z + w) ≤ 2 * r := (hNadd z w).trans (by linarith)
  have hS1 : |B x y z w - B y z x w| ≤ 18 * K * r ^ 4 := by
    rw [sub_cyclic hB]
    have a1 := abs_three_le hB N hN hNadd hK hk hx hyw hz
    have a2 := abs_three_le hB N hN hNadd hK hk hx hy hz
    have a3 := abs_three_le hB N hN hNadd hK hk hx hw hz
    have e1 := abs_sub (B x (y + w) z (y + w) - B x y z y) (B x w z w)
    have e2 := abs_sub (B x (y + w) z (y + w)) (B x y z y)
    have hr4 : 0 ≤ K * r ^ 4 := mul_nonneg hK (pow_nonneg hr 4)
    nlinarith
  have hS2 : |B y z x w - B z x y w| ≤ 18 * K * r ^ 4 := by
    rw [sub_cyclic hB]
    have a1 := abs_three_le hB N hN hNadd hK hk hy hzw hx
    have a2 := abs_three_le hB N hN hNadd hK hk hy hz hx
    have a3 := abs_three_le hB N hN hNadd hK hk hy hw hx
    have e1 := abs_sub (B y (z + w) x (z + w) - B y z x z) (B y w x w)
    have e2 := abs_sub (B y (z + w) x (z + w)) (B y z x z)
    have hr4 : 0 ≤ K * r ^ 4 := mul_nonneg hK (pow_nonneg hr 4)
    nlinarith
  have h3 := three_mul hB x y z w
  have habs : |3 * B x y z w| ≤ 3 * (18 * K * r ^ 4) := by
    rw [h3]
    calc |2 * (B x y z w - B y z x w) + (B y z x w - B z x y w)|
        ≤ |2 * (B x y z w - B y z x w)| + |B y z x w - B z x y w| := abs_add_le _ _
      _ ≤ 3 * (18 * K * r ^ 4) := by
          rw [abs_mul, abs_two]
          linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at habs
  linarith

end DifferentialGeometry.Geometry.Curvature.IsAlgCurvForm
