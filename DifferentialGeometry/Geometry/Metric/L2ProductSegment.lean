import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Segments of an `ℓ²` product project to affine curves in an inner-product factor (LFR11, K4)

Blueprint LFR11 (A:25566–25672), proof, second paragraph: for a distance isometry
`I : N → ℝ^j × Y` (`ℓ²` product), a (constant-speed) metric segment of `N` has an AFFINE Euclidean
component. Here: if `c : ℝ → WithLp 2 (F × Y)` satisfies `d(c s, c s') = λ |s - s'|` on `[a, b]`
and `F` is a real inner-product space, then `(c s).fst` is the affine interpolation of its
endpoint values (`fst_eq_affine_of_dist_eq_mul`).

Route: equality in the triangle inequality for `d = √(d_F² + d_Y²)` forces equality in both
factor triangle inequalities and in Cauchy–Schwarz for `(d_F, d_Y)`; strict convexity of `F`
(`sameRay_iff_norm_add`) then aligns the increments.
-/

set_option autoImplicit false

open Set WithLp

namespace GC.MetricGeometry

variable {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MetricSpace Y]

/-- **Kernel K4.** The Euclidean component of a constant-speed segment of an `ℓ²` product with an
inner-product factor is affine. -/
theorem fst_eq_affine_of_dist_eq_mul {c : ℝ → WithLp 2 (F × Y)} {a b lam : ℝ} (hab : a < b)
    (hseg : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, dist (c s) (c s') = lam * |s - s'|)
    {s : ℝ} (hs : s ∈ Icc a b) :
    (c s).fst = (c a).fst + ((s - a) / (b - a)) • ((c b).fst - (c a).fst) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  set p := c a with hp
  set q := c s with hq
  set r := c b with hr
  -- the three distances
  have hA : dist p q = lam * (s - a) := by
    rw [hseg a ha s hs, abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
  have hB : dist q r = lam * (b - s) := by
    rw [hseg s hs b hb, abs_sub_comm, abs_of_nonneg (by linarith [hs.2])]
  have hD : dist p r = lam * (b - a) := by
    rw [hseg a ha b hb, abs_sub_comm, abs_of_nonneg (by linarith)]
  have hlam : 0 ≤ lam := by
    have h0 := dist_nonneg (x := p) (y := r)
    rw [hD] at h0
    exact nonneg_of_mul_nonneg_left h0 (by linarith)
  -- factor distances
  set x₁ := dist p.fst q.fst with hx₁
  set x₂ := dist q.fst r.fst with hx₂
  set X := dist p.fst r.fst with hX
  set y₁ := dist p.snd q.snd with hy₁
  set y₂ := dist q.snd r.snd with hy₂
  set Yd := dist p.snd r.snd with hYd
  have hA2 : (lam * (s - a)) ^ 2 = x₁ ^ 2 + y₁ ^ 2 := by rw [← hA]; exact prod_dist_sq_eq_add_sq p q
  have hB2 : (lam * (b - s)) ^ 2 = x₂ ^ 2 + y₂ ^ 2 := by rw [← hB]; exact prod_dist_sq_eq_add_sq q r
  have hD2 : (lam * (b - a)) ^ 2 = X ^ 2 + Yd ^ 2 := by rw [← hD]; exact prod_dist_sq_eq_add_sq p r
  have hXle : X ≤ x₁ + x₂ := dist_triangle _ _ _
  have hYle : Yd ≤ y₁ + y₂ := dist_triangle _ _ _
  have hx₁0 : 0 ≤ x₁ := dist_nonneg
  have hx₂0 : 0 ≤ x₂ := dist_nonneg
  have hX0 : 0 ≤ X := dist_nonneg
  have hy₁0 : 0 ≤ y₁ := dist_nonneg
  have hy₂0 : 0 ≤ y₂ := dist_nonneg
  have hYd0 : 0 ≤ Yd := dist_nonneg
  set A := lam * (s - a) with hAdef
  set B := lam * (b - s) with hBdef
  have hA0 : 0 ≤ A := mul_nonneg hlam (by linarith [hs.1])
  have hB0 : 0 ≤ B := mul_nonneg hlam (by linarith [hs.2])
  have hAB : lam * (b - a) = A + B := by rw [hAdef, hBdef]; ring
  rw [hAB] at hD2
  have e1 : X ^ 2 ≤ (x₁ + x₂) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
  have e2 : Yd ^ 2 ≤ (y₁ + y₂) ^ 2 := pow_le_pow_left₀ hYd0 hYle 2
  -- Cauchy–Schwarz in `ℝ²` and the triangle inequalities give equality everywhere
  have hCS : x₁ * x₂ + y₁ * y₂ ≤ A * B := by
    have hsq : (x₁ * x₂ + y₁ * y₂) ^ 2 ≤ (A * B) ^ 2 := by
      rw [mul_pow A B 2, hA2, hB2]
      have h0 := sq_nonneg (x₁ * y₂ - x₂ * y₁)
      have h1 : (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) - (x₁ * x₂ + y₁ * y₂) ^ 2 =
          (x₁ * y₂ - x₂ * y₁) ^ 2 := by ring
      linarith
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hA0 hB0)).2
  have hup : (A + B) ^ 2 ≤ (x₁ + x₂) ^ 2 + (y₁ + y₂) ^ 2 := by
    rw [hD2]
    linarith
  have hcross : x₁ * x₂ + y₁ * y₂ = A * B := by
    apply le_antisymm hCS
    have h1 : (A + B) ^ 2 = A ^ 2 + B ^ 2 + 2 * (A * B) := by ring
    have h2 : (x₁ + x₂) ^ 2 + (y₁ + y₂) ^ 2 =
        (x₁ ^ 2 + y₁ ^ 2) + (x₂ ^ 2 + y₂ ^ 2) + 2 * (x₁ * x₂ + y₁ * y₂) := by ring
    rw [h1, h2, hA2, hB2] at hup
    linarith
  have hXeq : X = x₁ + x₂ := by
    have h1 : X ^ 2 + Yd ^ 2 = (x₁ + x₂) ^ 2 + (y₁ + y₂) ^ 2 := by
      linear_combination (-1 : ℝ) * hD2 + hA2 + hB2 - 2 * hcross
    have e3 : X ^ 2 = (x₁ + x₂) ^ 2 := by linarith
    exact (sq_eq_sq₀ hX0 (add_nonneg hx₁0 hx₂0)).mp e3
  have hpar : x₁ * y₂ = x₂ * y₁ := by
    have h1 : (x₁ * x₂ + y₁ * y₂) ^ 2 = (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) := by
      rw [hcross, ← hA2, ← hB2]; ring
    have h2 : (x₁ * y₂ - x₂ * y₁) ^ 2 = 0 := by linear_combination (-1 : ℝ) * h1
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hratio : x₁ * B = x₂ * A := by
    have h1 : (x₁ * B) ^ 2 = (x₂ * A) ^ 2 := by
      rw [mul_pow x₁ B 2, mul_pow x₂ A 2, hA2, hB2]
      linear_combination (x₁ * y₂ + x₂ * y₁) * hpar
    exact (sq_eq_sq₀ (mul_nonneg hx₁0 hB0) (mul_nonneg hx₂0 hA0)).mp h1
  -- the Euclidean increments lie on one ray
  set u := q.fst - p.fst with hu
  set w := r.fst - q.fst with hw
  have hnu : ‖u‖ = x₁ := by rw [hu, ← dist_eq_norm, dist_comm]
  have hnw : ‖w‖ = x₂ := by rw [hw, ← dist_eq_norm, dist_comm]
  have huw : u + w = r.fst - p.fst := by rw [hu, hw]; abel
  have hnuw : ‖u + w‖ = X := by rw [huw, ← dist_eq_norm, dist_comm]
  have hray : SameRay ℝ u w := sameRay_iff_norm_add.mpr (by rw [hnuw, hnu, hnw, hXeq])
  have hsmul : X • u = x₁ • (r.fst - p.fst) := by
    have h1 := hray.norm_smul_eq
    rw [hnu, hnw] at h1
    rw [← huw, smul_add, h1, ← add_smul, hXeq]
  -- conclusion
  by_cases hdeg : lam = 0 ∨ X = 0
  · have hx₁z : x₁ = 0 ∧ X = 0 := by
      rcases hdeg with h | h
      · have hA00 : A = 0 := by rw [hAdef, h, zero_mul]
        have hB00 : B = 0 := by rw [hBdef, h, zero_mul]
        have h1 : x₁ ^ 2 + y₁ ^ 2 = 0 := by rw [← hA2, hA00]; ring
        have h2 : X ^ 2 + Yd ^ 2 = 0 := by rw [← hD2, hA00, hB00]; ring
        have h3 : x₁ ^ 2 = 0 := by linarith [sq_nonneg x₁, sq_nonneg y₁]
        have h4 : X ^ 2 = 0 := by linarith [sq_nonneg X, sq_nonneg Yd]
        exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h3, pow_eq_zero_iff two_ne_zero |>.mp h4⟩
      · exact ⟨by linarith, h⟩
    have hqp : q.fst = p.fst := by
      have h0 : ‖u‖ = 0 := by rw [hnu, hx₁z.1]
      have := norm_eq_zero.mp h0
      rw [hu] at this
      exact sub_eq_zero.mp this
    have hrp : r.fst = p.fst := by
      have h0 : ‖r.fst - p.fst‖ = 0 := by rw [← huw, hnuw, hx₁z.2]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    rw [hqp, hrp, sub_self, smul_zero, add_zero]
  · push Not at hdeg
    obtain ⟨hlam0, hX0'⟩ := hdeg
    have hba : 0 < b - a := by linarith
    -- `x₁ (A + B) = A X`, i.e. `(b - a) x₁ = (s - a) X`
    have hx₁X : (b - a) * x₁ = (s - a) * X := by
      have h1 : x₁ * (A + B) = A * X := by rw [hXeq]; linear_combination hratio
      rw [hAdef, hBdef] at h1
      have h2 : lam * ((b - a) * x₁) = lam * ((s - a) * X) := by linear_combination h1
      exact mul_left_cancel₀ hlam0 h2
    have hgoal : q.fst - p.fst = ((s - a) / (b - a)) • (r.fst - p.fst) := by
      have h1 : u = (x₁ / X) • (r.fst - p.fst) := by
        rw [div_eq_inv_mul, mul_smul, ← hsmul, smul_smul, inv_mul_cancel₀ hX0', one_smul]
      rw [← hu, h1]
      congr 1
      field_simp
      linear_combination hx₁X
    rw [← hgoal]
    abel

end GC.MetricGeometry
