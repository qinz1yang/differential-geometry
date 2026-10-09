import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# The metric step of FC16 (long tests control coordinate values)

Blueprint 207B, `lem:fibration-adapted-values` (FC16, B:1036). FC16's proof has a Riemannian
step and a metric step. The Riemannian step — `η_a + d_{q_a}` has differential at most
`K = √(4ε+ε²)` almost everywhere on `B(p,R)` (Riesz estimate along every minimizing direction to
`q_a`) and is therefore `K`-Lipschitz along the radial segment from `p` — needs the a.e.
first-variation formula for the Riemannian distance and the local gradient-to-Lipschitz theorem,
neither of which is in the tree; it is recorded as the obstruction of FC16.

This file proves the metric step completely: for the long test points `q_a` (lifts of the axis
points `(s eₐ, z₀)` from the coverage of the product approximation `φ = (u, z)`), the estimate
`|η_a(x) − η_a(p) − d(p,q_a) + d(x,q_a)| ≤ R K` on `B(p,R)` implies the row's conclusion
`|η(x) − η(p) − u(x)| ≤ √k (RK + 4δ + (R+δ)²/(2(s−R−δ)))`, using the distortion at the basepoint
and the Pythagoras estimate `0 ≤ D_a − (s − u_a(x)) ≤ (R+δ)²/(2(s−R−δ))`.
Conventions as in FC19: `ℓ²` product, coverage with a preimage within `δ`.
-/

open Metric
open scoped InnerProductSpace

namespace GC.MetricGeometry

variable {k : ℕ}

private theorem dist_toLp_sq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (a c : α) (b d : β) :
    dist (WithLp.toLp 2 (a, b) : WithLp 2 (α × β)) (WithLp.toLp 2 (c, d)) ^ 2 =
      dist a c ^ 2 + dist b d ^ 2 := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2]
  change ((dist a c ^ (2 : ℝ) + dist b d ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 = _
  rw [Real.rpow_two, Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

/-- The Pythagoras estimate of FC16 for the axis point `(s eₐ, z₀)`. -/
theorem axis_distance_sub_le {Z : Type*} [PseudoMetricSpace Z] (v : EuclideanSpace ℝ (Fin k))
    (w z₀ : Z) (a : Fin k) {s r : ℝ} (hr : dist (WithLp.toLp 2 (v, w) : WithLp 2 (_ × Z))
      (WithLp.toLp 2 (0, z₀)) ≤ r) (hs : r < s) :
    0 ≤ dist (WithLp.toLp 2 (v, w) : WithLp 2 (_ × Z))
        (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)) - (s - v a) ∧
      dist (WithLp.toLp 2 (v, w) : WithLp 2 (_ × Z))
        (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)) - (s - v a) ≤
        r ^ 2 / (2 * (s - r)) := by
  set D := dist (WithLp.toLp 2 (v, w) : WithLp 2 (_ × Z))
    (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀))
  have hD0 : 0 ≤ D := dist_nonneg
  have hr0 : 0 ≤ r := dist_nonneg.trans hr
  have hva : |v a| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v a
  have hnorm : ‖v‖ ^ 2 + dist w z₀ ^ 2 ≤ r ^ 2 := by
    have := dist_toLp_sq v 0 w z₀
    rw [dist_zero_right] at this
    rw [← this]
    exact pow_le_pow_left₀ dist_nonneg hr 2
  have hvr : ‖v‖ ≤ r := by nlinarith [sq_nonneg (dist w z₀), norm_nonneg v]
  have hsv : s - r ≤ s - v a := by linarith [(abs_le.mp (hva.trans hvr)).2]
  have hsv0 : 0 < s - v a := by linarith
  -- `D² = (s − vₐ)² + ρ²` with `0 ≤ ρ² ≤ r²`
  have hinner : ⟪v, s • EuclideanSpace.single a (1 : ℝ)⟫_ℝ = s * v a := by
    rw [real_inner_smul_right, EuclideanSpace.inner_single_right]; simp
  have hD2 : D ^ 2 = (s - v a) ^ 2 + (‖v‖ ^ 2 - v a ^ 2 + dist w z₀ ^ 2) := by
    have := dist_toLp_sq v (s • EuclideanSpace.single a (1 : ℝ)) w z₀
    have he1 : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1 := by simp
    rw [this, dist_eq_norm, norm_sub_sq_real, hinner, norm_smul, he1, mul_one, Real.norm_eq_abs,
      sq_abs]
    ring
  have hρ0 : 0 ≤ ‖v‖ ^ 2 - v a ^ 2 + dist w z₀ ^ 2 := by
    have : v a ^ 2 ≤ ‖v‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hva 2
    nlinarith [sq_nonneg (dist w z₀)]
  have hρr : ‖v‖ ^ 2 - v a ^ 2 + dist w z₀ ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg (v a)]
  have hDge : s - v a ≤ D := by
    have : (s - v a) ^ 2 ≤ D ^ 2 := by rw [hD2]; linarith
    exact (pow_le_pow_iff_left₀ hsv0.le hD0 two_ne_zero).mp this
  refine ⟨by linarith, ?_⟩
  have hsum : 2 * (s - r) ≤ D + (s - v a) := by linarith
  have hpos : 0 < 2 * (s - r) := by linarith
  have hkey : (D - (s - v a)) * (D + (s - v a)) = ‖v‖ ^ 2 - v a ^ 2 + dist w z₀ ^ 2 := by
    nlinarith [hD2]
  rw [le_div_iff₀ hpos]
  have hdiff0 : 0 ≤ D - (s - v a) := by linarith
  calc (D - (s - v a)) * (2 * (s - r)) ≤ (D - (s - v a)) * (D + (s - v a)) :=
        mul_le_mul_of_nonneg_left hsum hdiff0
    _ ≤ r ^ 2 := by rw [hkey]; exact hρr

/-- **FC16, metric step**: on `B(p,R)`, the per-component Riemannian estimate along the radial
segment for EVERY admissible long test point `q` (a preimage within `δ` of `(s eₐ, z₀)`) gives the
row's value bound. Only this Riemannian estimate (`hstep`) is supplied; distortion, coverage
and the Pythagoras estimate are proved. -/
theorem norm_coordinate_value_sub_le_of_long_tests {X Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Z] (u : X → EuclideanSpace ℝ (Fin k)) (z : X → Z)
    (η : X → EuclideanSpace ℝ (Fin k)) {p : X} {z₀ : Z} {R s H δ K : ℝ} (hR : 0 < R)
    (hδ : 0 ≤ δ) (hs : 2 * R + 4 * δ < s) (hH : s + R + 3 * δ < H) (hup : u p = 0)
    (hzp : z p = z₀)
    (hdist : ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      |dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) -
        dist x y| ≤ δ)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H - δ →
        ∃ y ∈ ball p H, dist (WithLp.toLp 2 (u y, z y)) q ≤ δ)
    (hstep : ∀ a : Fin k, ∀ q ∈ ball p H,
      dist (WithLp.toLp 2 (u q, z q) : WithLp 2 (_ × Z))
        (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)) ≤ δ →
      ∀ x ∈ ball p R, |η x a - η p a - dist p q + dist x q| ≤ R * K) :
    ∀ x ∈ ball p R, ‖η x - η p - u x‖ ≤
      Real.sqrt k * (R * K + 4 * δ + (R + δ) ^ 2 / (2 * (s - (R + δ)))) := by
  intro x hx
  set φ : X → WithLp 2 (EuclideanSpace ℝ (Fin k) × Z) := fun x => WithLp.toLp 2 (u x, z x)
  have hφp : φ p = WithLp.toLp 2 (0, z₀) := by simp only [φ, hup, hzp]
  have hxp : dist x p < R := mem_ball.mp hx
  have hpH : p ∈ ball p H := mem_ball_self (by linarith)
  have hxH : x ∈ ball p H := mem_ball.mpr (by linarith)
  set c : ℝ := R * K + 4 * δ + (R + δ) ^ 2 / (2 * (s - (R + δ)))
  have hcomp : ∀ a, |(η x - η p - u x) a| ≤ c := by
    intro a
    set tgt : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z) :=
      WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀)
    have hs0 : 0 ≤ s := by linarith
    have hptgt : dist (φ p) tgt = s := by
      have h := dist_toLp_sq (0 : EuclideanSpace ℝ (Fin k))
        (s • EuclideanSpace.single a (1 : ℝ)) z₀ z₀
      have he1 : ‖EuclideanSpace.single a (1 : ℝ)‖ = 1 := by simp
      rw [dist_self, dist_eq_norm, zero_sub, norm_neg, norm_smul, he1, mul_one,
        Real.norm_eq_abs, abs_of_nonneg hs0] at h
      rw [hφp]
      have := (pow_left_inj₀ dist_nonneg hs0 two_ne_zero).mp (by rw [h]; ring)
      exact this
    obtain ⟨q, hqH, hq⟩ := hcover tgt (by rw [← hφp, dist_comm, hptgt]; linarith)
    have hpq : |dist p q - s| ≤ 2 * δ := by
      have h1 := abs_le.mp (hdist p hpH q hqH)
      have h2 := dist_triangle (φ p) (φ q) tgt
      have h3 := dist_triangle (φ p) tgt (φ q)
      rw [dist_comm tgt (φ q)] at h3
      rw [abs_le]; constructor <;> linarith
    set D := dist (φ x) tgt
    have hxq : |dist x q - D| ≤ 2 * δ := by
      have h1 := abs_le.mp (hdist x hxH q hqH)
      have h2 := dist_triangle (φ x) (φ q) tgt
      have h3 := dist_triangle (φ x) tgt (φ q)
      rw [dist_comm tgt (φ q)] at h3
      rw [abs_le]; constructor <;> linarith
    have hφx : dist (φ x) (WithLp.toLp 2 (0, z₀)) ≤ R + δ := by
      rw [← hφp]; linarith [(abs_le.mp (hdist x hxH p hpH)).2]
    obtain ⟨hpy0, hpy1⟩ := axis_distance_sub_le (u x) (z x) z₀ a (s := s) hφx (by linarith)
    have hpy0' : 0 ≤ D - (s - u x a) := hpy0
    have hpy1' : D - (s - u x a) ≤ (R + δ) ^ 2 / (2 * (s - (R + δ))) := hpy1
    have hstepx := hstep a q hqH hq x hx
    have hsplit : (η x - η p - u x) a = (η x a - η p a - dist p q + dist x q) + (dist p q - s) +
        (D - dist x q) + ((s - u x a) - D) := by
      simp only [PiLp.sub_apply]; ring
    rw [hsplit]
    have e1 := abs_le.mp hstepx
    have e2 := abs_le.mp hpq
    have e3 := abs_le.mp hxq
    rw [show c = R * K + 4 * δ + (R + δ) ^ 2 / (2 * (s - (R + δ))) from rfl, abs_le]
    constructor <;> linarith
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [EuclideanSpace.norm_eq]
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hcomp ⟨0, hk⟩)
  have hsq : ‖η x - η p - u x‖ ^ 2 ≤ (Real.sqrt k * c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    calc ∑ a, ‖(η x - η p - u x) a‖ ^ 2 ≤ (Finset.univ : Finset (Fin k)).card • c ^ 2 := by
          refine Finset.sum_le_card_nsmul _ _ _ fun a _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcomp a) 2
      _ = k * c ^ 2 := by rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end GC.MetricGeometry
