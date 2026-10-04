import DifferentialGeometry.Geometry.Metric.Approximation.LongTestValues

/-!
# Consumer of the FC16 metric step: exact product data

With an exactly isometric, exactly covering product map (`δ = 0`) and an exact radial step
(`K = 0`), the coordinate differs from the product coordinate by at most `√k R²/(2(s − R))`,
which tends to zero as the long test length `s` grows (the order of choices in the blueprint).
-/

set_option autoImplicit false

open Metric

namespace GC.MetricGeometry

variable {k : ℕ}

theorem norm_coordinate_value_sub_le_of_exact_long_tests {X Z : Type*} [PseudoMetricSpace X]
    [MetricSpace Z] (u : X → EuclideanSpace ℝ (Fin k)) (z : X → Z)
    (η : X → EuclideanSpace ℝ (Fin k)) {p : X} {z₀ : Z} {R s H : ℝ} (hR : 0 < R)
    (hs : 2 * R < s) (hH : s + R < H) (hup : u p = 0) (hzp : z p = z₀)
    (hiso : ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) = dist x y)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin k) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H → ∃ y ∈ ball p H, WithLp.toLp 2 (u y, z y) = q)
    (hstep : ∀ a : Fin k, ∀ q ∈ ball p H,
      WithLp.toLp 2 (u q, z q) = (WithLp.toLp 2 (s • EuclideanSpace.single a (1 : ℝ), z₀) :
        WithLp 2 (_ × Z)) →
      ∀ x ∈ ball p R, η x a - η p a = dist p q - dist x q) :
    ∀ x ∈ ball p R, ‖η x - η p - u x‖ ≤ Real.sqrt k * (R ^ 2 / (2 * (s - R))) := by
  intro x hx
  have h := norm_coordinate_value_sub_le_of_long_tests u z η (R := R) (s := s) (H := H)
    (δ := 0) (K := 0) hR le_rfl (by linarith) (by linarith) hup hzp
    (fun x hx y hy => by rw [hiso x hx y hy, sub_self, abs_zero])
    (fun q hq => by
      obtain ⟨y, hy, hyq⟩ := hcover q (by simpa using hq)
      exact ⟨y, hy, by rw [hyq, dist_self]⟩)
    (fun a q hq hqd x hx => by
      rw [hstep a q hq (dist_le_zero.mp hqd) x hx]; simp) x hx
  simpa using h

end GC.MetricGeometry
