import DifferentialGeometry.Geometry.Metric.Approximation.CommonEndpointTests

/-!
# Consumer of FC19: exact product data give an exact derivative comparison

If the product map is an exact isometry onto a covered target (`δ = 0`), the raw coordinate is
exactly affine in `u` (`E = 0`) and the long tests are exact (`α = 0`), then FC19's directional
step gives `dF = A ∘ dG` at every point of the tested ball.
-/

set_option autoImplicit false

open Metric

namespace GC.MetricGeometry

variable {k m : ℕ}

theorem fderiv_eq_comp_of_exact_common_endpoints {X Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Z] {TX : X → Type*} [∀ x, NormedAddCommGroup (TX x)]
    [∀ x, InnerProductSpace ℝ (TX x)] [∀ x, CompleteSpace (TX x)]
    (u : X → EuclideanSpace ℝ (Fin m)) (z : X → Z) (Ψ : X → EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (b₀ : EuclideanSpace ℝ (Fin k)) {p : X} {z₀ : Z} {L T s H : ℝ} (hT : 0 ≤ T)
    (hs : T < s) (hH : L + s < H) (hup : u p = 0) (hzp : z p = z₀)
    (hiso : ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      dist (WithLp.toLp 2 (u x, z x) : WithLp 2 (_ × Z)) (WithLp.toLp 2 (u y, z y)) = dist x y)
    (hcover : ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin m) × Z),
      dist q (WithLp.toLp 2 (0, z₀)) < H → ∃ y ∈ ball p H, WithLp.toLp 2 (u y, z y) = q)
    (hΨ : ∀ x ∈ ball p H, Ψ x = A (u x) + b₀)
    (W : ∀ x : X, X → Set (TX x)) (hW : ∀ x y, x ≠ y → (W x y).Nonempty)
    (hWunit : ∀ x y, ∀ w ∈ W x y, ‖w‖ = 1)
    (dF : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin k)) (dG : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hF : ∀ x ∈ ball p L, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1)
    (hG : ∀ x ∈ ball p L, ‖dG x‖ ≤ 1)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      dF x w = (dist x y)⁻¹ • (Ψ y - Ψ x))
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      dG x w = (dist x y)⁻¹ • (u y - u x)) :
    ∀ x ∈ ball p L, dF x = A.comp (dG x) := by
  intro x hx
  have h := norm_sub_comp_le_of_common_endpoints u z Ψ A hA b₀ (L := L) (T := T) (s := s) (H := H) (δ := 0) (E := 0)
    (α := 0) hT
    le_rfl le_rfl le_rfl
    (by linarith) (by linarith) hup hzp (fun x hx y hy => by rw [hiso x hx y hy]; simp)
    (fun q hq => by
      obtain ⟨y, hy, hyq⟩ := hcover q (by simpa using hq)
      exact ⟨y, hy, by rw [hyq, dist_self]⟩)
    (fun x hx => by rw [hΨ x hx]; simp) W hW hWunit dF dG (by simpa using hF) (by simpa using hG)
    (fun x hx y hy hT w hw => by rw [htestF x hx y hy hT w hw, sub_self, norm_zero])
    (fun x hx y hy hT w hw => by rw [htestG x hx y hy hT w hw, sub_self, norm_zero]) x hx
  norm_num at h
  exact sub_eq_zero.mp h

end GC.MetricGeometry
