import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]
variable {p : X} {a : A} {b : B} {j k : ℕ} {δ ε τ : ℝ}

def SplittingCompatible
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) ε)
    (τ : ℝ) : Prop :=
  j ≤ k ∧ ∃ Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))),
    ∃ E : KleinerLottApprox (0 : EuclideanSpace ℝ (Fin j)) 0 τ,
    ∃ F : KleinerLottApprox
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), b)) a τ,
    ∀ x ∈ ball p τ⁻¹,
      dist (WithLp.toLp 2 (E.toFun (Q (ψ.toFun x).fst).fst,
        F.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd))))
        (φ.toFun x) ≤ τ

theorem splittingCompatible_of_exact_factorization
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b)) ε)
    (hjk : j ≤ k) (hτ : 0 < τ) (hτone : τ < 1)
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A)
    (hH : H (WithLp.toLp 2 (0, b)) = a)
    (hfactor : ∀ x ∈ ball p τ⁻¹, φ.toFun x =
      WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst,
        H (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))) :
    SplittingCompatible φ ψ τ := by
  refine ⟨hjk, Q, (IsometryEquiv.refl _).toKleinerLottApprox rfl hτ hτone,
    H.toKleinerLottApprox hH hτ hτone, ?_⟩
  intro x hx
  change dist (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst,
    H (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd)))) (φ.toFun x) ≤ τ
  rw [← hfactor x hx, dist_self]
  exact hτ.le

end GC.MetricGeometry
