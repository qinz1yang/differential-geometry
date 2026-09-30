import DifferentialGeometry.Geometry.Comparison.GlobalPolynomialCovering
import DifferentialGeometry.Geometry.Comparison.FactorGlobalModels
import DifferentialGeometry.Geometry.Comparison.EuclideanFactorDimension

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X Z : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Z]

theorem euclidean_factor_dimension_of_nonnegative_comparison {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z) :
    k ≤ n ∧ dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) := by
  have hk : k ≤ n := by
    have h := (e.euclidean_rank_le_dimH z).trans hdim
    exact_mod_cast h
  exact ⟨hk, e.dimH_euclidean_factor_le hk (e.symm (WithLp.toLp 2 (0, z))) z
    (by simp) (polynomial_nets_of_nonnegative_comparison hcurves hcomp hn hdim _)⟩

theorem exists_pointed_euclidean_of_nonnegative_comparison {n : ℕ} (hn : 1 ≤ n)
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin n) × Z))
    (p : X) (z : Z) (hp : e p = WithLp.toLp 2 (0, z)) :
    ∃ F : X ≃ᵢ EuclideanSpace ℝ (Fin n), F p = 0 := by
  exact e.exists_pointed_isometryEquiv_euclidean_of_splitting p z hp hsegments
    (polynomial_nets_of_nonnegative_comparison
      (arbitrarily_short_curves_of_metric_segments hsegments) hcomp hn hdim p)

theorem exists_product_model_of_nonnegative_comparison {n k : ℕ} (hn : 1 ≤ n)
    (hcodim : n - k ≤ 1)
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (p : X) :
    (∃ F : X ≃ᵢ EuclideanSpace ℝ (Fin k), ∀ x, F x = (e x).fst) ∨
    (∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) := by
  have hd := (e.euclidean_factor_dimension_of_nonnegative_comparison hn
    (arbitrarily_short_curves_of_metric_segments hsegments) hcomp hdim (e p).snd).2
  have hd' : dimH (univ : Set Z) ≤ (n - k : ℕ) := by
    simpa only [ENNReal.ofReal_natCast] using hd
  exact e.exists_product_model_of_dimH_factor_le_one hsegments hcomp
    (hd'.trans (by exact_mod_cast hcodim)) p

end IsometryEquiv
