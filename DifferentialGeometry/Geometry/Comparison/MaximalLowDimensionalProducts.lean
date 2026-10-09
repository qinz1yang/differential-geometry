import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProduct
import DifferentialGeometry.Geometry.Comparison.LowDimensionalProducts

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

universe u v
variable {X : Type u} {Z : Type v} [MetricSpace X] [CompleteSpace X] [MetricSpace Z]

theorem exists_product_model_of_maximal_splitting {n k : ℕ} (hn : 1 ≤ n)
    (hcodim : n - k ≤ 1)
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ n)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (p : X)
    (hmax : ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ (w : W) (F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × W)),
        F p = WithLp.toLp 2 (0, w)) :
    (∃ F : X ≃ᵢ EuclideanSpace ℝ (Fin k), ∀ x, F x = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) := by
  rcases e.exists_product_model_of_nonnegative_comparison hn hcodim hsegments hcomp hdim p with
    hzero | ⟨F, _, _⟩ | hray | hinterval | hcircle
  · exact Or.inl hzero
  · exact (hmax (F.exists_pointed_successor_splitting_of_l2_real_product p)).elim
  · exact Or.inr (Or.inl hray)
  · exact Or.inr (Or.inr (Or.inl hinterval))
  · exact Or.inr (Or.inr (Or.inr hcircle))

theorem exists_product_model_of_maximal_real_splitting
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 2)
    (e : X ≃ᵢ WithLp 2 (ℝ × Z)) (p : X)
    (hmax : ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ (w : W) (F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 2) × W)),
        F p = WithLp.toLp 2 (0, w)) :
    (∃ F : X ≃ᵢ ℝ, ∀ x, F x = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (ℝ × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (ℝ × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) := by
  rcases e.exists_product_model_of_real_splitting_dimH_le_two hsegments hcomp hdim p with
    hzero | ⟨F, _, _⟩ | hray | hinterval | hcircle
  · exact Or.inl hzero
  · let v : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) :=
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv
    let F' := F.trans (withLpProdCongr 2 v (IsometryEquiv.refl ℝ))
    exact (hmax (F'.exists_pointed_successor_splitting_of_l2_real_product p)).elim
  · exact Or.inr (Or.inl hray)
  · exact Or.inr (Or.inr (Or.inl hinterval))
  · exact Or.inr (Or.inr (Or.inr hcircle))

end IsometryEquiv
