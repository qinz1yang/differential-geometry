import DifferentialGeometry.Geometry.Comparison.GlobalOneDimensionalModels
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

theorem exists_product_model_of_dimH_factor_le_one [CompleteSpace X]
    (e : X ≃ᵢ WithLp 2 (E × Y))
    (hsegments : ∀ x y : X, ∃ f : unitInterval → X,
      Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set Y) ≤ 1) (p : X) :
    (∃ F : X ≃ᵢ E, ∀ x, F x = (e x).fst) ∨
    (∃ F : X ≃ᵢ WithLp 2 (E × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L,
      ∃ F : X ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L),
        ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ F : X ≃ᵢ WithLp 2 (E × AddCircle L),
      (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) := by
  let := e.completeSpace_l2_product_factor (e p).fst
  rcases exists_pointed_one_dimensional_model
      (arbitrarily_short_curves_of_metric_segments
        (e.exists_segment_l2_product_factor (e p).fst hsegments))
      (fourPointComparison_l2_product_factor hcomp e (e p).fst) hdim (e p).snd with
    ⟨φ, _⟩ | ⟨φ, hφ⟩ | ⟨a, ha, φ, hφ⟩ | ⟨L, hL, a, ha, φ, hφ⟩ | ⟨L, hL, φ, hφ⟩
  · let F : X ≃ᵢ E :=
      (e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)).trans
        (withLpProdUnique 2 E (EuclideanSpace ℝ (Fin 0)))
    exact Or.inl ⟨F, fun _ => rfl⟩
  · let F : X ≃ᵢ WithLp 2 (E × ℝ) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inr (Or.inl ⟨F, hφ, fun _ => rfl⟩)
  · let F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inr (Or.inr (Or.inl ⟨a, ha, F, hφ, fun _ => rfl⟩))
  · let F : X ≃ᵢ WithLp 2 (E × Icc (0 : ℝ) L) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨L, hL, a, ha, F, hφ, fun _ => rfl⟩)))
  · let F : X ≃ᵢ WithLp 2 (E × AddCircle L) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨L, hL, F, hφ, fun _ => rfl⟩)))

end IsometryEquiv
