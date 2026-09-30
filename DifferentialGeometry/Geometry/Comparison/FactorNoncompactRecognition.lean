import DifferentialGeometry.Geometry.Comparison.NoncompactRecognition
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

theorem exists_line_or_ray_product_of_noncompact_factor [CompleteSpace X]
    (e : X ≃ᵢ WithLp 2 (E × Y))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set Y) ≤ 1) (hnot : ¬ IsCompact (univ : Set Y)) (p : X) :
    (∃ F : X ≃ᵢ WithLp 2 (E × ℝ), (F p).snd = 0 ∧ ∀ x, (F x).fst = (e x).fst) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)),
      ((F p).snd : ℝ) = a ∧ ∀ x, (F x).fst = (e x).fst) := by
  let := e.completeSpace_l2_product_factor (e p).fst
  rcases exists_line_or_ray_isometry_of_not_isCompact_of_geodesic_dimH_le_one
      (e.exists_segment_l2_product_factor (e p).fst hsegments)
      (fourPointComparison_l2_product_factor hcomp e (e p).fst) hdim hnot (e p).snd with
    ⟨φ, hφ⟩ | ⟨a, ha, φ, hφ⟩
  · let F : X ≃ᵢ WithLp 2 (E × ℝ) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inl ⟨F, hφ, fun _ => rfl⟩
  · let F : X ≃ᵢ WithLp 2 (E × Ici (0 : ℝ)) :=
      e.trans (withLpProdCongr 2 (IsometryEquiv.refl E) φ)
    exact Or.inr ⟨a, ha, F, hφ, fun _ => rfl⟩

end IsometryEquiv
