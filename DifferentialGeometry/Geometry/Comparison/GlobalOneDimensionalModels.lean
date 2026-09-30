import DifferentialGeometry.Geometry.Comparison.CompactRecognition
import DifferentialGeometry.Geometry.Comparison.NoncompactRecognition

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem exists_pointed_one_dimensional_model
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) (p : X) :
    (∃ e : X ≃ᵢ EuclideanSpace ℝ (Fin 0), e p = 0) ∨
    (∃ e : X ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : X ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ AddCircle L, e p = 0) := by
  classical
  rcases subsingleton_or_nontrivial X with hsub | hnontrivial
  · let := hsub
    let e : X ≃ᵢ EuclideanSpace ℝ (Fin 0) :=
      { toFun := fun _ => 0
        invFun := fun _ => p
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        isometry_toFun := isometry_subsingleton }
    exact Or.inl ⟨e, rfl⟩
  · let := hnontrivial
    by_cases hc : IsCompact (univ : Set X)
    · let : CompactSpace X := ⟨hc⟩
      have hsegments := exists_metric_segment_of_approximate_midpoints
        (approximate_midpoints_of_arbitrarily_short_curves hcurves)
      rcases exists_interval_or_circle_isometry_of_compact_dimH_le_one hsegments hcomp hdim p with hi | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
    · rcases exists_line_or_ray_isometry_of_not_isCompact_of_dimH_le_one hcurves hcomp hdim hc p with hl | hr
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Or.inl hr))

end DifferentialGeometry.Geometry.Comparison.Toponogov
