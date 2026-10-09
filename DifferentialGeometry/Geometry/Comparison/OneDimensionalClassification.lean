import DifferentialGeometry.Geometry.Comparison.GlobalOneDimensionalModels
import DifferentialGeometry.Topology.MetricSpace.ModelTypeUniqueness
import DifferentialGeometry.Topology.MetricSpace.ModelParameterRigidity

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem pointed_one_dimensional_classification
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) (p : X) :
    ((∃ e : X ≃ᵢ EuclideanSpace ℝ (Fin 0), e p = 0) ∨
    (∃ e : X ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : X ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ AddCircle L, e p = 0)) ∧
    List.Pairwise (fun A B : Prop => ¬ (A ∧ B))
      [Nonempty (X ≃ᵢ EuclideanSpace ℝ (Fin 0)),
       Nonempty (X ≃ᵢ ℝ),
       Nonempty (X ≃ᵢ Ici (0 : ℝ)),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ Icc (0 : ℝ) L),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ AddCircle L)] := by
  exact ⟨exists_pointed_one_dimensional_model hcurves hcomp hdim p,
    one_dimensional_model_types_pairwise⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
