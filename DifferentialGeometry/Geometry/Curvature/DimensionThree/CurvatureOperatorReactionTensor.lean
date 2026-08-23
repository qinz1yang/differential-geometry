import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorCone
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorReaction
import DifferentialGeometry.Tensor.RSTensor.CoordinateBasis

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {x : M}

private def componentSlots4 (a b c d : Fin 3) : Fin 4 → Fin 3 :=
  fun i ↦ if i = 0 then a else if i = 1 then b else if i = 2 then c else d

private def fin4SlotsEquiv :
    (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := componentSlots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [componentSlots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [componentSlots4]

private theorem sum_fin_four_fun
    (F : (Fin 4 → Fin 3) → Real) :
    (∑ s : Fin 4 → Fin 3, F s) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        F (componentSlots4 a b c d) := by
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) ↦
      F (componentSlots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro s
    have hslot :
        componentSlots4 (fin4SlotsEquiv s).1.1.1 (fin4SlotsEquiv s).1.1.2
          (fin4SlotsEquiv s).1.2 (fin4SlotsEquiv s).2 = s := by
      change fin4SlotsEquiv.symm (fin4SlotsEquiv s) = s
      exact fin4SlotsEquiv.left_inv s
    rw [hslot]

theorem tensor04StdAt_eq_curvatureTensorEval3_of_components
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : Tensor04At (I := I) (M := M) x)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M) A
        (basis a) (basis b) (basis c) (basis d) = R a b c d)
    (v w z u : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) A v w z u =
      DifferentialGeometry.Dim3Reaction.curvatureTensorEval3 R
        (fun a ↦ basis.coord a v) (fun a ↦ basis.coord a w)
        (fun a ↦ basis.coord a z) (fun a ↦ basis.coord a u) := by
  unfold tensor04StdAt
  rw [tensor0S_apply_eq_sum (I := I) basis A (vec4 (I := I) v w z u)]
  rw [sum_fin_four_fun]
  unfold DifferentialGeometry.Dim3Reaction.curvatureTensorEval3
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcomp' : component0S (I := I) basis A (componentSlots4 a b c d) =
      R a b c d := by
    rw [component0S_apply]
    change A (fun i ↦ basis (componentSlots4 a b c d i)) = R a b c d
    rw [← hcomp a b c d]
    unfold tensor04StdAt
    congr 1
    funext i
    fin_cases i <;> simp [componentSlots4, vec4]
  rw [hcomp']
  rw [Fin.prod_univ_four]
  simp [componentSlots4, vec4]
  ring

theorem algebraicCurvatureOperatorQuadraticEval_eq_curvatureOperatorQuadraticEval3_of_components
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real)
    (hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d) = R a b c d)
    {n : Nat} (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w =
      DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3 R c
        (fun i a ↦ basis.coord a (v i))
        (fun i a ↦ basis.coord a (w i)) := by
  unfold algebraicCurvatureOperatorQuadraticEval
    DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [tensor04StdAt_eq_curvatureTensorEval3_of_components basis
    (A : Tensor04At (I := I) (M := M) x) R hcomp]

theorem algebraicCurvatureOperatorNonnegative_of_components_eq_rm
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d) =
          DifferentialGeometry.Dim3Reaction.rm
            (DifferentialGeometry.Dim3Reaction.ricciFromSectional3 K12 K13 K23)
            a b c d) :
    A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  rw [algebraicCurvatureOperatorQuadraticEval_eq_curvatureOperatorQuadraticEval3_of_components
    basis A _ hcomp]
  exact DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_rm_nonneg
    K12 K13 K23 h12 h13 h23 c _ _

theorem algebraicCurvatureOperatorNonnegative_of_components_eq_reaction
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (K12 K13 K23 : Real) (h12 : 0 ≤ K12) (h13 : 0 ≤ K13) (h23 : 0 ≤ K23)
    (hcomp : ∀ a b c d,
      tensor04StdAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis a) (basis b) (basis c) (basis d) =
          DifferentialGeometry.Dim3Reaction.curvatureTensorReaction3
            K12 K13 K23 a b c d) :
    A ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  rw [algebraicCurvatureOperatorQuadraticEval_eq_curvatureOperatorQuadraticEval3_of_components
    basis A _ hcomp]
  exact DifferentialGeometry.Dim3Reaction.curvatureOperatorQuadraticEval3_reaction_nonneg
    K12 K13 K23 h12 h13 h23 c _ _

end DifferentialGeometry.Geometry.Curvature
