import RicciFlower.Riemann.Basic
import RicciFlower.LeviCivita.Torsion

/-!
# Second covariant derivatives and curvature

This file records the vector-field computation behind Remark 14.8.  The
torsion-free curvature formula is exposed as a corollary of the general
torsion-correction identity.
-/

suppress_compilation

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Bundle RicciFlower.Curvature
open scoped Manifold ContDiff

namespace RicciFlower.Riemann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The second covariant derivative of a vector field in two vector-field
directions:
`(nabla^2 Z)(X,Y) = nabla_X (nabla_Y Z) - nabla_{nabla_X Y} Z`. -/
def nabla2VectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun p : M => (cov Z p) (Y p)) x) (X x) -
      (cov Z x) ((cov Y x) (X x))

@[simp]
theorem nabla2VectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
    nabla2VectorField (I := I) cov X Y Z x =
      (cov (fun p : M => (cov Z p) (Y p)) x) (X x) -
        (cov Z x) ((cov Y x) (X x)) :=
  rfl

/-- Skewing the second covariant derivative gives curvature with the standard
torsion correction. -/
theorem nabla2VectorField_skew_eq_curvature_sub_torsion
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x =
      connectionRiemannCurvatureField (I := I) cov X Y Z x -
        (cov Z x) (cov.torsion x (X x) (Y x)) := by
  rw [cov.torsion_apply hX hY]
  unfold nabla2VectorField connectionRiemannCurvatureField
  simp [sub_eq_add_neg, map_add, add_assoc, add_left_comm, add_comm]
  abel

/-- Corrected Remark 14.8: for a torsion-free pair of directions at `x`,
curvature is the skew of the second covariant derivative. -/
theorem connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0) :
    connectionRiemannCurvatureField (I := I) cov X Y Z x =
      nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x := by
  have h :=
    nabla2VectorField_skew_eq_curvature_sub_torsion
      (I := I) cov (X := X) (Y := Y) (Z := Z) (x := x) hX hY
  rw [htor, map_zero, sub_zero] at h
  exact h.symm

/-- The same torsion-free formula stated for the auxiliary Riemann operator used
to construct the pointwise curvature tensor. -/
theorem riemannCurvatureAux_eq_nabla2VectorField_skew_of_torsion_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0) :
    CovariantDerivative.riemannCurvatureAux (I := I) cov X Y Z x =
      nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x := by
  rw [CovariantDerivative.riemannCurvatureAux_eq_connectionRiemannCurvatureField]
  exact connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (I := I) cov hX hY htor

/-- Levi-Civita specialization: curvature is the skew of the second covariant
derivative, with the torsion correction discharged by the constructed
Levi-Civita connection. -/
theorem leviCivita_connectionRiemannCurvatureField_eq_nabla2VectorField_skew
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    connectionRiemannCurvatureField (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) X Y Z x =
      nabla2VectorField (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) X Y Z x -
        nabla2VectorField (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) Y X Z x := by
  refine connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (I := I) (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) hX hY ?_
  have htf :=
    LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  change (LeviCivita.leviCivitaConnectionOfMetric (I := I) g).torsion x
    (X x) (Y x) = 0
  rw [htf x]
  simp

end RicciFlower.Riemann

