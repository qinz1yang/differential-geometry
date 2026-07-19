import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


def oneFormExtDerivAt
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  nablaAlpha x -
    Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel (nablaAlpha x)))


theorem oneFormIsClosed_iff_extDerivAt_eq_zero
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) :
    OneFormIsClosed (I := I) α nablaAlpha ↔
      ∀ x : M,
        oneFormExtDerivAt (I := I) nablaAlpha x =
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  sorry


def nablaOneFormExtDerivAt
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  nabla2Alpha x -
    Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 3) 2)
        (Tensor0SSpace.toModel (nabla2Alpha x)))


def oneFormHodgeLaplacianAt
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I)
      (fun y : M => oneFormCodifferentialAt (I := I) g nablaAlpha y) x -
    roughLap0STensor (I := I) g (s := 1)
      (nablaOneFormExtDerivAt (I := I) nabla2Alpha x)


theorem oneFormWeitzenbockIdentity
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x
          (fun _ : Fin 1 => X) =
        -roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) :=
  sorry


theorem isHarmonicOneForm_hodgeLaplacianAt_eq_zero
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hHarm : IsHarmonicOneForm (I := I) g α nablaAlpha)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      oneFormHodgeLaplacianAt (I := I) g nablaAlpha nabla2Alpha x
          (fun _ : Fin 1 => X) = 0 :=
  sorry


end DifferentialGeometry.Integral.Connection
