import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def swapSlots0S {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  T.domDomCongr (Equiv.swap (0 : Fin 2) 1)


def symmetricPart0S {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (2 : Real)⁻¹ • (T + swapSlots0S (I := I) T)


def antisymmetricPart0S {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (2 : Real)⁻¹ • (T - swapSlots0S (I := I) T)


def traceFreePart0S (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  T - ((Module.finrank Real E : Real)⁻¹ * metricTracePair0SAt (I := I) g T) • metricTensor0S (I := I) g x


def ahlforsOperator (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  traceFreePart0S (I := I) g (symmetricPart0S (I := I) T)


def covectorTensorProd0S {x : M}
    (a b : TangentSpace I x →L[Real] Real) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
    (a.smulRight b)).uncurryLeft


end DifferentialGeometry.Integral.Connection
