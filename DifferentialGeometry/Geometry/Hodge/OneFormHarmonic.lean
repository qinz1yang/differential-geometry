import DifferentialGeometry.Geometry.Curvature.EinsteinMetric
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


set_option linter.unusedVariables false in
def OneFormIsClosed
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ (x : M) (X Y : TangentSpace I x),
    nablaAlpha x (vec2 (I := I) X Y) = nablaAlpha x (vec2 (I := I) Y X)


def oneFormCodifferentialAt
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) (x : M) : Real :=
  -(metricTracePair0SAt (I := I) g (nablaAlpha x))


def OneFormIsCoclosed
    (g : SmoothRiemannianMetric I M)
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, oneFormCodifferentialAt (I := I) g nablaAlpha x = 0


def IsHarmonicOneForm
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  NablaOneFormSectionRealizes (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha ∧
    OneFormIsClosed (I := I) α nablaAlpha ∧
    OneFormIsCoclosed (I := I) g nablaAlpha


theorem IsHarmonicOneForm.realizes
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    NablaOneFormSectionRealizes (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha :=
  h.1


theorem IsHarmonicOneForm.closed
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    OneFormIsClosed (I := I) α nablaAlpha :=
  h.2.1


theorem IsHarmonicOneForm.coclosed
    {g : SmoothRiemannianMetric I M}
    {α : OneFormSection (I := I) (M := M)}
    {nablaAlpha : TwoTensorSection (I := I) (M := M)}
    (h : IsHarmonicOneForm (I := I) g α nablaAlpha) :
    OneFormIsCoclosed (I := I) g nablaAlpha :=
  h.2.2


theorem isHarmonicOneForm_roughLap_eq_ricciSharp
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
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) =
        metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (cotangentSharp (I := I) g x (α x)) X) := sorry


theorem isHarmonicOneForm_einstein_roughLap_eigen
    (g : SmoothRiemannianMetric I M)
    (α : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (κ : Real)
    (hEin : IsEinsteinMetric (I := I) g κ)
    (hHarm : IsHarmonicOneForm (I := I) g α nablaAlpha)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) α nablaAlpha x
        (nabla2Alpha x)) :
    ∀ (x : M) (X : TangentSpace I x),
      roughLap0STensor (I := I) g (s := 1) (nabla2Alpha x) (fun _ : Fin 1 => X) =
        κ * α x (fun _ : Fin 1 => X) := sorry

end DifferentialGeometry.Integral.Connection
