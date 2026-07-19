import DifferentialGeometry.Geometry.Surface.TensorTraceFree
import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Geometry.Hodge.Codifferential
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HeatProbeEnergy

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open MeasureTheory
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Forms
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


def oneFormReaction2D (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  let gradK : TangentSpace I x := gradFun (I := I) g (gaussCurvature (I := I) g) x
  let dKcov : TangentSpace I x →L[Real] Real := g.inner x gradK
  let hcov : TangentSpace I x →L[Real] Real := g.inner x (cotangentSharp (I := I) g x hx)
  covectorTensorProd0S (I := I) dKcov hcov
    + covectorTensorProd0S (I := I) hcov dKcov
    - (hcov gradK) • metricTensor0S (I := I) g x


theorem oneFormReaction2D_eq_ricciVariation
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (hx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaRic : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRic : ∀ Y V W : TangentSpace I x,
      nablaRic (vec3 (I := I) Y V W) =
        extDerivFun (I := I) (gaussCurvature (I := I) g) x Y * g.inner x V W) :
    oneFormReaction2D (I := I) g hx =
      DifferentialGeometry.PDE.RicciFlow.Evolution.HeatProbeEnergy.ricciVariationOneFormReaction
        (I := I) g x nablaRic hx := by
  sorry


theorem gradNormSq_decomposition_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    normSq0S (I := I) g x 2 T =
      normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g T)
        + normSq0S (I := I) g x 2 (antisymmetricPart0S (I := I) T)
        + (2 : Real)⁻¹ * metricTracePair0SAt (I := I) g T ^ 2 := by
  sorry


theorem ahlfors_identity_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Dh : Tensor0SSection (I := I) (M := M) 2)
    (nablaDh : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hDh : ∀ y : M, Dh y = ahlforsOperator (I := I) g (nablaH y))
    (hnablaDh : ∀ x : M,
      Nabla0SRealizesAt (I := I) 2 (metricCov (I := I) (M := M) g) Dh nablaDh x)
    (x : M) :
    (2 : Real) • metricTraceFirstTwo0STensor (I := I) g (s := 1) (nablaDh x) =
      roughLap0STensor (I := I) g (s := 1) (nabla2H x)
        + gaussCurvature (I := I) g x • (h x) := by
  sorry


theorem curvatureEnergyIdentity_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x)) :
    (∫ x, normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      =
      (∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x)
              + gaussCurvature (I := I) g x • (h x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (2 : Real) * (∫ x, gaussCurvature (I := I) g x *
              normSq0S (I := I) g x 2 (ahlforsOperator (I := I) g (nablaH x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        + (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
              normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  sorry


theorem curvatureEnergyInequality_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hKpos : ∀ x : M, 0 ≤ gaussCurvature (I := I) g x) :
    (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      + (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
            normSq0S (I := I) g x 1 (h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      ≤
      (∫ x, normSq0S (I := I) g x 1
          (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  sorry


theorem curvatureEnergyEquality_iff_ahlforsZero_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hK : ContMDiff I 𝓘(Real, Real) ∞ (gaussCurvature (I := I) g))
    (hRealizes1 : NablaOneFormSectionRealizes (I := I)
      (metricCov (I := I) (M := M) g) h nablaH)
    (hRealizes2 : ∀ x : M,
      Nabla2OneFormRealizesAt (I := I) (metricCov (I := I) (M := M) g) h nablaH x (nabla2H x))
    (hKpos : ∀ x : M, 0 ≤ gaussCurvature (I := I) g x) :
    ((∫ x, normSq0S (I := I) g x 1
            (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = (2 : Real)⁻¹ * (∫ x, formLaplacianScalar (I := I) g hK x *
              normSq0S (I := I) g x 1 (h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)))
      ↔ (∀ x : M, ahlforsOperator (I := I) g (nablaH x) = 0) := by
  sorry


end DifferentialGeometry.Integral.Connection
