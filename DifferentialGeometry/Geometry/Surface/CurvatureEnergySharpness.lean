import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open MeasureTheory
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open Metric
open scoped Manifold ContDiff BigOperators

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

def curvatureEnergy (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) : Real :=
  (∫ x, normSq0S (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
    - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
    - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))

end General

section Sphere

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sphereHeight (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) : Real :=
  innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2)
    (EuclideanSpace.single (2 : Fin 3) (1 : Real)) p

theorem sphereHeight_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ sphereHeight :=
  (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2)
    (EuclideanSpace.single (2 : Fin 3) (1 : Real))).contMDiff

def legendreConformalFactor (ε : Real)
    (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) : Real :=
  ε * ((3 * sphereHeight p ^ 2 - 1) / 2)

theorem legendreConformalFactor_contMDiff (ε : Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (legendreConformalFactor ε) :=
  contMDiff_const.mul
    (((contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).sub contMDiff_const).div_const 2)

def sphereConformalMetric (ε : Real) :
    SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))

def sphereHeightOneForm :
    OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff

def sphereConformalDerivs (ε : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) sphereHeightOneForm :=
  CanonicalSpatialDerivs0S.of_smooth_connection
    (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
    (metricCov_smooth (I := 𝓡 2) (sphereConformalMetric ε))
    sphereHeightOneForm

def sphereCurvatureEnergy (ε : Real) : Real :=
  curvatureEnergy (sphereConformalMetric ε) sphereHeightOneForm
    (sphereConformalDerivs ε).nablaA
    (fun x => (sphereConformalDerivs ε).nabla2A x)

theorem sphereCurvatureEnergy_zero : sphereCurvatureEnergy 0 = 0 := sorry

theorem sphereCurvatureEnergy_hasDerivAt :
    HasDerivAt sphereCurvatureEnergy (-(32 * Real.pi / 5)) 0 := sorry

theorem sphereCurvatureEnergy_neg :
    ∃ ε₀ : Real, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioo (0 : Real) ε₀, sphereCurvatureEnergy ε < 0 := sorry

theorem curvatureEnergyInequality_fails_unrestricted :
    ∃ g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ h : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nablaH : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nabla2H : (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) ->
      Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 3 x,
      NablaOneFormSectionRealizes (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH ∧
      (∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH x (nabla2H x)) ∧
      (∫ x, normSq0S (I := 𝓡 2) g x 1
            (roughLap0STensor (I := 𝓡 2) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
        < (∫ x, gaussCurvature (I := 𝓡 2) g x * normSq0S (I := 𝓡 2) g x 2 (nablaH x)
            ∂(riemannianVolumeMeasure (I := 𝓡 2)
              (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
          + (∫ x, inner0S (I := 𝓡 2) g x 2
                (oneFormReaction2D (I := 𝓡 2) g (h x)) (nablaH x)
              ∂(riemannianVolumeMeasure (I := 𝓡 2)
                (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g)) := sorry

end Sphere

end DifferentialGeometry.Integral.Connection
