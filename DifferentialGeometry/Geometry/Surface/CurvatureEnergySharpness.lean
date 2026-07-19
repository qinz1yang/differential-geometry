import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Geometry.Curvature.Sphere.RoundGaussCurvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open MeasureTheory
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Forms
open DifferentialGeometry.Integral.DivergenceTheorem
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

theorem sphereConformalDerivs_zero_nabla2A_roughLap
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        ((sphereConformalDerivs 0).nabla2A x)
      = -(sphereHeightOneForm x) := sorry

theorem sphereConformalDerivs_zero_nablaA_ahlfors
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    ahlforsOperator (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        ((sphereConformalDerivs 0).nablaA x)
      = 0 := sorry

set_option maxHeartbeats 400000 in
theorem sphereCurvatureEnergy_zero : sphereCurvatureEnergy 0 = 0 := by
  have hmetric : sphereConformalMetric 0
      = roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) := by
    apply DifferentialGeometry.Geometry.SmoothRiemannianMetric.ext'
    intro x v w
    rw [sphereConformalMetric, conformalMetric_inner]
    rw [show (2 : Real) * (legendreConformalFactor 0 x) = 0 by
          simp [legendreConformalFactor]]
    rw [Real.exp_zero, one_mul]
  have hK1 : ∀ x, gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x = 1 :=
    roundMetric_gaussCurvature_eq_one
  have hKfun : gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) = fun _ => (1 : Real) :=
    funext hK1
  have hK : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (gaussCurvature (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [hKfun]; exact contMDiff_const
  have hR2' : ∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric 0))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) x
      ((sphereConformalDerivs 0).nabla2A x) :=
    fun x => nabla2OneFormRealizesAt_of_totalNabla
      (metricCov (I := 𝓡 2) (sphereConformalMetric 0))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
      ((sphereConformalDerivs 0).nabla2A)
      (sphereConformalDerivs 0).first (sphereConformalDerivs 0).second x
  have hR2 : ∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
      (metricCov (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) x
      ((sphereConformalDerivs 0).nabla2A x) := by
    rw [← hmetric]; exact hR2'
  have hR1 : NablaOneFormSectionRealizes (I := 𝓡 2)
      (metricCov (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) :=
    fun x => (hR2 x).1 x
  have hLap0 : ∀ x, formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK x = 0 := by
    have hgrad_zero : grad_g (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK = 0 := by
      apply ContMDiffSection.ext
      intro y
      change gradFun (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          (gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) y
          = (0 : TangentSpace (𝓡 2) y)
      apply gradFun_eq_zero_of_mfderiv_eq_zero
      rw [hKfun]
      exact mfderiv_const
    intro x
    rw [formLaplacianScalar_def, hgrad_zero, codifferentialOfVectorField_zero]
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  have hid := curvatureEnergyIdentity_twoDim hdim
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
    sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
    (fun x => (sphereConformalDerivs 0).nabla2A x) hK hR1 hR2
  have hz1 : ∀ x, normSq0S (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1
      (roughLap0STensor (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
          ((sphereConformalDerivs 0).nabla2A x)
        + gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
            • (sphereHeightOneForm x)) = 0 := by
    intro x
    have harg : roughLap0STensor (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
          ((sphereConformalDerivs 0).nabla2A x)
        + gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
            • (sphereHeightOneForm x) = 0 := by
      rw [sphereConformalDerivs_zero_nabla2A_roughLap x, hK1 x, one_smul]
      abel
    rw [harg]
    exact (normSq0S_eq_zero_iff (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1 0).mpr rfl
  have hz2 : ∀ x, gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x *
      normSq0S (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2
        (ahlforsOperator (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          ((sphereConformalDerivs 0).nablaA x)) = 0 := by
    intro x
    rw [sphereConformalDerivs_zero_nablaA_ahlfors x,
      (normSq0S_eq_zero_iff (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2 0).mpr rfl]
    ring
  have hz3 : ∀ x, formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK x *
      normSq0S (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1
        (sphereHeightOneForm x) = 0 := by
    intro x
    rw [hLap0 x]
    ring
  have hstep : sphereCurvatureEnergy 0
      = curvatureEnergy (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
          (fun x => (sphereConformalDerivs 0).nabla2A x) :=
    congrArg
      (fun g => curvatureEnergy g sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
        (fun x => (sphereConformalDerivs 0).nabla2A x)) hmetric
  rw [hstep]
  unfold curvatureEnergy
  rw [hid]
  simp only [hz1, hz2, hz3, MeasureTheory.integral_zero, mul_zero, add_zero]

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
