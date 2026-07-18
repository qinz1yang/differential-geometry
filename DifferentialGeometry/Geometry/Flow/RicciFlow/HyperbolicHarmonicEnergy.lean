import DifferentialGeometry.Geometry.Flow.RicciFlow.EinsteinScaling
import DifferentialGeometry.Geometry.Curvature.Riemann.ConstantCurvature
import DifferentialGeometry.Geometry.Hodge.OneFormHarmonic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic
open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem hyperbolic_isSolutionOn
    (g₀ : SmoothRiemannianMetric I M)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator (I := I) g₀ p v w ≠ 0 →
        DifferentialGeometry.Geometry.Riemannian.sectionalCurvature (I := I) g₀ p v w = -1) :
    IsSolutionOn (I := I)
      (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))) := by
  have hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)) := by
    have h := DifferentialGeometry.Geometry.Riemannian.einstein_of_constant_sectionalCurvature
      (I := I) g₀ (-1) hsec
    simpa only [neg_one_mul] using h
  exact hyperbolicScaled_isSolutionOn g₀ hEin

theorem hyperbolic_harmonic_isHeatOneFormOn
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator (I := I) g₀ p v w ≠ 0 →
        DifferentialGeometry.Geometry.Riemannian.sectionalCurvature (I := I) g₀ p v w = -1)
    (hHarm : DifferentialGeometry.Integral.Connection.IsHarmonicOneForm (I := I) g₀ alpha nablaOmega)
    (hRealizes2 : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x)) :
    IsHeatOneFormOn (I := I)
      (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family
      (einsteinScaledProbe (-((Module.finrank Real E : Real) - 1)) alpha)
      (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega)
      (einsteinScaledProbeNabla2 (-((Module.finrank Real E : Real) - 1)) nabla2Omega) := by
  have hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)) := by
    have h := DifferentialGeometry.Geometry.Riemannian.einstein_of_constant_sectionalCurvature
      (I := I) g₀ (-1) hsec
    simpa only [neg_one_mul] using h
  have hEigen := DifferentialGeometry.Integral.Connection.isHarmonicOneForm_einstein_roughLap_eigen
    (I := I) g₀ alpha nablaOmega nabla2Omega (-((Module.finrank Real E : Real) - 1)) hEin hHarm hRealizes2
  exact hyperbolicScaled_isHeatOneFormOn g₀ alpha nablaOmega nabla2Omega hEin hRealizes2 hEigen

theorem hyperbolic_harmonic_gradEnergy_hasDerivAt [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hn : 7 ≤ Module.finrank Real E)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator (I := I) g₀ p v w ≠ 0 →
        DifferentialGeometry.Geometry.Riemannian.sectionalCurvature (I := I) g₀ p v w = -1)
    (hHarm : DifferentialGeometry.Integral.Connection.IsHarmonicOneForm (I := I) g₀ alpha nablaOmega)
    (hRealizes2 : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I)
            ((einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family.metric s) x 2
            (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
              (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family s))
      (((Module.finrank Real E : Real) - 1) ^ 2 * ((Module.finrank Real E : Real) - 6) *
        ∫ x, normSq0S (I := I) g₀ x 1 (alpha x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      0 := by
  have hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)) := by
    have h := DifferentialGeometry.Geometry.Riemannian.einstein_of_constant_sectionalCurvature
      (I := I) g₀ (-1) hsec
    simpa only [neg_one_mul] using h
  have hEigen := DifferentialGeometry.Integral.Connection.isHarmonicOneForm_einstein_roughLap_eigen
    (I := I) g₀ alpha nablaOmega nabla2Omega (-((Module.finrank Real E : Real) - 1)) hEin hHarm hRealizes2
  exact hyperbolicScaled_gradEnergy_hasDerivAt g₀ alpha nablaOmega nabla2Omega hn hEin hRealizes2 hEigen

theorem hyperbolic_harmonic_gradEnergy_hasDerivAt_dimSix [CompactSpace M]
    (g₀ : SmoothRiemannianMetric I M)
    (alpha : DifferentialGeometry.Integral.Connection.OneFormSection (I := I) (M := M))
    (nablaOmega : DifferentialGeometry.Integral.Connection.TwoTensorSection (I := I) (M := M))
    (nabla2Omega : (x : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hdim : Module.finrank Real E = 6)
    (hsec : ∀ (p : M) (v w : TangentSpace I p),
      DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator (I := I) g₀ p v w ≠ 0 →
        DifferentialGeometry.Geometry.Riemannian.sectionalCurvature (I := I) g₀ p v w = -1)
    (hHarm : DifferentialGeometry.Integral.Connection.IsHarmonicOneForm (I := I) g₀ alpha nablaOmega)
    (hRealizes2 : ∀ x : M,
      DifferentialGeometry.Integral.Connection.Nabla2OneFormRealizesAt (I := I)
        (metricCov (I := I) (M := M) g₀) alpha nablaOmega x (nabla2Omega x)) :
    HasDerivAt
      (fun s : Real =>
        ∫ x, normSq0S (I := I)
            ((einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family.metric s) x 2
            (einsteinScaledProbeNabla (-((Module.finrank Real E : Real) - 1)) nablaOmega s x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M)
              (einsteinScaledSolution g₀ (-((Module.finrank Real E : Real) - 1))).family s))
      0 0 := by
  have hEin : DifferentialGeometry.Integral.Connection.IsEinsteinMetric (I := I) g₀
      (-((Module.finrank Real E : Real) - 1)) := by
    have h := DifferentialGeometry.Geometry.Riemannian.einstein_of_constant_sectionalCurvature
      (I := I) g₀ (-1) hsec
    simpa only [neg_one_mul] using h
  have hEigen := DifferentialGeometry.Integral.Connection.isHarmonicOneForm_einstein_roughLap_eigen
    (I := I) g₀ alpha nablaOmega nabla2Omega (-((Module.finrank Real E : Real) - 1)) hEin hHarm hRealizes2
  exact hyperbolicScaled_gradEnergy_hasDerivAt_dimSix g₀ alpha nablaOmega nabla2Omega hdim hEin hRealizes2 hEigen

end DifferentialGeometry.PDE.RicciFlow
