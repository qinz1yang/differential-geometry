import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_normGradSqFun_eq_integral_neg_laplacian_mul
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hsupport : HasCompactSupport u) :
    (∫ x, normGradSqFun (I := I) g u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (-laplacian (I := I) (LeviCivita (I := I) g) g u x) * u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g hu hu hsupport
  change (∫ x, normGradSqFun (I := I) g u x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    -∫ x, u x * ΔG (I := I) g ⟨u, hu⟩ x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) at hgreen
  calc
    _ = -∫ x, u x * ΔG (I := I) g ⟨u, hu⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hgreen
    _ = -∫ x, u x * laplacian (I := I) (LeviCivita (I := I) g) g u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        congrArg (fun z => u x * z) (laplacian_levi_eq g hu x).symm
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring

end DifferentialGeometry.Integral.DivergenceTheorem
