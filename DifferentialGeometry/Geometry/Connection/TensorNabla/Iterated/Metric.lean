import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def metricCovariantDerivative (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (x : M) → Tensor0SSpace s I x) (x : M) : Tensor0SSpace (s + 1) I x := by
  letI := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  exact (trivializationAt (Tensor0SModel (s + 1) ℝ E)
    (fun x => Tensor0SSpace (s + 1) I x) x).symm x
    (totalCovDerivTensor0SModelAt (𝕜 := ℝ) (E := E) s
      (fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x T)
        (Set.range I) (extChartAt I x x))
      (connectionEndomorphismInChartL (𝕜 := ℝ) (I := I) (leviCivitaConnectionOfMetric g) x
        (extChartAt I x x))
      (tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x x (T x)))

def iteratedMetricCovariantDerivative (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : (x : M) → Tensor0SSpace s I x) :
    (k : ℕ) → (x : M) → Tensor0SSpace (s + k) I x
  | 0 => T
  | k + 1 => metricCovariantDerivative g (s + k) (iteratedMetricCovariantDerivative g s T k)

end DifferentialGeometry.Geometry.Connection
