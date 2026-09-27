import DifferentialGeometry.Tensor.LinearAlgebra.RankOneBilinear
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

open scoped BigOperators

namespace ContinuousLinearMap

theorem sum_mul_apply_diagonal_eq_sum_coordinates
    {𝕜 E ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (H : E →L[𝕜] E →L[𝕜] 𝕜) (e : Module.Basis ι 𝕜 E)
    (s : Finset κ) (a : κ → 𝕜) (v : κ → E) (C : ι → ι → 𝕜)
    (hC : ∀ i j, C i j = ∑ k ∈ s, a k * e.repr (v k) i * e.repr (v k) j) :
    (∑ k ∈ s, a k * H (v k) (v k)) = ∑ i, ∑ j, C i j * H (e i) (e j) := by
  simpa only [smul_eq_mul, toLinearMap₁₂_apply_apply_apply] using
    H.toLinearMap₁₂.sum_smul_apply_eq_sum_coordinates e e s a v v C hC

end ContinuousLinearMap

namespace DifferentialGeometry.Analysis.Calculus

theorem sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates
    {𝕜 E ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (u : E → 𝕜) (x : E) (e : Module.Basis ι 𝕜 E)
    (s : Finset κ) (a : κ → 𝕜) (v : κ → E) (C : ι → ι → 𝕜)
    (hC : ∀ i j, C i j = ∑ k ∈ s, a k * e.repr (v k) i * e.repr (v k) j) :
    (∑ k ∈ s, a k * iteratedFDeriv 𝕜 2 u x ![v k, v k]) =
      ∑ i, ∑ j, C i j * iteratedFDeriv 𝕜 2 u x ![e i, e j] := by
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates
      (fderiv 𝕜 (fderiv 𝕜 u) x) e s a v C hC

end DifferentialGeometry.Analysis.Calculus
