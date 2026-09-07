import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

open Set

namespace DifferentialGeometry.Analysis

theorem trace_fderivWithin_eq_sum
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) {u : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffWithinAt K s x) (hu : DifferentiableWithinAt K u s x) :
    LinearMap.trace K E (fderivWithin K u s x).toLinearMap =
      ∑ i, fderivWithin K (fun y => b.repr (u y) i) s x (b i) := by
  classical
  let _ : FiniteDimensional K E := Module.Finite.of_basis b
  rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  let L : E →L[K] K := (b.coord i).toContinuousLinearMap
  have hderiv := (L.hasFDerivAt.comp_hasFDerivWithinAt x hu.hasFDerivWithinAt).fderivWithin hs
  simp only [Matrix.diag, LinearMap.toMatrix_apply]
  rw [show (fun y => b.repr (u y) i) = L ∘ u by rfl, hderiv]
  rfl

theorem trace_fderiv_eq_sum
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) {u : E → E} {x : E}
    (hu : DifferentiableAt K u x) :
    LinearMap.trace K E (fderiv K u x).toLinearMap =
      ∑ i, fderiv K (fun y => b.repr (u y) i) x (b i) := by
  simpa only [fderivWithin_univ] using
    trace_fderivWithin_eq_sum b uniqueDiffWithinAt_univ hu.differentiableWithinAt

end DifferentialGeometry.Analysis
