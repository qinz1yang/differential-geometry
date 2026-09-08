import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

open Set

namespace DifferentialGeometry.Analysis

theorem hasDerivWithinAt_linearMap_trace
    {K W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W]
    {A : K → (W →L[K] W)} {A' : W →L[K] W} {s : Set K} {t : K}
    (hA : HasDerivWithinAt A A' s t) :
    HasDerivWithinAt (fun r => LinearMap.trace K W (A r).toLinearMap)
      (LinearMap.trace K W A'.toLinearMap) s t := by
  let tr : (W →L[K] W) →L[K] K :=
    LinearMap.toContinuousLinearMap ((LinearMap.trace K W).comp
      (LinearMap.toContinuousLinearMap : (W →ₗ[K] W) ≃ₗ[K] (W →L[K] W)).symm.toLinearMap)
  exact tr.hasFDerivAt.comp_hasDerivWithinAt t hA

theorem hasDerivAt_linearMap_trace
    {K W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W]
    {A : K → (W →L[K] W)} {A' : W →L[K] W} {t : K}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun r => LinearMap.trace K W (A r).toLinearMap)
      (LinearMap.trace K W A'.toLinearMap) t := by
  exact (hasDerivWithinAt_linearMap_trace (s := univ) hA.hasDerivWithinAt).hasDerivAt
    Filter.univ_mem

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

theorem trace_fderivWithin_conj
    {K V W : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup V] [NormedSpace K V]
    [NormedAddCommGroup W] [NormedSpace K W]
    (e : V ≃L[K] W) {u : V → V} {s : Set V} {x : W}
    (hs : UniqueDiffWithinAt K (e.symm ⁻¹' s) x) :
    LinearMap.trace K W (fderivWithin K (e ∘ u ∘ e.symm) (e.symm ⁻¹' s) x).toLinearMap =
      LinearMap.trace K V (fderivWithin K u s (e.symm x)).toLinearMap := by
  rw [e.comp_fderivWithin hs, e.symm.comp_right_fderivWithin hs]
  exact LinearMap.trace_conj' (fderivWithin K u s (e.symm x)).toLinearMap e.toLinearEquiv

theorem trace_fderiv_conj
    {K V W : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup V] [NormedSpace K V]
    [NormedAddCommGroup W] [NormedSpace K W]
    (e : V ≃L[K] W) (u : V → V) (x : W) :
    LinearMap.trace K W (fderiv K (e ∘ u ∘ e.symm) x).toLinearMap =
      LinearMap.trace K V (fderiv K u (e.symm x)).toLinearMap := by
  simpa only [preimage_univ, fderivWithin_univ] using
    trace_fderivWithin_conj (s := univ) (u := u) e uniqueDiffWithinAt_univ

end DifferentialGeometry.Analysis
