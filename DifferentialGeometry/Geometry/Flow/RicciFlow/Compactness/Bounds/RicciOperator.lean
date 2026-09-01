import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Raising
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.FlowUniformEquivalence
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricci_quadratic_form_on_unit_vector_le_of_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    {t : Real} (x : M) (u : TangentSpace I x)
    (hu : (S.base.metric t).inner x u u = 1) :
    |S.ricciAt t x (vec2 (I := I) u u)|
      ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2
          * Real.sqrt (normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)) := by
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (S.base.metric t) x
  have hinv : MetricInverseInBasisGen (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) (S.base.metric t) basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hbridge : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      (S.ricci t) x (vec2 (I := I) (basis i) (basis j))
        = S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j; simp
  have htrace : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      S.ricciAt t x (vec2 (I := I) (basis i) (basis j))
        = ∑ a, S.base.rm04 t x
            (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    have h :=
      ricci_diag_eq_sum_rm04_diag_of_orthonormal (I := I) (S.base.metric t) basis
        (S.ricci t) (S.base.rm13 t) (S.base.rm04 t)
        (DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSol (I := I) S t)
        (DifferentialGeometry.PDE.RicciFlow.solution_rm04LowersRm13At (I := I) S t x) hON i j
    rw [hbridge i j] at h
    exact h
  exact ricci_unitQuad_le_of_trace (I := I) (S.base.metric t) basis hON hinv
    (S.ricciAt t x) (S.base.rm04 t x) htrace u hu

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem twoTensorQuadBound_of_solutions
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (K : Set M) (β ψ C : Real)
    (hcurv : forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
      normSq0S (I := I) ((S i).base.metric t) x 4 ((S i).base.rm04 t x) <= C) :
    DifferentialGeometry.HCGCompactness.TwoTensorQuadBoundOnWindow (I := I) K β ψ
      (fun i s => (S i).base.metric s) (fun i t x => (S i).ricciAt t x)
      ((Module.finrank Real E : Real) ^ 2 * Real.sqrt C) := by
  refine DifferentialGeometry.HCGCompactness.twoTensorQuadBound_of_unit_bound K β ψ
    ((Module.finrank Real E : Real) ^ 2 * Real.sqrt C)
    (fun i s => (S i).base.metric s) (fun i t x => (S i).ricciAt t x)
    (by positivity) ?_
  intro i t ht x hx u hu
  calc |(S i).ricciAt t x (vec2 (I := I) u u)|
      ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2
          * Real.sqrt (normSq0S (I := I) ((S i).base.metric t) x 4 ((S i).base.rm04 t x)) :=
        ricci_quadratic_form_on_unit_vector_le_of_solution (S i) x u hu
    _ ≤ (Module.finrank Real E : Real) ^ 2 * Real.sqrt C := by
        have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
        rw [hfr]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hcurv i t ht x hx)) (by positivity)

end DifferentialGeometry.Geometry.Curvature
