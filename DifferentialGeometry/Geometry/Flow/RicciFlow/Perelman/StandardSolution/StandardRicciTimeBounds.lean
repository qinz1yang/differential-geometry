import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.OrdinaryRicciTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteCurvatureBounds

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem uniformStandardLifetime_ordinary_ricci_time_bound_positive
    (τ : ℝ) (hτ : 0 ≤ τ) (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : StandardSolution, ∀ t ∈ Ioc 0 τ, ∀ x : E3,
      DifferentiableWithinAt ℝ (fun r => metricRicciAt (S.val.metric r) x)
        S.val.domain t ∧
      Real.sqrt (normSq0S (S.val.metric t) x 2
        (derivWithin (fun r => metricRicciAt (S.val.metric r) x) S.val.domain t)) ≤ B := by
  obtain ⟨C, hC, hnorm⟩ :=
    uniformStandardLifetime_curvature_derivative_bounds_closed τ hτ hlt 2
  refine ⟨ricciOrdinaryTimeBound 3 C, ricciOrdinaryTimeBound_nonneg 3 C hC, ?_⟩
  intro S t ht x
  have hlife : ENNReal.ofReal τ < S.val.lifetime :=
    hlt.trans_le (uniformStandardLifetime_le_lifetime S)
  have hreg : t ∈ (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt hlife⟩
  refine ⟨metricRicciAt_differentiableWithinAt S.val.toSolutionOn S.val.isSolutionOn
    ⟨t, hreg⟩ x, ?_⟩
  have hb := ricci_ordinary_time_derivative_bound S.val.toSolutionOn S.val.isSolutionOn
    ⟨t, hreg⟩ x C hC (fun k hk => hnorm S k hk t ⟨ht.1.le, ht.2⟩ x)
  exact hb.trans_eq (congrArg (fun d => ricciOrdinaryTimeBound d C)
    (by simp : Module.finrank ℝ E3 = 3))

end DifferentialGeometry.PDE.RicciFlow

end
