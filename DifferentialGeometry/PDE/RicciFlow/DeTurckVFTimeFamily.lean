import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.VectorFieldSmooth
import DifferentialGeometry.PDE.DeTurck.ChristoffelContInMetric
import DifferentialGeometry.PDE.DeTurck.DeTurckVFChartCoord

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
**Spatial-smooth / time-continuous regularity of the DeTurck vector field
along a time-family of metrics.**

Given a background metric `g_bg`, a horizon `T : ℝ`, and a time-family of
metrics `g_DT : ℝ → SmoothRiemannianMetric I M` whose pointwise inner-product
pairings are time-continuous on `[0, T)` together with continuity-in-`t` of the
chart-coordinate first partial derivatives of those pairings, the DeTurck vector
field `deTurckVF (g_DT t) g_bg` is, at each fixed time `t`, a smooth tangent
section (by construction — this is the meaning of `Cₛ^∞⟮…⟯`), and at each fixed
point `x : M` the assignment `t ↦ (deTurckVF (g_DT t) g_bg) x` is continuous in
`t` on `[0, T)`.

The signature records the time-continuity at each spatial point — the spatial
smoothness is already encoded in the `Cₛ^∞` type of `deTurckVF` and is not
restated.

## Hypotheses

* `h_metric_cont` records `C^0` time-continuity of the inner-product pairings
  `(g_DT t).inner x v w`.  This is the conclusion of
  `maxreg_solution_in_c1_via_sobolev_embedding`
  (`PDE/RicciFlow/DeTurckSolutionC1.lean`) and is produced for free by that
  lemma when `g_DT` is the maxReg DeTurck-Ricci solution.

* `h_metric_partial_cont` records `C^1` time-continuity of the chart-coordinate
  representation of the inner-product pairings: each Fréchet partial derivative
  of the chart-pulled-back Gram entry function is time-continuous.  This is the
  genuine `C^1`-in-the-metric data that the DeTurck vector field needs in
  order to express continuity of its chart-coordinate components via the
  Cramer's-rule chart formula; it cannot be obtained from the bare `C^0`
  pairing hypothesis alone.  Like `h_metric_cont`, it is produced for free
  when `g_DT` is the maxReg DeTurck-Ricci solution (where Sobolev embedding
  gives `C^1` regularity in `(t, x)` for the metric coefficients).

## Proof

The bundled DeTurck vector field admits, in the chart at `α := x`, the
chart-coordinate expansion `(deTurckVF g g_bg) x = Σ_p chartDeTurckVFComp g g_bg
x p (extChartAt I x x) · (chartModelBasis E p)` (the bridge
`deTurckVF_apply_eq_chartDeTurckVFComp_sum_self`, which routes through the
chart-Christoffel-correction form of `connDiff`).  The chart-coordinate
component `chartDeTurckVFComp g g_bg x p y` is continuous in `g` in the
Cramer's-rule sense — `chartDeTurckVFComp_continuous_in_metric_at` — under the
two chart-coordinate hypotheses, which are exactly what `h_metric_cont` and
`h_metric_partial_cont` supply (with `α := x`, `y := extChartAt I x x`, and the
self-chart membership of `x` in its own base set).  The bundled section value
is therefore a continuous finite linear combination of model-basis vectors
(constant in `t`), with continuous-in-`t` coefficients. -/
theorem deturck_vf_time_family_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (h_metric_cont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T))
    (h_metric_partial_cont :
      ∀ (x : M) (l i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun t : ℝ =>
            partialDeriv (E := E) l
              (chartGramOnE (I := I) (g_DT t) x i j) (extChartAt I x x))
          (Set.Ico (0 : ℝ) T)) :
    ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T) := by
  intro x
  have hrewrite : (fun t : ℝ =>
        (deTurckVF (I := I) (g_DT t) g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      fun t : ℝ =>
        ∑ p : Fin (Module.finrank ℝ E),
          DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg x p
              (extChartAt I x x) •
            ((chartModelBasis E) p : TangentSpace I x) := by
    funext t
    exact deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) (g_DT t) g_bg x
  rw [hrewrite]
  refine continuousOn_finset_sum _ ?_
  intro p _
  refine ContinuousOn.smul ?_ continuousOn_const
  have h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ =>
          chartGramOnE (I := I) (g_DT t) x i j (extChartAt I x x))
        (Set.Ico (0 : ℝ) T) := by
    intro i j
    have hreduce :
        (fun t : ℝ =>
            chartGramOnE (I := I) (g_DT t) x i j (extChartAt I x x))
          = fun t : ℝ =>
              (g_DT t).inner x
                ((chartModelBasis E) i : TangentSpace I x)
                ((chartModelBasis E) j : TangentSpace I x) := by
      funext t
      rw [chartGramOnE_def]
      rw [extChartAt_to_inv (I := I) x]
      rw [chartGramMatrix_apply]
      rw [chartBasisVecFiber_self (I := I) x i,
          chartBasisVecFiber_self (I := I) x j]
    rw [hreduce]
    exact h_metric_cont x ((chartModelBasis E) i) ((chartModelBasis E) j)
  have h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ =>
          partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) x i j)
            (extChartAt I x x))
        (Set.Ico (0 : ℝ) T) := h_metric_partial_cont x
  have hx_base : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [extChartAt_to_inv (I := I) x]
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  exact chartDeTurckVFComp_continuous_in_metric_at (I := I) g_bg x
    (extChartAt I x x) (Set.Ico (0 : ℝ) T) g_DT h_entry h_partial hx_base p

end DifferentialGeometry.PDE.RicciFlow
