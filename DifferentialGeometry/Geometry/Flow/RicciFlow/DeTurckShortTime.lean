import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Analysis.Spectral.Intrinsic.ConnectionLaplacianMaximalRegularity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialDataExistence

/-!
# Short-time existence for the Ricci–DeTurck flow

On a closed manifold, the DeTurck-modified Ricci right-hand side is strictly parabolic, so the
abstract quasilinear parabolic short-time existence theorem applies.  This file records the
resulting headline.

## Main results

* `deTurckRicci_shortTime_existence_of_closed` — for any initial metric `g₀` and background
  metric `g_bg` on a closed manifold there exist `T > 0` and a family `g_DT` solving the
  Ricci–DeTurck flow on `[0, T)` with `g_DT 0 = g₀`.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M]

/-- **Short-time existence for the Ricci–DeTurck flow on a closed manifold.**

On a closed (compact, boundaryless) manifold `M`, for any smooth Riemannian
metric `g₀` and any background metric `g_bg`, there exist a positive time
`T > 0` and a family `g_DT : ℝ → SmoothRiemannianMetric I M` that solves the
Ricci–DeTurck flow `∂_t g = deTurckRicciRHS g_bg g` on `[0, T)` with initial
value `g_DT 0 = g₀`, in the sense of `IsQuasilinearMetricParabolicSolution`.

The right-hand side `deTurckRicciRHS g_bg g = -2 · Ric(g) + 𝓛_{W(g, g_bg)} g`
is the DeTurck-modified Ricci operator, where `W(g, g_bg)` is the DeTurck
vector field; this modification makes the otherwise only weakly-parabolic
Ricci flow strictly parabolic.

This is the genuine quasi-linear parabolic short-time existence for the concrete
DeTurck–Ricci operator. Its inputs are that `deTurckRicciRHS g_bg` is strictly
parabolic at every metric (`deTurckRicciRHS_isStrictlyParabolic_at_self`), has
smooth quasi-linear dependence on `(g, ∇g, ∇²g)`
(`deTurckRicciRHS_isSmoothQuasilinear`), and is value-symmetric
(`deTurckRicciRHS_symm` — this keeps the conclusion, a curve of symmetric metrics,
satisfiable).

The proof is the trivial projection onto the existence conjunct: the single honest
analytic input `deturck_ricci_flow_parabolic_short_time_existence`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`) supplies a
time `T` and a flow `g_DT` whose FIRST conjunct is exactly this
`IsQuasilinearMetricParabolicSolution` datum (existence + the closed-interval
`Ico 0 T` one-sided derivative), bundled with the up-to-`t = 0` regularity the
Ricci-flow pullback needs; here we read off that existence conjunct. That input is
the deferred classical analytic result (strictly-parabolic smooth-quasilinear
existence + interior regularity from smooth data); it remains `sorry`, so consumers
transitively depend on `sorryAx`.

There is intentionally no abstract free-operator version: that statement is false
as written (the conclusion forces value-symmetry that a free operator binder does
not carry), so the existence content lives here, at the symmetric DeTurck operator. -/
theorem deTurckRicci_shortTime_existence_of_closed
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := by
  obtain ⟨T, g_DT, hbundle⟩ :=
    deturck_ricci_flow_parabolic_short_time_existence (I := I) g₀ g_bg
  exact ⟨T, g_DT, hbundle.1⟩

end DifferentialGeometry.PDE.RicciFlow
