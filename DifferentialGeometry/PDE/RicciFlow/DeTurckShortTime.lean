import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.StrictParabolicAtSelf
import DifferentialGeometry.PDE.RicciFlow.SmoothQuasilinear
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MaxReg
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.PointwiseDeriv

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

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

The proof instantiates the abstract quasilinear parabolic short-time existence
theorem `quasilinear_parabolic_metric_short_time_existence` with the two witnesses
that `deTurckRicciRHS g_bg` is strictly parabolic at `g₀`
(`deTurckRicciRHS_isStrictlyParabolic_at_self`) and has smooth quasi-linear
dependence on `(g, ∇g, ∇²g)` (`deTurckRicciRHS_isSmoothQuasilinear`). -/
theorem deTurckRicci_shortTime_existence_of_closed
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT :=
  DifferentialGeometry.PDE.quasilinear_parabolic_metric_short_time_existence
    (deTurckRicciRHS (I := I) g_bg) g₀
    (deTurckRicciRHS_isStrictlyParabolic_at_self g₀ g_bg)
    (deTurckRicciRHS_isSmoothQuasilinear g_bg)

end DifferentialGeometry.PDE.RicciFlow
