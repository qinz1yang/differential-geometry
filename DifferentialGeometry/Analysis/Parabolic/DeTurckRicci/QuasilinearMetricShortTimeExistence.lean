import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.MildSolutionExistence
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Predicates for the quasi-linear parabolic metric flow, and the linear tensor heat equation

This file provides the abstract *data* of the quasi-linear parabolic flow
`∂_t g = F(g)` on smooth Riemannian metrics, together with the existence theorem
for its **linear** building block (the Duhamel mild solution).

The **non-linear** short-time existence statement is recorded concretely, for the
strictly-parabolic symmetric DeTurck–Ricci right-hand side `deTurckRicciRHS g_bg`,
as `deTurckRicci_shortTime_existence_of_closed`
(`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`); that is the genuine leaf the
Ricci-flow short-time-existence headline consumes.

There is deliberately **no** abstract operator-level `∂_t g = F(g)` existence
theorem here. Such a statement is *false as stated* for a free operator `F`:
the conclusion is a curve of genuine — hence symmetric — Riemannian metrics, so by
derivative uniqueness it forces `F g₀` to be value-symmetric, while a free `F`
binder carries no symmetry hypothesis (adding any `g`-independent antisymmetric
field to a valid right-hand side satisfies every hypothesis yet breaks the
conclusion). The honest content is the concrete symmetric DeTurck–Ricci operator,
whose value-symmetry is `deTurckRicciRHS_symm`.

## Layout

* `IsQuasilinearMetricParabolicSolution F g₀ T g_fam` — the equation
  `∂_t g_fam(t) = F(g_fam(t))` evaluated pointwise against tangent vectors, with
  the initial condition `g_fam 0 = g₀` and the existence time `T` recorded.
* `IsStrictlyParabolicMetricRHS` — abstract strict-parabolicity data for an
  operator `F` at a metric `g` (the existence of a principal symbol).
* `IsSmoothQuasilinearMetricRHS` — smooth quasi-linear dependence on the chart
  data `(g, ∇g, ∇²g)` plus strict parabolicity at every metric.
* `IsLinearTensorParabolicMildSolution` — the predicate for the linear
  inhomogeneous tensor heat equation `∂_t u + L u = F(t)`, via the Duhamel
  formula; the linearisation of the quasi-linear case.

## Main theorems

* `linear_tensor_parabolic_shortTime_exists` — existence of a mild solution to the
  linear inhomogeneous tensor heat equation, stated predicate-free and built
  directly from the Duhamel map of the abstract bounded `C₀`-semigroup.
-/

namespace DifferentialGeometry
namespace PDE

universe u v

open scoped Manifold ContDiff Topology
open Bundle MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- A smooth family of Riemannian metrics `g_fam : ℝ → SmoothRiemannianMetric I M`
solves the quasi-linear parabolic PDE `∂_t g(t) = F(g(t))` on the time interval
`[0, T)` with initial value `g₀`, when the time derivative of the underlying
bilinear form `(g_fam s).inner x v w` at every base point `x` and tangent pair
`(v, w)` matches `F(g_fam(t)) x v w`.

The right-hand side `F` produces, for each metric `g`, a pointwise bilinear form
`F g : ∀ x, T_x M →L T_x M →L ℝ`. The DeTurck-Ricci instantiation takes `F` to be the
DeTurck-Ricci right-hand side
`F(g) x v w = -2 ricciTensor g x v w + lieDerivMetric g (deTurckVF g g_bg) x v w`. -/
def IsQuasilinearMetricParabolicSolution
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M) (T : ℝ)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  0 < T ∧ g_fam 0 = g₀ ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
                  (F (g_fam t) x v w) (Set.Ici 0) t

/-- An abstract strict-parabolicity hypothesis on an operator `F` at a metric `g`.

Downstream callers supply concrete content by combining the existing
`deTurckSymbol_isStrictlyParabolic_of_symm`
(`Analysis/Parabolic/StrictParabolicity.lean`) with the linearisation
infrastructure in `Analysis/Parabolic/DeTurckLinearization/`. The concrete
instance is `deTurckRicciRHS_isStrictlyParabolic_at_self`, consumed by the
DeTurck–Ricci short-time existence leaf `deTurckRicci_shortTime_existence_of_closed`. -/
def IsStrictlyParabolicMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
    DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol F g σ

/-- A second-order parabolic operator `F` on metrics has *smooth quasi-linear
dependence on* the data `(g, ∇g, ∇²g)`: `F` factors through chart-coordinate
data as a smooth function of metric components and their first two derivatives,
and is strictly parabolic in the highest-order part.

The chart-smoothness conjunct is stated against the **chart-`α`-pushforward
frame vectors** `(trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)`,
which form a genuine smooth local frame for `TangentSpace I` over the chart-`α`
source. (Stating chart-smoothness against the bare model-basis constants
`chartModelBasis E i : E`, treated as `TangentSpace I x` via the canonical
type-synonym defeq, would silently force smoothness of a constant tangent
section — which is not available on a non-parallelizable manifold such as the
two-sphere; the chart-frame formulation is the project's standard pattern,
matching `Trivialization.coordChangeL` smoothness via
`contMDiffOn_coordChangeL`.) -/
def IsSmoothQuasilinearMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) : Prop :=
  (∀ (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x => F g x
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Integral.Measure.chartModelBasis E i))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Integral.Measure.chartModelBasis E j)))
        (chartAt H α).source)
    ∧ ∀ g : SmoothRiemannianMetric I M, IsStrictlyParabolicMetricRHS F g

/-- A predicate stating that `u : ℝ → TensorL2 r s g` is the mild Duhamel solution
of the linear inhomogeneous tensor heat equation `∂_t u + L u = F(t)` with initial
value `u₀`, where `L` is the (operator generating the) semigroup `S`.

The Duhamel formula is `u(t) = S(t) u₀ + ∫₀ᵗ S(t - τ) (F τ) dτ`. Here we leave
the semigroup `S` and forcing `F` as abstract data so the predicate composes
with the existing `Analysis/Parabolic/QuasiLinear/Semigroup/` Duhamel
infrastructure. -/
def IsLinearTensorParabolicMildSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (T : ℝ) (u : ℝ → X) : Prop :=
  0 < T ∧ u 0 = u₀ ∧
    ContinuousOn u (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (F τ)

/-- **Linear inhomogeneous tensor heat equation: mild solution exists.**

A predicate-free mild-solution existence statement for the abstract linear
inhomogeneous evolution equation `∂_t u + L u = F(t)` with initial datum
`u₀`, where `L` is the (generator of the) bounded `C₀`-semigroup `S` on a
Banach space `X`. The solution is given by the Duhamel formula
`u(t) = S t u₀ + ∫₀ᵗ S (t - τ) (F τ) dτ`.

The construction is direct: we take `u := duhamel S u₀ F`. The initial
condition `u 0 = u₀` is `duhamel_zero`; continuity on `[0, T]` follows
from `duhamel_continuousOn` on `[0, ∞)` by restriction. Any positive
existence time works for this purely linear case; we pick `T := 1`. -/
theorem linear_tensor_parabolic_shortTime_exists
    [CompactSpace M]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ → X,
      IsLinearTensorParabolicMildSolution S u₀ F T u := by
  refine ⟨1, Analysis.Parabolic.QuasiLinear.duhamel S u₀ F, ?_, ?_, ?_, ?_⟩
  · exact zero_lt_one
  · exact Analysis.Parabolic.QuasiLinear.duhamel_zero S u₀ F
  · have h_cont :
        ContinuousOn (Analysis.Parabolic.QuasiLinear.duhamel S u₀ F)
          (Set.Ici (0 : ℝ)) :=
      Analysis.Parabolic.QuasiLinear.duhamel_continuousOn S u₀ hF
    exact h_cont.mono (Set.Icc_subset_Ici_self)
  · intro t _
    rfl

end PDE
end DifferentialGeometry
