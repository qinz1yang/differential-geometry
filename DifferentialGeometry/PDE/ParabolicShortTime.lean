import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Existence
import DifferentialGeometry.PDE.DeTurck.Symbol
import DifferentialGeometry.PDE.RicciFlow.PrincipalSymbol
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Phase 7 — Parabolic existence: the engineering interface to Phase 8 (SKELETON)

This file is a *skeleton* for the Phase 7 deliverables. Statements are concrete
and self-contained, but the deeper sub-theorems are stubbed with `sorry` so
the chain can be assembled and downstream Phase 8 work can begin in parallel.

The endpoint is a quasi-linear short-time existence theorem for an
abstract second-order parabolic operator on smooth Riemannian metrics:
given any operator `F : SmoothRiemannianMetric I M → pointwiseBilin I` which
is strictly parabolic at the initial metric `g₀` and has the standard
smooth dependence on `(g, ∇g, ∇²g)`, there is a positive existence time
`T > 0` and a smooth-in-time family of Riemannian metrics
`g_fam : ℝ → SmoothRiemannianMetric I M` with `g_fam 0 = g₀` and
`∂_t g_fam(t) = F(g_fam(t))` for every `t ∈ [0, T)`.

Phase 8 (handled in a separate dispatch) consumes this endpoint by
instantiating `F` with the DeTurck-Ricci right-hand side
`g ↦ -2 Ric(g) + 𝓛_{X(g, g_bg)} g`, which is strictly parabolic by the
existing `deTurckSymbol_isStrictlyParabolic_of_symm`.

## Layout

* `IsParabolicMetricRHS` — abstract data describing a parabolic operator
  on metrics together with its strict-parabolicity witness at the initial
  metric, suitable for plugging into `quasilinear_parabolic_metric_short_time_existence`.
* `IsQuasilinearMetricParabolicSolution F g₀ T g_fam` — the equation
  `∂_t g_fam(t) = F(g_fam(t))` evaluated pointwise against tangent
  vectors, with the initial condition `g_fam 0 = g₀` and the existence
  time `T` recorded.
* `IsLinearTensorParabolicMildSolution` — the analogous predicate for the
  linear inhomogeneous tensor heat equation `∂_t u + L u = F(t)`,
  expressed via the Duhamel formula. Used internally as the linearisation
  of the quasi-linear case.

## Main theorems (skeleton, proofs are `sorry`)

* `linear_tensor_parabolic_shortTime_exists` — existence of a mild
  solution to the linear inhomogeneous tensor heat equation. The
  existing project lemma `tensor_linear_parabolic_existence`
  (`Analysis/Parabolic/TensorLinearParabolic.lean`) provides this under
  a chart-locality predicate; the predicate-free version is the target
  of Route Y. The skeleton states it predicate-free.
* `quasilinear_parabolic_metric_short_time_existence` — the Phase 7 endpoint:
  short-time existence for `∂_t g = F(g)`, by Banach fixed point on
  Duhamel iterates seeded by the linearised semigroup.
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

/-- A smooth family of Riemannian metrics `g_fam : ℝ → SmoothRiemannianMetric I M`
solves the quasi-linear parabolic PDE `∂_t g(t) = F(g(t))` on the time interval
`[0, T)` with initial value `g₀`, when the time derivative of the underlying
bilinear form `(g_fam s).inner x v w` at every base point `x` and tangent pair
`(v, w)` matches `F(g_fam(t)) x v w`.

The right-hand side `F` produces, for each metric `g`, a pointwise bilinear form
`F g : ∀ x, T_x M →L T_x M →L ℝ`. Phase 8 will instantiate `F` with the
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

For the skeleton this is an opaque `Prop` placeholder; downstream callers
(notably Phase 8) supply concrete content by combining the existing
`deTurckSymbol_isStrictlyParabolic_of_symm` (`PDE/DeTurck/StrictParabolicity.lean`) with
the linearisation infrastructure in `PDE/DeTurck/DeTurckLinearization/`. The
shape `Prop` is what `quasilinear_parabolic_metric_short_time_existence` consumes. -/
def IsStrictlyParabolicMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
    DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol F g σ

/-- A second-order parabolic operator `F` on metrics has *smooth quasi-linear
dependence on* the data `(g, ∇g, ∇²g)`. As an abstract Prop placeholder for the
skeleton; downstream the concrete content is "F factors through chart-coordinate
data as a smooth function of metric components and their first two derivatives,
strictly parabolic in the highest-order part".

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

/-- **Short-time existence for a strictly parabolic quasi-linear PDE on smooth
Riemannian metrics over a closed manifold.**

For any smooth Riemannian metric `g₀` on a closed (compact, boundaryless)
manifold `M` and any operator `F` on smooth Riemannian metrics that is
strictly parabolic at `g₀` (`IsStrictlyParabolicMetricRHS F g₀`) and has smooth
quasi-linear dependence on the chart data `(g, ∇g, ∇²g)`
(`IsSmoothQuasilinearMetricRHS F`), the PDE `∂_t g = F(g)` admits a positive
existence time `T > 0` and a time-solution `g_fam : ℝ → SmoothRiemannianMetric I M`
with `g_fam 0 = g₀`, in the sense of `IsQuasilinearMetricParabolicSolution`.

The DeTurck-Ricci right-hand side `F(g) := -2 Ric(g) + 𝓛_{X(g, g_bg)} g` is one
intended instantiation; its strict-parabolicity witness is
`deTurckSymbol_isStrictlyParabolic_of_symm`.

The proof is currently `sorry`. -/
theorem quasilinear_parabolic_metric_short_time_existence
    [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (_hParabolic : IsStrictlyParabolicMetricRHS (I := I) F g₀)
    (_hSmooth : IsSmoothQuasilinearMetricRHS (I := I) F) :
    ∃ T : ℝ, ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I) F g₀ T g_fam := by
  sorry

/-- A predicate stating that `u : ℝ → TensorL2 r s g` is the mild Duhamel solution
of the linear inhomogeneous tensor heat equation `∂_t u + L u = F(t)` with initial
value `u₀`, where `L` is the (operator generating the) semigroup `S`.

The Duhamel formula is `u(t) = S(t) u₀ + ∫₀ᵗ S(t - τ) (F τ) dτ`. Here we leave
the semigroup `S` and forcing `F` as abstract data so the predicate composes
with the existing `Analysis/Parabolic/QuasiLinear/Existence.lean` infrastructure. -/
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
    [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
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
