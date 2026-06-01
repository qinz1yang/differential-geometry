import DifferentialGeometry.Realized.CurvatureTensor
import DifferentialGeometry.Tensor.RSTensor.Tensor0SMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Rough Laplacian Preparation

This file provides the basis-level metric trace interface used by the scalar
and one-form Bochner layer.  It intentionally does not claim that the traced
object is already the intrinsic rough Laplacian tensor operation; that bridge is
recorded as an explicit realization predicate.
-/

namespace DifferentialGeometry
namespace Realized

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Insert two distinguished tangent vectors into the first two slots of a
covariant tensor input, leaving the remaining `s` slots to `tail`. -/
def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)

/-- Basis-level metric trace of the first two covariant slots of a `(0,s+2)`
tensor. This is the coordinate-side preparation interface for the rough
Laplacian. -/
def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)

/-- Basis-level rough Laplacian value of a covariant tensor, represented as the
metric trace of a supplied second covariant derivative tensor. -/
def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail

/-- One-form specialization of the basis-level rough Laplacian interface. -/
def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)

/-- Realization predicate saying that a supplied rough Laplacian tensor is the
basis-level metric trace of a supplied second covariant derivative tensor. -/
def RoughLap0SRealizesMetricTrace
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTrace (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  h tail

theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTrace (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  h (fun _ : Fin 1 => Y)

/-- A supplied `(0,s)` tensor realizes the metric trace of a supplied
`(0,s+2)` tensor if all basis coordinate trace formulas agree with it. -/
def metric_trace_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  ∀ {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real),
      MetricInverseInBasis (I := I) g x basis gInv ->
        ∀ tail : Fin s -> TangentSpace I x,
          traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail

/-- Intrinsic-facing rough Laplacian realization for covariant tensors. -/
def rough_lap_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  metric_trace_0s (I := I) g nabla2A roughA

/-- One-form specialization of the intrinsic-facing rough Laplacian interface. -/
def rough_lap_one_form
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x) : Prop :=
  rough_lap_0s (I := I) g (s := 1) nabla2α roughα

theorem metric_trace_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (htrace : metric_trace_0s (I := I) g T traceT)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail :=
  htrace basis gInv hinv tail

theorem rough_lap_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (hrough : rough_lap_0s (I := I) g nabla2A roughA)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  by
    simpa [roughLap0SAt] using hrough basis gInv hinv tail

theorem rough_lap_one_form_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : rough_lap_one_form (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  by
    simpa [rough_lap_one_form, rough_lap_0s, roughLap1FormAt, roughLap0SAt] using
      hrough basis gInv hinv (fun _ : Fin 1 => Y)

end

end Realized
end DifferentialGeometry
