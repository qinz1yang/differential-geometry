import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartGramChristoffel
import Mathlib.Analysis.ODE.Gronwall

set_option linter.unusedSectionVars false

/-!
# Sections along a curve, covariant derivative `D/dt`, and parallel transport

Given a smooth Riemannian metric `g` on a smooth manifold `M` and a curve
`γ : ℝ → M`, a **section along `γ` on `s ⊆ ℝ`** is a map
`t ↦ X(t) ∈ T_{γ(t)} M`. Because the project's `TangentSpace I (γ t)` is
definitionally `E`, such a section is type-theoretically the same as a
function `ℝ → E`; the geometric content lives in how chart transitions
act on it.

This file packages the chart-local theory of sections along curves:

1. **G.5.1 — `SectionAlongCurve`**: the bundled data of a section, kept
   simple as a wrapper around `ℝ → E`. The geometric content is in the
   companion smoothness and tangentiality predicates below.

2. **G.5.2 — Smoothness API**: smoothness of a section along `γ` is the
   chart-local notion. The section `X` is smooth at `t₀` in the chart at
   `α : M` (whose source contains `γ(t₀)`) iff `X : ℝ → E` is `C^n` at
   `t₀` *as a function with values in the model fibre at `α`*. Because
   `TangentSpace I (γ t) = E` definitionally for every `t`, no
   trivialization-rewrite is needed for the `E`-valued representation
   itself; the chart-α dependence enters only through the Christoffel
   symbols that appear in `D/dt`.

3. **G.5.3 — `chartCovDerivAlong`**: the chart-local covariant derivative
   `D X / dt` written in a fixed chart at `α : M`,
   $$\bigl(\tfrac{D X}{dt}\bigr)(t) := X'(t) +
       \Gamma_\alpha\bigl(u'(t), X(t)\bigr)(u(t)),$$
   where `u(t) := φ_α(γ(t))`. The predicate
   `IsCovDerivAlongChart g α γ Y W s` records that `W` is the covariant
   derivative of `Y` along `γ` on `s ⊆ ℝ` in the chart at `α`. The
   companion lemmas establish linearity in the section argument and the
   scalar-Leibniz rule.

4. **G.5.4 — `IsParallelTransportChart`**: a section `Y` is *parallel
   along `γ` in chart `α`* if its chart-local representation satisfies
   the parallel-transport ODE
   $$Y'(t) + \Gamma_\alpha\bigl(u'(t), Y(t)\bigr)(u(t)) = 0.$$
   We prove the **uniqueness** of parallel transport with prescribed
   initial value using Mathlib's Gronwall machinery
   (`ODE_solution_unique_of_mem_Ioo`). Existence of parallel transport
   along a curve segment staying inside a single chart is recorded as
   the chart-local Picard–Lindelöf statement; the global extension and
   the chart-independence of the parallel-transport ODE require a
   separate chart-gluing development and are not addressed here.

## Strategic notes

We follow the **chart-fixed** strategy: every definition takes an
explicit basepoint `α : M`, and statements about `X(t) ∈ T_{γ(t)} M` are
interpreted in the chart at `α`, valid whenever `γ(t) ∈ (chartAt α).source`.
This avoids the chart-transition complications that arise when `γ`
crosses multiple chart domains and is the natural foundation on which a
Picard–Lindelöf construction (followed by chart-gluing) would be built.

The intrinsic, chart-independent versions of `D/dt` and parallel
transport are downstream developments built on top of this chart-local
infrastructure.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- A section along a curve `γ : ℝ → M`. The underlying data is the
function `toFun : ℝ → E`; semantically, `X.toFun t` is interpreted as
a vector in `T_{γ(t)} M = E`. -/
@[ext] structure SectionAlongCurve (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (_γ : ℝ → M) where

  toFun : ℝ → E

namespace SectionAlongCurve

variable {γ : ℝ → M}

/-- `X : ℝ → E` is interpreted as a vector in `T_{γ(t)} M = E` at each
parameter value `t`. -/
@[simp] lemma toFun_def (X : SectionAlongCurve I M γ) (t : ℝ) :
    X.toFun t = X.toFun t := rfl

/-- The zero section: identically zero. -/
def zero : SectionAlongCurve I M γ := ⟨fun _ => 0⟩

@[simp] lemma zero_toFun (t : ℝ) : (zero : SectionAlongCurve I M γ).toFun t = 0 := rfl

/-- Pointwise addition of two sections along the same curve. -/
def add (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t + Y.toFun t⟩

@[simp] lemma add_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (add X Y).toFun t = X.toFun t + Y.toFun t := rfl

/-- Pointwise negation of a section. -/
def neg (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => - X.toFun t⟩

@[simp] lemma neg_toFun (X : SectionAlongCurve I M γ) (t : ℝ) :
    (neg X).toFun t = - X.toFun t := rfl

/-- Pointwise subtraction of two sections. -/
def sub (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t - Y.toFun t⟩

@[simp] lemma sub_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (sub X Y).toFun t = X.toFun t - Y.toFun t := rfl

/-- Pointwise scalar multiplication of a section by a real number. -/
def smul (a : ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => a • X.toFun t⟩

@[simp] lemma smul_toFun (a : ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smul a X).toFun t = a • X.toFun t := rfl

/-- Pointwise scalar multiplication of a section by a real-valued
function of the parameter `t`. This is the operation by which `D/dt`
acts as a derivation. -/
def smulFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => f t • X.toFun t⟩

@[simp] lemma smulFun_toFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smulFun f X).toFun t = f t • X.toFun t := rfl

/-- The underlying function of a section, exposed as `(↑·)`. -/
instance : CoeFun (SectionAlongCurve I M γ) (fun _ => ℝ → E) := ⟨toFun⟩

@[simp] lemma coe_zero : ((zero : SectionAlongCurve I M γ) : ℝ → E) = fun _ => 0 := rfl

@[simp] lemma coe_add (X Y : SectionAlongCurve I M γ) :
    ((add X Y : SectionAlongCurve I M γ) : ℝ → E) = fun t => X.toFun t + Y.toFun t := rfl

@[simp] lemma coe_smul (a : ℝ) (X : SectionAlongCurve I M γ) :
    ((smul a X : SectionAlongCurve I M γ) : ℝ → E) = fun t => a • X.toFun t := rfl

/-- Smoothness predicate for a section along a curve, *in the chart at
`α`*: `X.toFun` is `C^n` (in the sense of `ContDiffOn ℝ n`) on `s`. The
geometric interpretation (e.g. transformation under chart changes)
requires that `γ(s)` lies in the chart's source; we keep this as a
separate hypothesis in downstream theorems rather than baking it in. -/
def ContMDiffOnInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ n X.toFun s

/-- Smoothness predicate for a section along a curve at a single point.
This is the localised version of `ContMDiffOnInChart`. -/
def ContMDiffAtInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  ContDiffAt ℝ n X.toFun t

/-- Differentiability predicate for a section along a curve, as a special
case of `ContMDiffOnInChart` with `n = 1`. -/
def DifferentiableOnAlong (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  DifferentiableOn ℝ X.toFun s

/-- Differentiability at a point. -/
def DifferentiableAtAlong (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  DifferentiableAt ℝ X.toFun t

@[simp] lemma contMDiffOnInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) n X s = ContDiffOn ℝ n X.toFun s := rfl

@[simp] lemma contMDiffAtInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) n X t = ContDiffAt ℝ n X.toFun t := rfl

/-- The zero section is smooth. -/
lemma zero_contMDiffOnInChart (n : WithTop ℕ∞) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) (γ := γ) n zero s := by
  unfold ContMDiffOnInChart
  exact contDiffOn_const

/-- The zero section is smooth at every point. -/
lemma zero_contMDiffAtInChart (n : WithTop ℕ∞) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) (γ := γ) n zero t := by
  unfold ContMDiffAtInChart
  exact contDiffAt_const

/-- The sum of two smooth sections is smooth. -/
lemma add_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (add X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.add hY

/-- Smoothness of the sum at a point. -/
lemma add_contMDiffAtInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {t : ℝ}
    (hX : ContMDiffAtInChart (I := I) (M := M) n X t)
    (hY : ContMDiffAtInChart (I := I) (M := M) n Y t) :
    ContMDiffAtInChart (I := I) (M := M) n (add X Y) t := by
  unfold ContMDiffAtInChart at *
  exact hX.add hY

/-- The negation of a smooth section is smooth. -/
lemma neg_contMDiffOnInChart {n : WithTop ℕ∞} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (neg X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.neg

/-- Smoothness of the difference. -/
lemma sub_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (sub X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.sub hY

/-- A real-scalar multiple of a smooth section is smooth. -/
lemma smul_contMDiffOnInChart {n : WithTop ℕ∞} {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smul a X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.const_smul a

/-- A scalar-function multiple of a smooth section is smooth, provided
the scalar function is itself smooth on `s`. -/
lemma smulFun_contMDiffOnInChart {n : WithTop ℕ∞} {f : ℝ → ℝ}
    {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : ContDiffOn ℝ n f s)
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smulFun f X) s := by
  unfold ContMDiffOnInChart at *
  exact hf.smul hX

/-- Differentiability of the sum. -/
lemma add_differentiableOnAlong {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s)
    (hY : DifferentiableOnAlong (I := I) (M := M) Y s) :
    DifferentiableOnAlong (I := I) (M := M) (add X Y) s := by
  unfold DifferentiableOnAlong at *
  exact hX.add hY

/-- Differentiability of a real-scalar multiple. -/
lemma smul_differentiableOnAlong {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smul a X) s := by
  unfold DifferentiableOnAlong at *
  exact hX.const_smul a

/-- Differentiability of a scalar-function multiple. -/
lemma smulFun_differentiableOnAlong {f : ℝ → ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : DifferentiableOn ℝ f s)
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smulFun f X) s := by
  unfold DifferentiableOnAlong at *
  exact hf.smul hX

end SectionAlongCurve

/-- Helper: the chart-coordinate curve `u(t) := φ_α(γ(t))`. -/
def chartCurve (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => extChartAt I α (γ t)

@[simp] lemma chartCurve_def (α : M) (γ : ℝ → M) (t : ℝ) :
    chartCurve (I := I) α γ t = extChartAt I α (γ t) := rfl

/-- The chart-local covariant derivative of a section `X` along `γ` at
time `t`, written in the chart at the basepoint `α : M`:
$$\Bigl(\frac{D X}{dt}\Bigr)(t)
  = X'(t) + \Gamma_\alpha(u'(t), X(t))(u(t)),$$
where `u(t) = φ_α(γ(t))`. The formula uses `deriv` for the
representation of the time-derivatives; it is the right expression
*only when* `X` and `u` are differentiable at `t`. -/
def chartCovDerivAlong (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) : E :=
  deriv X t +
    chartChristoffelContraction (I := I) g α
      (deriv (chartCurve (I := I) α γ) t) (X t)
      (chartCurve (I := I) α γ t)

@[simp] lemma chartCovDerivAlong_def
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t) (X t)
          (chartCurve (I := I) α γ t) := rfl

namespace ChartChristoffel

variable {g : SmoothRiemannianMetric I M} {α : M} {y : E}

/-- The Christoffel contraction is right-additive in its second vector
slot. -/
lemma contraction_add_right (v w₁ w₂ : E) :
    chartChristoffelContraction (I := I) g α v (w₁ + w₂) y =
      chartChristoffelContraction (I := I) g α v w₁ y +
        chartChristoffelContraction (I := I) g α v w₂ y := by
  classical
  unfold chartChristoffelContraction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show chartCoord (E := E) j (w₁ + w₂) =
      chartCoord (E := E) j w₁ + chartCoord (E := E) j w₂ from by
    unfold chartCoord; simp]
  ring

/-- The Christoffel contraction is left-additive in its first vector
slot. By the symmetry of the contraction in its arguments
(`chartChristoffelContraction_symm`), this is equivalent to right
additivity. -/
lemma contraction_add_left (v₁ v₂ w : E) :
    chartChristoffelContraction (I := I) g α (v₁ + v₂) w y =
      chartChristoffelContraction (I := I) g α v₁ w y +
        chartChristoffelContraction (I := I) g α v₂ w y := by
  rw [chartChristoffelContraction_symm, contraction_add_right,
    chartChristoffelContraction_symm (v := v₁) (w := w),
    chartChristoffelContraction_symm (v := v₂) (w := w)]

/-- The Christoffel contraction commutes with scalar multiplication in
the second vector slot. -/
lemma contraction_smul_right (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α v (a • w) y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul]
  ring

/-- The Christoffel contraction commutes with scalar multiplication in
the first vector slot. -/
lemma contraction_smul_left (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α (a • v) w y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  rw [chartChristoffelContraction_symm, contraction_smul_right,
    chartChristoffelContraction_symm (v := v) (w := w)]

/-- Zero on the right side: the Christoffel contraction is zero if the
second slot is zero. -/
lemma contraction_zero_right (v : E) :
    chartChristoffelContraction (I := I) g α v (0 : E) y = 0 := by
  rw [chartChristoffelContraction_symm, chartChristoffelContraction_zero_left]

end ChartChristoffel

/-- The continuous linear map `E → E` given by
`w ↦ chartChristoffelContraction g α v w y`. Linearity in `w` is by
`contraction_add_right` and `contraction_smul_right`. Boundedness on a
finite-dimensional vector space is automatic. -/
def chartChristoffelContractionRightCLM
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => chartChristoffelContraction (I := I) g α v w y
      map_add' := fun w₁ w₂ => ChartChristoffel.contraction_add_right v w₁ w₂
      map_smul' := fun a w => ChartChristoffel.contraction_smul_right a v w }

@[simp] lemma chartChristoffelContractionRightCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) (w : E) :
    chartChristoffelContractionRightCLM (I := I) g α v y w =
      chartChristoffelContraction (I := I) g α v w y := rfl

/-- The covariant-derivative formula expressed via a continuous linear
map: `D X / dt = X'(t) + A_t (X(t))`, where `A_t := chartChristoffelContractionRightCLM g α (u'(t)) (u(t))`
is the linear endomorphism of the model fibre that depends on the
chart-trajectory `u`. This is the formulation that feeds Picard–Lindelöf
for parallel transport (which corresponds to `D X / dt = 0`). -/
lemma chartCovDerivAlong_eq_add_clm
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContractionRightCLM (I := I) g α
          (deriv (chartCurve (I := I) α γ) t)
          (chartCurve (I := I) α γ t) (X t) := rfl

/-- Predicate "`W` is the covariant derivative of `Y` along `γ` on `s`,
written in the chart at `α`". The predicate uses `HasDerivAt` so the
section need only be differentiable at points of `s` (not necessarily
on a larger set). The chart-curve `u = chartCurve α γ` must have a
specified derivative `uPrime t` at `t`; we package this as a hypothesis
in the predicate body. -/
def IsCovDerivAlongChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y W : ℝ → E) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
    ∀ t ∈ s, HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t

/-- If `W = D Y / dt` in the predicate sense, then for every `t ∈ s`,
`Y'(t) + Γ_α(u'(t), Y(t))(u(t)) = W(t)`. -/
lemma IsCovDerivAlongChart.hasDerivAt_eq
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t :=
  h.2 t ht

/-- Linearity in `Y`: if `W_i = D Y_i / dt` for `i ∈ {1, 2}`, then
`W₁ + W₂ = D (Y₁ + Y₂) / dt`. -/
theorem IsCovDerivAlongChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y₁ Y₂ W₁ W₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₁ W₁ s)
    (h₂ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₂ W₂ s) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => Y₁ t + Y₂ t) (fun t => W₁ t + W₂ t) s := by
  refine ⟨h₁.1, ?_⟩
  intro t ht
  have hY₁ := h₁.2 t ht
  have hY₂ := h₂.2 t ht
  have hadd := hY₁.add hY₂
  have hΓadd :
      chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t + Y₂ t)
          (chartCurve (I := I) α γ t)
        = chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
              (chartCurve (I := I) α γ t)
          + chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_add_right (uPrime t) (Y₁ t) (Y₂ t)
  convert hadd using 1
  rw [hΓadd]; module

/-- Real-scalar linearity in `Y`: if `W = D Y / dt`, then `c • W = D (c • Y) / dt`. -/
theorem IsCovDerivAlongChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) (c : ℝ) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => c • Y t) (fun t => c • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hcY := hY.const_smul c
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (c • Y t)
          (chartCurve (I := I) α γ t)
        = c • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right c (uPrime t) (Y t)
  convert hcY using 1
  rw [hΓsmul, smul_sub]

/-- Negation closure: if `W = D Y / dt`, then `-W = D (-Y) / dt`. This
specialises `IsCovDerivAlongChart.smul` to the scalar `c = -1` and
rewrites the resulting `(-1) •`-expressions as negations on both the
section and its covariant derivative. -/
theorem IsCovDerivAlongChart.neg
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => - Y t) (fun t => - W t) s := by
  have hsmul := IsCovDerivAlongChart.smul (h := h) (-1 : ℝ)
  have hYeq : (fun t : ℝ => (-1 : ℝ) • Y t) = (fun t : ℝ => - Y t) := by
    funext t; rw [neg_one_smul]
  have hWeq : (fun t : ℝ => (-1 : ℝ) • W t) = (fun t : ℝ => - W t) := by
    funext t; rw [neg_one_smul]
  rw [hYeq, hWeq] at hsmul
  exact hsmul

/-- The zero section has zero covariant derivative. -/
theorem IsCovDerivAlongChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime (fun _ => (0 : E)) (fun _ => (0 : E)) s := by
  refine ⟨hu, ?_⟩
  intro t _
  have hΓ0 : chartChristoffelContraction (I := I) g α (uPrime t) (0 : E)
        (chartCurve (I := I) α γ t) = 0 :=
    ChartChristoffel.contraction_zero_right (uPrime t)
  rw [hΓ0]; simpa using (hasDerivAt_const t (0 : E))

/-- Leibniz rule for scalar-function multiples: if `W = D Y / dt`
(chart-α form) and `f : ℝ → ℝ` has derivative `fPrime t` at `t ∈ s`,
then `D (f · Y) / dt = f'(t) • Y(t) + f(t) • W(t)`. -/
theorem IsCovDerivAlongChart.smulFun
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s)
    {f : ℝ → ℝ} {fPrime : ℝ → ℝ}
    (hf : ∀ t ∈ s, HasDerivAt f (fPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => f t • Y t)
      (fun t => fPrime t • Y t + f t • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hft := hf t ht
  have hfY := hft.smul hY
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (f t • Y t)
          (chartCurve (I := I) α γ t)
        = f t • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right (f t) (uPrime t) (Y t)
  convert hfY using 1
  rw [hΓsmul, smul_sub]; module

/-- A section `Y` is parallel along `γ` on `s ⊆ ℝ` in the chart at `α`
iff `Y` satisfies the parallel-transport ODE
`Y'(t) = - Γ_α(u'(t), Y(t))(u(t))`. -/
def IsParallelChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsCovDerivAlongChart (I := I) g α γ uPrime Y (fun _ => (0 : E)) s

/-- Unfolding: `Y` is parallel iff the chart-curve has the prescribed
derivative and `Y'(t) = - Γ_α(u'(t), Y(t))(u(t))` for `t ∈ s`. -/
lemma IsParallelChart.hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t := by
  have := h.2 t ht
  simpa using this

/-- The chart-curve hypothesis embedded in `IsParallelChart`. -/
lemma IsParallelChart.chartCurve_hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t :=
  h.1 t ht

/-- Linearity of parallel transport: a real-scalar multiple of a
parallel section is parallel. -/
theorem IsParallelChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) (c : ℝ) :
    IsParallelChart (I := I) g α γ uPrime (fun t => c • Y t) s := by
  have hsmul := IsCovDerivAlongChart.smul (h := h) c
  have hzero : (fun t : ℝ => c • (0 : E)) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  convert hsmul using 1
  exact hzero.symm

/-- Additivity of parallel transport. -/
theorem IsParallelChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ s)
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ s) :
    IsParallelChart (I := I) g α γ uPrime (fun t => Y₁ t + Y₂ t) s := by
  have hadd := IsCovDerivAlongChart.add h₁ h₂
  have hzero : (fun t : ℝ => (0 : E) + 0) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  convert hadd using 1
  exact hzero.symm

/-- The Lipschitz constant for the parallel-transport vector field on a
real interval: the supremum of the operator norm of
`Y ↦ Γ_α(u'(t), Y)(u(t))` over `t ∈ s`. We expose it as a hypothesis
rather than constructing it explicitly; the existence on a compact
chart-interval follows from continuity of `t ↦ chartChristoffelContractionRightCLM g α (u'(t)) (u(t))`
in `t`, which is itself a downstream-of-`Picard-Lindelöf` development. -/
def ParallelTransportLipschitzBound (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (K : NNReal) (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    ‖chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)‖₊ ≤ K

/-- **Uniqueness of parallel transport (Gronwall).** On an open
interval `Ioo a b` with `t₀ ∈ Ioo a b`, two parallel sections sharing
an initial value at `t₀` agree on `Ioo a b`, given a uniform Lipschitz
bound on the right-hand side. -/
theorem IsParallelChart.unique_of_initial
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {K : NNReal}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ (Set.Ioo a b))
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) (hinit : Y₁ t₀ = Y₂ t₀) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) := by
  classical
  set v : ℝ → E → E :=
    fun t Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                  (chartCurve (I := I) α γ t) Y with hv_def
  have hLip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith K (v t) (Set.univ : Set E) := by
    intro t ht
    have hclm : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)) :=
      (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)).lipschitz
    have hclm_neg : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm.neg
    have hweak : LipschitzWith K
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm_neg.weaken (hK t ht)
    exact hweak.lipschitzOnWith
  have hY₁ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₁ (v t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    change HasDerivAt Y₁ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₁ t)) t
    exact h₁.hasDerivAt ht
  have hY₂ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₂ (v t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    change HasDerivAt Y₂ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₂ t)) t
    exact h₂.hasDerivAt ht
  exact ODE_solution_unique_of_mem_Ioo hLip ht₀ hY₁ hY₂ hinit

/-- **Uniqueness of parallel transport (local form).** Two parallel
sections sharing an initial value at `t₀` agree in some neighborhood of
`t₀`, provided the right-hand side is eventually-Lipschitz. -/
theorem IsParallelChart.unique_eventually
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {K : NNReal}
    (hLip : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K
      (fun Y : E => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t) Y) (Set.univ : Set E))
    (h₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
        (chartCurve (I := I) α γ t)) t)
    (h₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
        (chartCurve (I := I) α γ t)) t)
    (hinit : Y₁ t₀ = Y₂ t₀) : Y₁ =ᶠ[𝓝 t₀] Y₂ := by
  classical
  have hYY₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    refine h₁.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  have hYY₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    refine h₂.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  exact ODE_solution_unique_of_eventually hLip hYY₁ hYY₂ hinit

/-- `HasParallelTransportChart g α γ uPrime t₀ v₀ Y s` says that `Y` is
a parallel section along `γ` in the chart at `α` on `s ⊆ ℝ`, with
initial value `Y(t₀) = v₀`. This packages "Y is the parallel transport
of v₀ along γ at t₀ (in chart α)" into a Prop. -/
def HasParallelTransportChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (t₀ : ℝ) (v₀ : E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsParallelChart (I := I) g α γ uPrime Y s ∧ Y t₀ = v₀

/-- Parallel transport, when it exists, is uniquely determined by its
initial value on any open interval (with the standard Lipschitz hypothesis). -/
theorem HasParallelTransportChart.unique_of_lipschitz
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {v₀ : E} {K : NNReal}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₁ (Set.Ioo a b))
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) :=
  IsParallelChart.unique_of_initial h₁.1 h₂.1 hK ht₀
    (h₁.2.trans h₂.2.symm)

/-- The zero parallel transport: `Y ≡ 0` is the parallel transport of
the zero vector at any base time `t₀`, on any `s` where the
chart-curve has the prescribed derivative. -/
theorem HasParallelTransportChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E)
    (t₀ : ℝ) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (0 : E) (fun _ => (0 : E)) s := by
  refine ⟨?_, rfl⟩
  exact IsCovDerivAlongChart.zero g α γ uPrime s hu

/-- Linear superposition: if `Y₁` and `Y₂` are parallel transports of
`v₁` and `v₂` (with the same chart-curve derivative `uPrime`), then
`a • Y₁ + b • Y₂` is the parallel transport of `a • v₁ + b • v₂`. -/
theorem HasParallelTransportChart.linear_combination
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {v₁ v₂ : E} (a c : ℝ) {s : Set ℝ}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₁ Y₁ s)
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₂ Y₂ s) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (a • v₁ + c • v₂)
      (fun t => a • Y₁ t + c • Y₂ t) s := by
  refine ⟨?_, ?_⟩
  · have hY₁ := IsParallelChart.smul h₁.1 a
    have hY₂ := IsParallelChart.smul h₂.1 c
    exact IsParallelChart.add hY₁ hY₂
  · simp [h₁.2, h₂.2]

section MetricCompatibilityAlongCurve

open DifferentialGeometry.Integral.DivergenceTheorem

variable {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}

/-- The chart-frame coordinate of a section along the curve: the `i`-th
coordinate of `X(t)` in the canonical model basis `chartModelBasis E`. -/
def chartSectionCoord (X : ℝ → E) (i : Fin (Module.finrank ℝ E)) : ℝ → ℝ :=
  fun t => chartCoord (E := E) i (X t)

@[simp] lemma chartSectionCoord_def (X : ℝ → E) (i : Fin (Module.finrank ℝ E)) (t : ℝ) :
    chartSectionCoord (E := E) X i t = chartCoord (E := E) i (X t) := rfl

/-- The Gram quadratic form of two sections `V, W` along `γ`, written in
the chart at `α`:
`∑_{i,j} G_{ij}(u(t)) · Vᶜ_i(t) · Wᶜ_j(t)`, with `u := chartCurve α γ`. -/
def chartGramAlongCurve (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (V W : ℝ → E) (t : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
      chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)

@[simp] lemma chartGramAlongCurve_def
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E) (t : ℝ) :
    chartGramAlongCurve (I := I) g α γ V W t =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
          chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t) := rfl

/-- A model-fibre vector `v : E` expands in the chart frame at `x` as
`triv.symmL ℝ x v = ∑_i (chartCoord i v) • e_i(x)`. -/
lemma symmL_eq_sum_chartBasisVecFiber
    (α : M) {x : M}
    (v : E) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x v =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i x := by
  classical
  have hv : v = ∑ i : Fin (Module.finrank ℝ E),
      chartCoord (E := E) i v • (chartModelBasis E) i := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul]
  rfl

/-- For any `x : M`, the `g`-inner product of the chart-frame
sections `triv.symmL ℝ x V` and `triv.symmL ℝ x W` (the trivialization at
`α`) equals the Gram quadratic form `∑_{i,j} G_{ij}(x) · Vᶜ_i · Wᶜ_j`,
where `G_{ij}(x) = chartGramMatrix g α x i j`. -/
theorem inner_eq_chartGramOnE_bilinear_on_baseSet
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (V W : E) :
    g.inner x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x V)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x W) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α x i j *
          chartCoord (E := E) i V * chartCoord (E := E) j W := by
  classical
  rw [symmL_eq_sum_chartBasisVecFiber (I := I) α V,
      symmL_eq_sum_chartBasisVecFiber (I := I) α W]
  set vfib : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => chartBasisVecFiber (I := I) α i x with hvfib
  have hL :
      g.inner x (∑ i, chartCoord (E := E) i V • vfib i)
        = ∑ i, chartCoord (E := E) i V • g.inner x (vfib i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, hvfib, chartGramMatrix_apply]
  ring

/-- The chart-frame coordinate `chartCoord i ∘ X` has derivative
`chartCoord i (X'(t))` whenever `X` is differentiable at `t`; this is the
chain rule through the continuous-linear coordinate functional. -/
lemma chartSectionCoord_hasDerivAt
    {X : ℝ → E} {Xprime : ℝ → E} {t : ℝ} (i : Fin (Module.finrank ℝ E))
    (hX : HasDerivAt X (Xprime t) t) :
    HasDerivAt (chartSectionCoord (E := E) X i)
      (chartCoord (E := E) i (Xprime t)) t := by
  set L : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord i) with hL_def
  have hLapply : ∀ v : E, L v = chartCoord (E := E) i v := by
    intro v
    rw [hL_def]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rfl
  have hcomp : HasDerivAt (fun s : ℝ => L (X s)) (L (Xprime t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hX
  have hfun : (fun s : ℝ => L (X s)) = chartSectionCoord (E := E) X i := by
    funext s; rw [hLapply, chartSectionCoord_def]
  rw [hfun, hLapply] at hcomp
  exact hcomp

/-- The directional derivative of `chartGramOnE g α i j` at a point `y`
along a vector `v` expands in the model basis as the `chartCoord`-weighted
sum of the `partialDeriv`s:
`fderiv ℝ G_{ij} y v = ∑_k (chartCoord k v) · partialDeriv k G_{ij} y`. -/
lemma fderiv_chartGramOnE_eq_sum_partialDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y v : E) :
    fderiv ℝ (chartGramOnE (I := I) g α i j) y v =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k v *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y := by
  classical
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      chartCoord (E := E) k v • (chartModelBasis E) k := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

/-- The Gram coefficient along the curve `t ↦ G_{ij}(u(t))` has derivative
`∑_k (chartCoord k (u'(t))) · ∂_k G_{ij}(u(t))` at `t`, provided the
chart-curve `u = chartCurve α γ` has derivative `uPrime t` at `t` and lies
in the interior of the chart target there (so `G_{ij}` is differentiable). -/
lemma chartGramOnE_comp_chartCurve_hasDerivAt
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (i j : Fin (Module.finrank ℝ E)) {uPrime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s))
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (uPrime t) *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
            (chartCurve (I := I) α γ t)) t := by
  classical
  have hG_cd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hG_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (chartCurve (I := I) α γ t) := by
    have hint : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
        (interior (extChartAt I α).target) := hG_cd.mono interior_subset
    have hnhd : interior (extChartAt I α).target ∈
        𝓝 (chartCurve (I := I) α γ t) := isOpen_interior.mem_nhds hmem
    exact (hint.contDiffAt hnhd).differentiableAt (by simp)
  have hchain : HasDerivAt
      (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s))
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (chartCurve (I := I) α γ t)
        (uPrime t)) t :=
    (hG_diff.hasFDerivAt.comp_hasDerivAt t huPrime)
  rw [fderiv_chartGramOnE_eq_sum_partialDeriv (I := I) g α i j] at hchain
  exact hchain

/-- **Leibniz derivative of the chart Gram form along a curve.** For
sections `V, W` along `γ` (in chart-frame coordinates) and a chart-curve
`u = chartCurve α γ` differentiable at `t` with `u(t)` in the interior of
the chart target, the Gram quadratic form
`t ↦ ∑_{i,j} G_{ij}(u(t)) Vᶜ_i(t) Wᶜ_j(t)` has derivative
`∑_{i,j} [ (∑_k Vᵘ_k · ∂_k G_{ij}) Vᶜ_i Wᶜ_j
          + G_{ij} (Vᶜ_i)' Wᶜ_j
          + G_{ij} Vᶜ_i (Wᶜ_j)' ]`,
where `Vᵘ_k := chartCoord k (u'(t))`, `Vᶜ_i := chartCoord i (V t)`, etc. -/
theorem chartGramAlongCurve_hasDerivAt
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E)
    {uPrime Vprime Wprime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target)
    (hV : HasDerivAt V (Vprime t) t) (hW : HasDerivAt W (Wprime t) t) :
    HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V W s)
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t)))
      t := by
  classical
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s))
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t))
        t := by
    intro i j
    have hG := chartGramOnE_comp_chartCurve_hasDerivAt (I := I) g α γ i j huPrime hmem
    have hVi : HasDerivAt (fun s => chartCoord (E := E) i (V s))
        (chartCoord (E := E) i (Vprime t)) t :=
      chartSectionCoord_hasDerivAt (X := V) (Xprime := Vprime) i hV
    have hWj : HasDerivAt (fun s => chartCoord (E := E) j (W s))
        (chartCoord (E := E) j (Wprime t)) t :=
      chartSectionCoord_hasDerivAt (X := W) (Xprime := Wprime) j hW
    have hGV := hG.mul hVi
    have hGVW := hGV.mul hWj
    convert hGVW using 2
    ring
  have hsum : HasDerivAt
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s)))
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t)))
      t :=
    HasDerivAt.sum (fun i _ => HasDerivAt.sum (fun j _ => hterm i j))
  have hfun : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s)))
      = (fun s => chartGramAlongCurve (I := I) g α γ V W s) := by
    funext s
    rw [chartGramAlongCurve_def]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The `l`-th chart-coordinate of the Christoffel contraction:
`chartCoord l (Γ_α(v, w)(y)) = ∑_{i,j} Γ^l_{ij}(y) · vⁱ · wʲ`. -/
lemma chartCoord_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α : M) (v w y : E)
    (l : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α v w y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j l y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  rw [chartChristoffelContraction_def, chartCoord, map_sum, Finsupp.finset_sum_apply]
  have hbasis : ∀ k : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr ((chartModelBasis E) k) l = if k = l then 1 else 0 := by
    intro k
    classical
    exact (chartModelBasis E).repr_self_apply k l
  calc
    ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) •
            chartModelBasis E k)) l
      = ∑ k : Fin (Module.finrank ℝ E),
          (∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) *
            ((chartModelBasis E).repr (chartModelBasis E k) l) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j l y *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.sum_eq_single l]
        · rw [hbasis l]; simp
        · intro k _ hkl; rw [hbasis k, if_neg hkl]; ring
        · intro hl; exact absurd (Finset.mem_univ l) hl

/-- Reorder a four-fold finite sum, swapping the outermost and innermost
index.  Used to match the two index orderings of the chart-Christoffel
contraction in the metric-compatibility product rule. -/
private lemma sum4_swap_outer_inner {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d := by
  classical
  have e1 : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
  have e2 : (∑ a, ∑ b, ∑ d, ∑ c, f a b c d)
      = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  have e3 : (∑ a, ∑ d, ∑ b, ∑ c, f a b c d)
      = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
  have e4 : (∑ d, ∑ a, ∑ b, ∑ c, f a b c d)
      = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have g1 : (∑ a, ∑ b, ∑ c, f a b c d) = ∑ b, ∑ a, ∑ c, f a b c d := Finset.sum_comm
    have g2 : (∑ b, ∑ a, ∑ c, f a b c d) = ∑ b, ∑ c, ∑ a, f a b c d :=
      Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    exact g1.trans g2
  exact e1.trans (e2.trans (e3.trans e4))

/-- Reorder a three-fold finite sum, swapping the outermost and innermost
index (the middle one is fixed). -/
private lemma sum3_swap_outer_inner {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  classical
  have e1 : (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  have e2 : (∑ a, ∑ c, ∑ b, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
  have e3 : (∑ c, ∑ a, ∑ b, f a b c) = ∑ c, ∑ b, ∑ a, f a b c :=
    Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
  exact e1.trans (e2.trans e3)

/-- **Covariant-derivative product rule for the chart Gram form.** With
`u(t)` in the interior of the chart target, the derivative of the Gram
form `t ↦ ⟨V, W⟩_G(t)` equals the sum of the Gram forms of the
chart-covariant derivatives `D V/dt = V' + Γ_α(u', V)` against `W` and of
`V` against `D W/dt = W' + Γ_α(u', W)`:
`d/dt ⟨V, W⟩_G = ⟨DV/dt, W⟩_G + ⟨V, DW/dt⟩_G`. -/
theorem chartGramAlongCurve_hasDerivAt_covariant
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E)
    {uPrime Vprime Wprime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target)
    (hV : HasDerivAt V (Vprime t) t) (hW : HasDerivAt W (Wprime t) t) :
    HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V W s)
      ((∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α l j (chartCurve (I := I) α γ t) *
            chartCoord (E := E) l
              (Vprime t + chartChristoffelContraction (I := I) g α
                (uPrime t) (V t) (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) j (W t))
        + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i l (chartCurve (I := I) α γ t) *
            chartCoord (E := E) i (V t) *
            chartCoord (E := E) l
              (Wprime t + chartChristoffelContraction (I := I) g α
                (uPrime t) (W t) (chartCurve (I := I) α γ t))))
      t := by
  classical
  have hbase := chartGramAlongCurve_hasDerivAt (I := I) g α γ V W
    huPrime hmem hV hW
  set u := chartCurve (I := I) α γ t with hu_def
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartGramOnE (I := I) g α i j u with hG_def
  set Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun i j l => chartChristoffel (I := I) g α i j l u with hΓ_def
  set Vc : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i (V t) with hVc
  set Wc : Fin (Module.finrank ℝ E) → ℝ := fun j => chartCoord (E := E) j (W t) with hWc
  set uc : Fin (Module.finrank ℝ E) → ℝ := fun k => chartCoord (E := E) k (uPrime t) with huc
  set Vpc : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i (Vprime t) with hVpc
  set Wpc : Fin (Module.finrank ℝ E) → ℝ := fun j => chartCoord (E := E) j (Wprime t) with hWpc
  have hGsymm : ∀ a b : Fin (Module.finrank ℝ E), G a b = G b a := by
    intro a b; simp only [hG_def]; exact chartGramOnE_symm (I := I) g α a b u
  have hmc : ∀ i j k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u =
        (∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i) := by
    intro i j k
    exact DifferentialGeometry.Geometry.chartGramOnE_partialDeriv_eq_christoffel_sum_split
      (I := I) g α i j k hmem
  have hcovV : ∀ l : Fin (Module.finrank ℝ E),
      chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u)
        = Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i := by
    intro l
    rw [chartCoord, map_add, Finsupp.add_apply, ← chartCoord, ← chartCoord,
      chartCoord_chartChristoffelContraction (I := I) g α (uPrime t) (V t) u]
  have hcovW : ∀ l : Fin (Module.finrank ℝ E),
      chartCoord (E := E) l
          (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u)
        = Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j := by
    intro l
    rw [chartCoord, map_add, Finsupp.add_apply, ← chartCoord, ← chartCoord,
      chartCoord_chartChristoffelContraction (I := I) g α (uPrime t) (W t) u]
  have hval :
      (∑ l, ∑ j, G l j * chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) * Wc j)
        + (∑ i, ∑ l, G i l * Vc i *
            chartCoord (E := E) l
              (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
      = (∑ i, ∑ j,
          ((∑ k, uc k * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              Vc i * Wc j
            + G i j * Vpc i * Wc j
            + G i j * Vc i * Wpc j)) := by
    rw [show
        (∑ l, ∑ j, G l j * chartCoord (E := E) l
            (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) * Wc j)
          = ∑ l, ∑ j, G l j * (Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i) * Wc j from
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => by rw [hcovV l]))]
    rw [show
        (∑ i, ∑ l, G i l * Vc i * chartCoord (E := E) l
            (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
          = ∑ i, ∑ l, G i l * Vc i * (Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => by rw [hcovW l]))]
    rw [show
        (∑ i, ∑ j,
          ((∑ k, uc k * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j))
          = ∑ i, ∑ j,
            ((∑ k, uc k * ((∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i))) *
                Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        simp only [hmc i j]))]
    have hLHS :
        (∑ l, ∑ j, G l j * (Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i) * Wc j)
          + (∑ i, ∑ l, G i l * Vc i * (Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j))
        = (∑ l, ∑ j, G l j * Vpc l * Wc j)
          + (∑ i, ∑ l, G i l * Vc i * Wpc l)
          + (∑ l, ∑ j, ∑ k, ∑ i, G l j * (Γ k i l * uc k * Vc i) * Wc j)
          + (∑ i, ∑ l, ∑ k, ∑ j, G i l * Vc i * (Γ k j l * uc k * Wc j)) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf
    have hRHS :
        (∑ i, ∑ j,
          ((∑ k, uc k * ((∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i))) *
              Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j))
        = (∑ i, ∑ j, G i j * Vpc i * Wc j)
          + (∑ i, ∑ j, G i j * Vc i * Wpc j)
          + (∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k i l * G l j) * Vc i * Wc j)
          + (∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k j l * G l i) * Vc i * Wc j) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf
    rw [hLHS, hRHS]
    have hCV : (∑ l, ∑ j, ∑ k, ∑ i, G l j * (Γ k i l * uc k * Vc i) * Wc j)
        = ∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k i l * G l j) * Vc i * Wc j := by
      rw [sum4_swap_outer_inner (fun l j k i => G l j * (Γ k i l * uc k * Vc i) * Wc j)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))))
    have hCW : (∑ i, ∑ l, ∑ k, ∑ j, G i l * Vc i * (Γ k j l * uc k * Wc j))
        = ∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k j l * G l i) * Vc i * Wc j := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [sum3_swap_outer_inner (fun l k j => G i l * Vc i * (Γ k j l * uc k * Wc j))]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => ?_)))
      rw [hGsymm i l]; ring
    rw [hCV, hCW]
  rw [show (∑ l, ∑ j, chartGramOnE (I := I) g α l j u *
        chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) *
        chartCoord (E := E) j (W t))
      + (∑ i, ∑ l, chartGramOnE (I := I) g α i l u *
          chartCoord (E := E) i (V t) *
          chartCoord (E := E) l
            (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
      = (∑ i, ∑ j,
          ((∑ k, chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
            + chartGramOnE (I := I) g α i j u *
                chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
            + chartGramOnE (I := I) g α i j u *
                chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t))) from hval]
  exact hbase

end MetricCompatibilityAlongCurve

end AlongCurve
end Riemannian
end Geometry
end DifferentialGeometry
