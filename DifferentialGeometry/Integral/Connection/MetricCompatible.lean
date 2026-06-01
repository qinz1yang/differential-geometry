import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import DifferentialGeometry.Integral.Measure.ChartDensity

/-!
# Metric compatibility for a covariant derivative on the tangent bundle

Given a smooth Riemannian metric `g : SmoothRiemannianMetric I M` and a
`CovariantDerivative I E (TangentSpace I)` on the tangent bundle of a manifold `M`,
we say that the covariant derivative is *metric-compatible* if it satisfies the
Leibniz / product rule for the inner product:

For all sections `Y, Z` of the tangent bundle which are differentiable at a point
`x : M`, and every tangent vector `v : TangentSpace I x`,
$$
  \mathrm{d}\bigl(b \mapsto g_b(Y_b, Z_b)\bigr)(x)\,v
    \;=\; g_x\bigl((\nabla_v Y)_x, Z_x\bigr) + g_x\bigl(Y_x, (\nabla_v Z)_x\bigr).
$$

The right-hand side uses the Mathlib argument convention `cov.toFun σ x v ≅ ∇_v σ`.
The left-hand side uses Mathlib's `mfderiv I 𝓘(ℝ)` applied to the scalar function
`b ↦ g.inner b (Y b) (Z b)`.

This file defines:

* `IsMetricCompatibleOn cov g s` — the local form of the predicate, on a set `s ⊆ M`,
  for an unbundled `cov : (Π x, TangentSpace I x) → (Π x, TangentSpace I x →L[ℝ] TangentSpace I x)`.
* `IsMetricCompatible cov g` — the global predicate, for a bundled
  `CovariantDerivative I E (TangentSpace I)`.

Both are `def : Prop`, not classes; this is a property of an existing covariant derivative,
not data.

The applied form `IsMetricCompatible.hasMFDerivAt` packages the derivative equation as a
`HasMFDerivAt` statement that composes well with downstream Riemannian-geometry calculations.
A symmetry corollary `IsMetricCompatible.swap` exchanges `Y` and `Z`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The covariant derivative `cov` (in unbundled form) is *metric-compatible* on a set `s ⊆ M`
with respect to `g` if, for every pair of tangent-bundle sections `Y, Z` differentiable at a
point `x ∈ s`, the directional derivative of the scalar function `b ↦ g.inner b (Y b) (Z b)`
at `x` decomposes via the connection:
$$
  \mathrm{d}\bigl(b \mapsto g_b(Y_b, Z_b)\bigr)(x)\,v
    = g_x((\nabla_v Y)_x, Z_x) + g_x(Y_x, (\nabla_v Z)_x).
$$

The Mathlib argument convention is `cov σ x v ≅ ∇_v σ x`. -/
def IsMetricCompatibleOn
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (g : Measure.SmoothRiemannianMetric I M) (s : Set M := Set.univ) : Prop :=
  ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
    MDiffAt (T% Y) x → MDiffAt (T% Z) x → x ∈ s →
    ∀ v : TangentSpace I x,
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
        g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)

/-- The covariant derivative `cov` is *metric-compatible* with respect to `g` if it is
metric-compatible on all of `M`. Phrased for a bundled `CovariantDerivative`. -/
def IsMetricCompatible (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : Measure.SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatibleOn cov.toFun g Set.univ

/-- The Leibniz / metric-compatibility differential as a continuous linear functional on
`TangentSpace I x`. This packages the right-hand side of the metric-compatibility identity
$$
  v \mapsto g_x(\mathrm{covY}\,v, Z_x) + g_x(Y_x, \mathrm{covZ}\,v)
$$
as a CLM. The first summand is rewritten via inner-product symmetry as
`g_x(Z_x, \mathrm{covY}\,v)` so that the whole expression is a sum of `comp`-ositions of
continuous linear maps. -/
def metricCompatibleDifferential
    (g : Measure.SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) : TangentSpace I x →L[ℝ] ℝ :=
  (g.inner x Zx).comp covY + (g.inner x Yx).comp covZ

@[simp]
lemma metricCompatibleDifferential_apply
    (g : Measure.SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) (v : TangentSpace I x) :
    metricCompatibleDifferential g covY covZ Yx Zx v =
      g.inner x Zx (covY v) + g.inner x Yx (covZ v) := rfl

namespace IsMetricCompatibleOn

variable
    {cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    {g : Measure.SmoothRiemannianMetric I M}

/-- Restrict metric compatibility from a larger to a smaller set. -/
lemma mono {s t : Set M} (h : IsMetricCompatibleOn cov g t) (hst : s ⊆ t) :
    IsMetricCompatibleOn cov g s :=
  fun _Y _Z _x hY hZ hxs v => h hY hZ (hst hxs) v

/-- Metric compatibility is local on the base: if it holds on each `s i`, it holds on
`⋃ i, s i`. This mirrors `IsCovariantDerivativeOn.iUnion`. -/
lemma iUnion {ι : Type*} {s : ι → Set M}
    (h : ∀ i, IsMetricCompatibleOn cov g (s i)) :
    IsMetricCompatibleOn cov g (⋃ i, s i) := by
  intro Y Z x hY hZ hx v
  obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
  exact h i hY hZ hxsi v

/-- Symmetry corollary on a set: swapping `Y` and `Z` in the metric-compatibility identity
yields an equivalent equation, by symmetry of the inner product. -/
lemma swap {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov Z x v) (Y x) + g.inner x (Z x) (cov Y x v) := by
  have hfun : (fun b => g.inner b (Z b) (Y b)) = (fun b => g.inner b (Y b) (Z b)) := by
    funext b; exact (g.symm b (Z b) (Y b))
  rw [hfun]
  have hYZ := h hY hZ hxs v
  rw [g.symm x (cov Z x v) (Y x), g.symm x (Z x) (cov Y x v),
      add_comm]
  exact hYZ

/-- Pointwise applied form: alias for the predicate's body, exposed via
dot-notation on `IsMetricCompatibleOn`. -/
lemma apply {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v) :=
  h hY hZ hxs v

/-- `HasMFDerivAt` form of metric compatibility: the `mfderiv` of
`b ↦ g.inner b (Y b) (Z b)` at `x` is
`metricCompatibleDifferential g (cov Y x) (cov Z x) (Y x) (Z x)`.
The differentiability of `b ↦ g.inner b (Y b) (Z b)` is supplied by the caller (typically
obtained from `ContMDiff.inner_bundle` plus `ContMDiffAt.mdifferentiableAt`). -/
lemma hasMFDerivAt {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (hsmooth : MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov Y x) (cov Z x) (Y x) (Z x)) := by
  refine hsmooth.hasMFDerivAt.congr_mfderiv ?_
  ext v
  change (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (Z x) (cov Y x v) + g.inner x (Y x) (cov Z x v)
  rw [h hY hZ hxs v, g.symm x (cov Y x v) (Z x)]

end IsMetricCompatibleOn

namespace IsMetricCompatible

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {g : Measure.SmoothRiemannianMetric I M}

/-- Pointwise applied form: from metric compatibility, the directional-derivative identity
at any point `x` and any tangent vector `v`, given that the two sections are differentiable
at `x`. -/
lemma apply (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov.toFun Y x v) (Z x) + g.inner x (Y x) (cov.toFun Z x v) :=
  h hY hZ (Set.mem_univ _) v

/-- Symmetry corollary: swapping `Y` and `Z` in the metric-compatibility identity yields
an equivalent equation, by symmetry of the inner product. -/
lemma swap (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov.toFun Z x v) (Y x) + g.inner x (Z x) (cov.toFun Y x v) :=
  IsMetricCompatibleOn.swap h hY hZ (Set.mem_univ _) v

/-- `HasMFDerivAt` form, given differentiability of the inner-product function at `x`. -/
lemma hasMFDerivAt (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hsmooth :
      MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov.toFun Y x) (cov.toFun Z x) (Y x) (Z x)) :=
  IsMetricCompatibleOn.hasMFDerivAt h hY hZ (Set.mem_univ _) hsmooth

/-- A globally metric-compatible covariant derivative is metric-compatible on every set `s`,
in the local sense. -/
lemma toIsMetricCompatibleOn (h : IsMetricCompatible cov g) {s : Set M} :
    IsMetricCompatibleOn cov.toFun g s :=
  IsMetricCompatibleOn.mono (t := Set.univ) h (fun _ _ => trivial)

@[simp]
lemma toIsMetricCompatibleOn_univ_iff :
    IsMetricCompatibleOn cov.toFun g Set.univ ↔ IsMetricCompatible cov g := Iff.rfl

end IsMetricCompatible

/-- A covariant derivative which is locally metric-compatible on `Set.univ` is globally
metric-compatible. This is the converse direction enabling the chart-local form to chain
with `IsCovariantDerivativeOn.iUnion`. -/
lemma IsMetricCompatibleOn.toIsMetricCompatible
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : Measure.SmoothRiemannianMetric I M}
    (h : IsMetricCompatibleOn cov.toFun g Set.univ) :
    IsMetricCompatible cov g := h

end Connection
end Integral
end DifferentialGeometry
