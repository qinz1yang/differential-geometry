import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Intrinsic
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option linter.unusedSectionVars false

/-!
# Vanishing of velocity off the chart source

For a smooth Riemannian metric `g` on a boundaryless smooth manifold
`M`, the chart-fixed geodesic vector field `geodesicVectorFieldChart
g α` is defined via a trivialisation of `T(TM)` whose base set is
`(chartAt H α).source` (lifted to `TM`). Outside this base set,
Mathlib's `Trivialization.symm_apply_of_notMem` ensures the inverse
trivialisation returns zero — hence the chart-fixed geodesic vector
field vanishes off the chart source.

For a curve `γ : ℝ → M` witnessed as a geodesic with basepoint `α`,
the lift `f : ℝ → TangentBundle I M` is an integral curve of
`geodesicVectorFieldChart g α`. At any time `t` where `γ t` exits the
chart-α source, the vector field's vanishing forces the lift's
manifold derivative — and hence the intrinsic velocity `velocity γ t`
— to vanish.

## Main results

* `geodesicVectorFieldChart_eq_zero_of_proj_notMem` — the chart-fixed
  geodesic vector field is zero outside the chart source.

* `velocity_eq_zero_of_proj_notMem` — the intrinsic velocity vanishes
  at off-chart-source times.

* `IsGeodesic.speedSq_eq_zero_of_notMem_witness_chartSource` — the
  squared speed of a global geodesic vanishes at off-chart-source
  times.

* `isGeodesic_const.inner_velocity_const` — constant speed for the
  constant curve, via direct computation.

## The general headline is recorded as a downstream goal

The general headline (constant speed at *all* pairs of times for any
`C²` geodesic) requires combining the off-chart vanishing with a
chart-source derivative-zero computation (the chart-coordinate
metric-compatibility identity specialised to `V = W = velocity γ`)
and a connectedness gluing argument. The chart-source computation in
turn requires either (a) a chart-overlap transformation law for
Christoffel symbols (currently a pending mathematical prerequisite,
see `Geometry/Riemannian/Geodesic/Intrinsic.lean`) or (b) a direct
chart-α₀ four-index cancellation argument mirroring the metric-
compatibility identity in `Curve/CovDerivAlongMetric.lean`. We
document the structure here and defer the full headline pending the
chart-overlap law.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Curve

/-! ## Squared speed -/

/-- The squared speed of a curve at a given time, with respect to a
smooth Riemannian metric. -/
def speedSq (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)

@[simp] lemma speedSq_def (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speedSq (I := I) g γ t =
      g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := rfl

/-! ## Vanishing of the geodesic vector field off the chart source -/

/-- The chart-fixed geodesic vector field vanishes when `p.proj` is
outside `(chartAt H α).source`. The vector field is defined via the
trivialisation's `.symm`, which by Mathlib's
`Trivialization.symm_apply_of_notMem` returns zero off the base set. -/
lemma geodesicVectorFieldChart_eq_zero_of_proj_notMem
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p.proj ∉ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = 0 := by
  classical
  unfold geodesicVectorFieldChart
  have hbase_set_eq := geodesicChartDomain_eq_trivBaseSet (I := I) (M := M) α
  have hp_not_base : p ∉ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [← hbase_set_eq]
    intro hp_in
    exact hp hp_in
  exact (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).symm_apply_of_notMem hp_not_base _

/-! ## Vanishing of the intrinsic velocity off the chart source

For a global geodesic witnessed by basepoint `α`, the intrinsic
velocity vanishes off the chart-α source. We use the rosetta-stone
bridge `velocity_eq_mfderiv_proj_of_isMIntegralCurveAt` together with
the vector-field vanishing above. -/

/-- The intrinsic velocity vanishes when the foot of the lift is off
the witness chart source. -/
theorem velocity_eq_zero_of_proj_notMem
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀)
    (h : γ t₀ ∉ (chartAt H α).source) :
    velocity (I := I) γ t₀ = 0 := by
  classical
  have hvel := velocity_eq_mfderiv_proj_of_isMIntegralCurveAt (I := I)
    (V := geodesicVectorFieldChart (I := I) g α) hproj hf
  have hf_proj : (f t₀).proj = γ t₀ := hproj t₀
  have hf_not : (f t₀).proj ∉ (chartAt H α).source := hf_proj ▸ h
  have hVeq : geodesicVectorFieldChart (I := I) g α (f t₀) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_proj_notMem (I := I) g α hf_not
  rw [hvel, hVeq, map_zero]
  rfl

/-- The squared speed vanishes when the foot of the lift is off the
witness chart source. -/
theorem speedSq_eq_zero_of_proj_notMem
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀)
    (h : γ t₀ ∉ (chartAt H α).source) :
    speedSq (I := I) g γ t₀ = 0 := by
  unfold speedSq
  rw [velocity_eq_zero_of_proj_notMem (I := I) hproj hf h]
  simp

/-- **Off-chart-source vanishing of squared speed for a global geodesic.**
For any global geodesic `γ` with witness basepoint `α`, the squared
speed vanishes at any time `t` where `γ t ∉ (chartAt H α).source`. -/
theorem IsGeodesic.speedSq_eq_zero_of_notMem_witness_chartSource
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : IsGeodesic (I := I) g γ) {t : ℝ}
    (hno : ∃ α f, (∀ s, (f s).proj = γ s) ∧
      IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α) ∧
      γ t ∉ (chartAt H α).source) :
    speedSq (I := I) g γ t = 0 := by
  obtain ⟨α, f, hproj, hf, hnot⟩ := hno
  exact speedSq_eq_zero_of_proj_notMem (I := I) hproj (hf.isMIntegralCurveAt t) hnot

/-! ## Constant-curve case of the headline

The constant curve has zero velocity at every time, hence constant
(zero) speed. -/

/-- For the constant curve, the intrinsic velocity at every time is
zero, so the squared speed is identically zero. -/
theorem velocity_const (p : M) (t : ℝ) :
    velocity (I := I) (fun _ : ℝ => p) t = 0 := by
  -- The constant curve has zero manifold derivative.
  unfold velocity
  -- `mfderiv 𝓘(ℝ, ℝ) I (fun _ => p) t = 0` by `mfderiv_const`.
  rw [mfderiv_const]
  rfl

/-- Constant-curve case of the headline. -/
theorem inner_velocity_const_of_const
    (g : SmoothRiemannianMetric I M) (p : M) (t₀ t₁ : ℝ) :
    g.inner ((fun _ : ℝ => p) t₀)
      (velocity (I := I) (fun _ : ℝ => p) t₀)
      (velocity (I := I) (fun _ : ℝ => p) t₀) =
    g.inner ((fun _ : ℝ => p) t₁)
      (velocity (I := I) (fun _ : ℝ => p) t₁)
      (velocity (I := I) (fun _ : ℝ => p) t₁) := by
  rw [velocity_const, velocity_const]

/-! ## Pointwise headline-along-a-witness

When two times both lie in the chart-source complement of the witness,
the squared speed is zero at both, hence equal. -/

theorem inner_velocity_eq_of_both_notMem
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : IsGeodesic (I := I) g γ) {α : M} {f : ℝ → TangentBundle I M}
    (hwit : (∀ t, (f t).proj = γ t) ∧
      IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    {t₀ t₁ : ℝ}
    (h₀ : γ t₀ ∉ (chartAt H α).source)
    (h₁ : γ t₁ ∉ (chartAt H α).source) :
    g.inner (γ t₀) (velocity (I := I) γ t₀) (velocity (I := I) γ t₀) =
    g.inner (γ t₁) (velocity (I := I) γ t₁) (velocity (I := I) γ t₁) := by
  classical
  have hsq0 : speedSq (I := I) g γ t₀ = 0 :=
    speedSq_eq_zero_of_proj_notMem (I := I) hwit.1 (hwit.2.isMIntegralCurveAt t₀) h₀
  have hsq1 : speedSq (I := I) g γ t₁ = 0 :=
    speedSq_eq_zero_of_proj_notMem (I := I) hwit.1 (hwit.2.isMIntegralCurveAt t₁) h₁
  -- speedSq is g.inner ... ... by definition.
  change speedSq (I := I) g γ t₀ = speedSq (I := I) g γ t₁
  rw [hsq0, hsq1]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
