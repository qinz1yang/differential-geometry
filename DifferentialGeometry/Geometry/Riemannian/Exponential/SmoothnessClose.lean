import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow

set_option linter.unusedSectionVars false

/-!
# Closing `expMap_contMDiffAt_zero_of_uniformChartFlowBridge`

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, this file delivers the
analytic ingredients needed to combine the chart-flow candidate's
`C^1` smoothness at `v = 0` with the manifold-side identification of
`expMap g p v` and `maximalGeodesic g p v 1`, closing the headline
`ContMDiffAt 𝓘(ℝ, E) I 1 (expMap g p) 0`.

## Components

* **Chart-coordinate geodesic rescaling**: at the chart-phase ODE level
  on `E × E`, the rescaling `(x, v) ↦ (x, a • v)` together with the
  time-rescaling `s ↦ a * s` preserves the chart-phase ODE. This is the
  chart-coord form of the standard geodesic invariance
  `γ_{p, a • v}(t) = γ_{p, v}(a t)`.

* **`UniformChartFlowBridge`**: a packaged uniform-in-`v` identification
  of the chart-flow candidate at time `t' = 1` with `expMap g p` on a
  neighbourhood of `0`. This is the substantive analytic input.

* **Headline**: `expMap_contMDiffAt_zero_of_uniformChartFlowBridge` is closed via
  `ContMDiffAt.congr_of_eventuallyEq` applied to the candidate's `C^1`
  smoothness.

The uniform-bridge input combines the per-`v` bridge
`chartPushedFlow_eq_maximalGeodesicChosenCurve_eventually_unconditional`
with chart-coordinate ODE uniqueness and the rescaling identity to
identify `expMap g p v` with the chart-flow candidate. Producing the
uniform bridge as an unconditional theorem is the next downstream step.

## Main results

* `chartPhaseVF_rescale` — `chartPhaseVF g α (x, a • v) =
  (a • v, -(a * a) • Γ_α(v, v)(x))`.

* `hasDerivAt_rescaled_orbit` — chain-rule chart-phase derivative of a
  rescaled orbit.

* `UniformChartFlowBridge` — packaged uniform-in-`v` identification.

* `expMap_contMDiffAt_zero_of_uniformChartFlowBridge` — the headline `ContMDiffAt 1` smoothness
  of `expMap g p` at `v = 0`, under the uniform-bridge hypothesis.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section ChartCoordRescaling

variable [I.Boundaryless]

/-- The chart-phase rescaling on `E × E`: scale the velocity component
by `a`. -/
def rescaleChartOrbit (a : ℝ) : E × E → E × E :=
  fun z => (z.1, a • z.2)

@[simp] lemma rescaleChartOrbit_apply (a : ℝ) (z : E × E) :
    rescaleChartOrbit a z = (z.1, a • z.2) := rfl

@[simp] lemma rescaleChartOrbit_mk (a : ℝ) (x v : E) :
    rescaleChartOrbit (E := E) a (x, v) = (x, a • v) := rfl

/-- **Chart-phase vector field at a rescaled point.** The chart-phase
vector field evaluated at `(x, a • v)`:
`chartPhaseVF g α (x, a • v) = (a • v, -(a * a) • Γ_α(v, v)(x))`. -/
lemma chartPhaseVF_rescale
    (g : SmoothRiemannianMetric I M) (α : M)
    (a : ℝ) (x v : E) :
    chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -(a * a) • chartChristoffelContraction (I := I) g α v v x) := by
  classical
  have h0 : chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -chartChristoffelContraction (I := I) g α (a • v) (a • v) x) := rfl
  rw [h0]
  refine Prod.ext rfl ?_
  have hΓ : chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      (a * a) • chartChristoffelContraction (I := I) g α v v x :=
    chartChristoffelContraction_smul_smul (I := I) g α a v x
  change -chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      -(a * a) • chartChristoffelContraction (I := I) g α v v x
  rw [hΓ, neg_smul]

/-- **Rescaled-orbit chain-rule chart-phase derivative.** If a curve
`c : ℝ → E × E` has a chart-phase derivative at the rescaled time
`a * s₀`, then the rescaled-orbit
`s ↦ rescaleChartOrbit a (c (a * s))` has a chart-phase derivative at
`s₀`. -/
lemma hasDerivAt_rescaled_orbit
    {g : SmoothRiemannianMetric I M} {α : M}
    {c : ℝ → E × E} {s₀ a : ℝ}
    (hd : HasDerivAt c (chartPhaseVF (I := I) g α (c (a * s₀))) (a * s₀)) :
    HasDerivAt (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s)))
      (chartPhaseVF (I := I) g α
        (rescaleChartOrbit (E := E) a (c (a * s₀)))) s₀ := by
  classical
  set z : E × E := c (a * s₀) with hz_def
  have hmul : HasDerivAt (fun s : ℝ => a * s) a s₀ := by
    have : HasDerivAt (fun s : ℝ => a * s) (a * 1) s₀ := (hasDerivAt_id s₀).const_mul a
    simpa using this
  have hcomp : HasDerivAt (fun s : ℝ => c (a * s))
      (a • chartPhaseVF (I := I) g α z) s₀ := hd.scomp s₀ hmul
  set rescale : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • (ContinuousLinearMap.id ℝ E))
    with hrescale_def
  have hrescale_apply : ∀ y : E × E, rescale y = (y.1, a • y.2) := by
    intro y
    change ((ContinuousLinearMap.id ℝ E) y.1, (a • (ContinuousLinearMap.id ℝ E)) y.2) =
        (y.1, a • y.2)
    refine Prod.ext rfl ?_
    change (a • (ContinuousLinearMap.id ℝ E)) y.2 = a • y.2
    rw [ContinuousLinearMap.smul_apply]
    rfl
  have hrescaled_eq : (fun s : ℝ => rescale (c (a * s))) =
      (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s))) := by
    funext s
    simp [rescaleChartOrbit, hrescale_apply]
  have hcomp_rescale : HasDerivAt (fun s : ℝ => rescale (c (a * s)))
      (rescale (a • chartPhaseVF (I := I) g α z)) s₀ :=
    rescale.hasFDerivAt.comp_hasDerivAt s₀ hcomp
  rw [hrescaled_eq] at hcomp_rescale
  have hrhs_eq :
      rescale (a • chartPhaseVF (I := I) g α z) =
        chartPhaseVF (I := I) g α
          (rescaleChartOrbit (E := E) a (c (a * s₀))) := by
    rw [hrescale_apply]
    have h_rescaled_form : rescaleChartOrbit (E := E) a (c (a * s₀)) =
        (z.1, a • z.2) := rfl
    rw [h_rescaled_form]
    rw [chartPhaseVF_rescale (I := I) g α a z.1 z.2]
    have hpvf : chartPhaseVF (I := I) g α z =
        (z.2, -chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl
    rw [hpvf]
    simp only [Prod.smul_mk, smul_neg, smul_smul]
    refine Prod.ext rfl ?_
    rw [neg_smul]
  rw [← hrhs_eq]
  exact hcomp_rescale

end ChartCoordRescaling

section UniformBridge

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Packaged uniform-in-`v` chart-flow bridge at a small time `t'`.**
The existence of a chart-flow `Φ`, a fixed time `t' > 0`, and a radius
`ρ > 0` such that:

* the manifold-valued chart-flow candidate at time `t'`,
  `chartFlowCandidate Φ p t' : E → M`, is `ContMDiffAt 𝓘(ℝ, E) I 1` at
  `v = 0`;

* and for all `v` in the ball of radius `ρ`,
  `expMap g p (t' • v) = chartFlowCandidate Φ p t' v` (the rescaled
  identification: the chart-flow's value at time `t'` along `(p, v)`
  equals the exponential map at `t' • v`).

This packages the analytic input for closing `expMap_contMDiffAt_zero_of_uniformChartFlowBridge`
via the chain rule: `expMap g p w = chartFlowCandidate Φ p t' (w / t')`
for `w` near `0`.
-/
def UniformChartFlowBridge (g : SmoothRiemannianMetric I M) (p : M) : Prop :=
  ∃ (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ), 0 < t' ∧ 0 < ρ ∧
    ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') (0 : E) ∧
    ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v

end UniformBridge

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **`expMap_contMDiffAt_zero_of_uniformChartFlowBridge` via the uniform chart-flow bridge.**
The exponential map `expMap g p`, viewed as a function `E → M` (using
`TangentSpace I p = E` definitionally), is `ContMDiffAt 𝓘(ℝ, E) I 1` at
the zero vector, provided the uniform-in-`v` bridge at some `t' > 0`
holds.

The proof composes the candidate's `C^1` smoothness with the smooth
scalar-multiplication `w ↦ w / t'`. Concretely, by the bridge,
`expMap g p w = chartFlowCandidate Φ p t' (w / t')` on a neighbourhood
of `w = 0`, and the right-hand side is `C^1` at `w = 0`. -/
theorem expMap_contMDiffAt_zero_of_uniformChartFlowBridge
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : UniformChartFlowBridge (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  classical
  obtain ⟨Φ, t', ρ, ht'_pos, hρ_pos, hcand_cd, heq⟩ := h
  set F : E → M := fun w : E =>
    chartFlowCandidate (I := I) Φ p t' ((1 / t') • w)
    with hF_def
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun w : E => (1 / t') • w) := by
    have : ContDiff ℝ ∞ (fun w : E => (1 / t') • w) :=
      (contDiff_const.smul contDiff_id)
    have h1 : ContDiff ℝ 1 (fun w : E => (1 / t') • w) :=
      this.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.contMDiff
  have hsmul_cda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun w : E => (1 / t') • w) (0 : E) := hsmul_cd.contMDiffAt
  have hval0 : (1 / t') • (0 : E) = 0 := smul_zero _
  have hF_cd : ContMDiffAt 𝓘(ℝ, E) I 1 F (0 : E) := by
    have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 1
        (chartFlowCandidate (I := I) Φ p t')
        ((fun w : E => (1 / t') • w) (0 : E)) := by
      change ContMDiffAt 𝓘(ℝ, E) I 1
          (chartFlowCandidate (I := I) Φ p t') ((1 / t') • (0 : E))
      rw [hval0]
      exact hcand_cd
    have hcomp : ContMDiffAt 𝓘(ℝ, E) I 1
        ((chartFlowCandidate (I := I) Φ p t') ∘ (fun w : E => (1 / t') • w))
        (0 : E) := hcand_cd'.comp (0 : E) hsmul_cda
    exact hcomp
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  have hev :
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)] F := by
    have hsmul_cont : Continuous (fun w : E => (1 / t') • w) :=
      continuous_const.smul continuous_id
    have hsmul_at0_zero : (fun w : E => (1 / t') • w) (0 : E) = 0 := hval0
    have hpre : (fun w : E => (1 / t') • w) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun w : E => (1 / t') • w) (0 : E)) := by
        rw [hsmul_at0_zero]
        exact Metric.ball_mem_nhds _ hρ_pos
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with w hw
    have hheq := heq ((1 / t') • w) hw
    have htv_eq_w : t' • ((1 / t') • w) = w := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htv_eq_w] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from w) : M) = F w
    rw [hF_def]
    exact hheq
  exact hF_cd.congr_of_eventuallyEq hev

/-- **Existence-form variant.** The headline packaged as taking an
explicit `∃`-statement. -/
theorem expMap_contMDiffAt_zero_exists
    (g : SmoothRiemannianMetric I M) (p : M)
    (huniform : ∃ (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ), 0 < t' ∧ 0 < ρ ∧
      ContMDiffAt 𝓘(ℝ, E) I 1
        (chartFlowCandidate (I := I) Φ p t') (0 : E) ∧
      ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
        (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
          chartFlowCandidate (I := I) Φ p t' v) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_of_uniformChartFlowBridge (I := I) (g := g) (p := p) huniform

end Headline

section UniformBridgePointwise

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- At `v = 0` and `t' = 0`, the chart-flow candidate value matches
`expMap g p 0 = p`, provided the chart-flow has the correct initial
condition. -/
lemma chartFlowCandidate_zero_matches_expMap_at_origin
    (g : SmoothRiemannianMetric I M) (p : M)
    {Φ : (E × E) × ℝ → E × E}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowCandidate (I := I) Φ p 0 (0 : E) =
      expMap (I := I) g p (show TangentSpace I p from (0 : E)) := by
  classical
  rw [show expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p from
    expMap_zero (I := I) g p]
  exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

end UniformBridgePointwise

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
