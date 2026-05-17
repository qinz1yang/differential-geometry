import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Intrinsic
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlongMetric
import DifferentialGeometry.Integral.Connection.ChartMetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option linter.unusedSectionVars false

/-!
# Constant speed of geodesics

For a `C²` geodesic `γ : ℝ → M` on a smooth Riemannian manifold `(M, g)`,
the squared speed `t ↦ g.inner (γ t) (velocity γ t) (velocity γ t)` is
constant in `t`. The proof works directly in the chart at the
`IsGeodesic`-witness basepoint `α`, exploiting:

* the chart-α integral-curve identity `HasDerivAt (chartFiberCoord α ∘ f)
  (-Γ_α(v, v)(y)) t` and `HasDerivAt (extChartAt I α ∘ γ) v t` on the
  chart-α domain;
* the chart-metric identity `∂_k G_{ij}(y) = ∑_l Γ^l_{ki}(y) G_{lj}(y)
  + ∑_l Γ^l_{kj}(y) G_{li}(y)`;
* a four-index reindexing-and-symmetry cancellation that collapses the
  derivative to zero on the chart-α domain;
* the off-chart vanishing of the velocity (the geodesic vector field is
  zero outside the chart base set, hence the lift is locally constant
  there, and the projection's velocity vanishes);
* gluing the on-chart and off-chart pieces via continuity of the squared
  speed (a consequence of `C²` smoothness of `γ`).

## Main results

* `IsGeodesic.inner_velocity_const` — the headline: for any two times,
  the squared speed of a `C²` geodesic agrees.
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
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
outside `(chartAt H α).source`. -/
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

/-! ## Vanishing of the intrinsic velocity off the chart source -/

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

/-- **Off-chart-source vanishing of squared speed for a global geodesic.** -/
theorem IsGeodesic.speedSq_eq_zero_of_notMem_witness_chartSource
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (_hγ : IsGeodesic (I := I) g γ) {t : ℝ}
    (hno : ∃ α f, (∀ s, (f s).proj = γ s) ∧
      IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α) ∧
      γ t ∉ (chartAt H α).source) :
    speedSq (I := I) g γ t = 0 := by
  obtain ⟨α, f, hproj, hf, hnot⟩ := hno
  exact speedSq_eq_zero_of_proj_notMem (I := I) hproj (hf.isMIntegralCurveAt t) hnot

/-! ## Constant-curve case -/

/-- For the constant curve, the intrinsic velocity at every time is zero. -/
theorem velocity_const (p : M) (t : ℝ) :
    velocity (I := I) (fun _ : ℝ => p) t = 0 := by
  unfold velocity
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

/-! ## Both-off-chart case -/

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
  change speedSq (I := I) g γ t₀ = speedSq (I := I) g γ t₁
  rw [hsq0, hsq1]

/-! ## The chart-α machinery for constant speed

We work in a fixed chart at the `IsGeodesic`-witness basepoint `α`. On the
chart-α domain `γ⁻¹((chartAt H α).source)`, the chart-pushed lift
`(t ↦ (extChartAt I α (γ t), chartFiberCoord α (f t)))` has derivative
`(chartFiberCoord α (f t), -Γ_α(v, v)(y))` — the chart-α geodesic
equation. We exploit this together with the chart-metric identity to
show that the chart-α-relative squared speed has derivative zero. -/

section ChartAlpha

variable [I.Boundaryless] [CompleteSpace E]

/-- The chart-α coordinate of the lift at time `t`: an element of `E`. -/
def vCoord (α : M) (f : ℝ → TangentBundle I M) (t : ℝ) : E :=
  chartFiberCoord (I := I) α (f t)

@[simp] lemma vCoord_def (α : M) (f : ℝ → TangentBundle I M) (t : ℝ) :
    vCoord (I := I) α f t = chartFiberCoord (I := I) α (f t) := rfl

/-- The chart-α base coordinate of `γ t`: an element of `E`. -/
def yCoord (α : M) (γ : ℝ → M) (t : ℝ) : E := extChartAt I α (γ t)

@[simp] lemma yCoord_def (α : M) (γ : ℝ → M) (t : ℝ) :
    yCoord (I := I) α γ t = extChartAt I α (γ t) := rfl

/-! ### Chart-α `HasDerivAt`-formulae from the integral-curve property -/

/-- On the chart-α domain, the chart-pushed lift through the extended
chart at `⟨α, 0⟩` has derivative equal to the chart-fiber data
`(v(t), -Γ_α(v(t), v(t))(y(t)))` of the geodesic vector field. -/
private lemma chartPushLift_α_hasDerivAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    HasDerivAt
      (fun s => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s))
      (geodesicVectorFieldChartFiber (I := I) g α (f t)) t := by
  classical
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV_def
  have hf_mf : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent f t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t))) := hpath.hasMFDerivAt
  have hf_proj : (f t).proj = γ t := hproj t
  have hf_proj_chart : (f t).proj ∈ (chartAt H α).source := hf_proj ▸ hbase
  have hp' : f t ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) (f t)
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hf_proj_chart
  have hchart_mdiff : MDifferentiableAt I.tangent 𝓘(ℝ, E × E)
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t) :=
    mdifferentiableAt_extChartAt (I := I.tangent) hp'
  have hcomp_mf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E × E)
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘ f) t
      ((mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) :=
    hchart_mdiff.hasMFDerivAt.comp t hf_mf
  have hcomp_fd : HasFDerivAt
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘ f)
      ((mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) t :=
    hcomp_mf.hasFDerivAt
  have hcomp_da : HasDerivAt
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘ f)
      (((mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) (1 : ℝ)) t :=
    hcomp_fd.hasDerivAt
  have hval :
      (((mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) (1 : ℝ)) =
      (mfderiv I.tangent 𝓘(ℝ, E × E)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t))
          (V (f t)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul]
  rw [hval] at hcomp_da
  have hp_baseSet : f t ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp'
  have hmfd_eq := TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I.tangent) (M := TangentBundle I M)
    (x₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (x := f t) hp'
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hV_eq : V (f t) = e.symmL ℝ (f t)
      (geodesicVectorFieldChartFiber (I := I) g α (f t)) := rfl
  have hkey :
      (mfderiv I.tangent 𝓘(ℝ, E × E)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t))
          (V (f t)) =
      geodesicVectorFieldChartFiber (I := I) g α (f t) := by
    rw [← hmfd_eq, hV_eq]
    exact e.continuousLinearMapAt_symmL hp_baseSet _
  rw [hkey] at hcomp_da
  exact hcomp_da

/-- Pointwise decomposition of `extChartAt I.tangent ⟨α, 0⟩` applied to a
bundle point `q`. -/
private lemma extChartAt_tangent_zeroSection_apply_eq (α : M)
    (q : TangentBundle I M) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q =
      (extChartAt I α q.proj, chartFiberCoord (I := I) α q) := by
  classical
  have hfst := fst_extChartAt_tangent_zeroSection_apply (I := I) α q
  refine Prod.ext hfst ?_
  -- snd: identify `(extChartAt I.tangent ⟨α,0⟩ q).2` with `chartFiberCoord α q`.
  have hfb : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q =
      ((extChartAt I α).prod (PartialEquiv.refl E))
        ((trivializationAt E (TangentSpace I) α).toPartialEquiv q) := by
    have := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
      (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q = _
    rw [this]
    rfl
  rw [hfb]
  rfl

/-- **Chart-α geodesic equation (II): chart base velocity equals fiber.** -/
private lemma hasDerivAt_yCoord
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    HasDerivAt (yCoord (I := I) α γ) (vCoord (I := I) α f t) t := by
  classical
  have hpush := chartPushLift_α_hasDerivAt (I := I) g α hproj hpath hbase
  have hfst_fd : HasFDerivAt
      (fun s => (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).1)
      (ContinuousLinearMap.fst ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) t :=
    hpush.hasFDerivAt.fst
  have hfst_da : HasDerivAt
      (fun s => (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).1)
      ((ContinuousLinearMap.fst ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) (1 : ℝ)) t :=
    hfst_fd.hasDerivAt
  have hval : (ContinuousLinearMap.fst ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) (1 : ℝ) =
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).1 := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply]
  rw [hval] at hfst_da
  have hfst_val :
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).1 =
        chartFiberCoord (I := I) α (f t) := rfl
  rw [hfst_val] at hfst_da
  have hfun : (fun s => (extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).1) =
      yCoord (I := I) α γ := by
    funext s
    have hd := extChartAt_tangent_zeroSection_apply_eq (I := I) α (f s)
    have h1 : (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).1 =
        extChartAt I α (f s).proj := by rw [hd]
    rw [h1, hproj s]
    rfl
  rw [hfun] at hfst_da
  change HasDerivAt (yCoord (I := I) α γ) _ t
  exact hfst_da

/-- **Chart-α geodesic equation (I): fiber velocity equals `-Γ`.** -/
private lemma hasDerivAt_vCoord
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    HasDerivAt (vCoord (I := I) α f)
      (- chartChristoffelContraction (I := I) g α
          (vCoord (I := I) α f t) (vCoord (I := I) α f t)
          (yCoord (I := I) α γ t)) t := by
  classical
  have hpush := chartPushLift_α_hasDerivAt (I := I) g α hproj hpath hbase
  have hsnd_fd : HasFDerivAt
      (fun s => (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).2)
      (ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) t :=
    hpush.hasFDerivAt.snd
  have hsnd_da : HasDerivAt
      (fun s => (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).2)
      ((ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) (1 : ℝ)) t :=
    hsnd_fd.hasDerivAt
  have hval : (ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (geodesicVectorFieldChartFiber (I := I) g α (f t)))) (1 : ℝ) =
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).2 := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply]
  rw [hval] at hsnd_da
  have hsnd_val :
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).2 =
        - chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α (f t))
            (chartFiberCoord (I := I) α (f t))
            (extChartAt I α (f t).proj) := rfl
  rw [hsnd_val] at hsnd_da
  have hfun : (fun s => (extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M) (f s)).2) =
      vCoord (I := I) α f := by
    funext s
    have hd := extChartAt_tangent_zeroSection_apply_eq (I := I) α (f s)
    rw [hd]
    rfl
  rw [hfun] at hsnd_da
  rw [hproj t] at hsnd_da
  change HasDerivAt (vCoord (I := I) α f) _ t
  exact hsnd_da

/-! ### Chart-α-relative squared speed -/

/-- The chart-α-relative squared speed:
`∑_{ij} G_{ij}(y(t)) * v^i(t) * v^j(t)`. -/
def speedSqChart (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (f : ℝ → TangentBundle I M) (t : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
      chartCoord (E := E) i (vCoord (I := I) α f t) *
      chartCoord (E := E) j (vCoord (I := I) α f t)

@[simp] lemma speedSqChart_def (g : SmoothRiemannianMetric I M) (α : M)
    (γ : ℝ → M) (f : ℝ → TangentBundle I M) (t : ℝ) :
    speedSqChart (I := I) g α γ f t =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
          chartCoord (E := E) i (vCoord (I := I) α f t) *
          chartCoord (E := E) j (vCoord (I := I) α f t) := rfl

/-! ### `speedSqChart = speedSq` on the chart-α domain -/

private lemma speedSqChart_eq_speedSq
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    speedSqChart (I := I) g α γ f t = speedSq (I := I) g γ t := by
  classical
  unfold speedSqChart speedSq
  have hxbase : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hbase
  have hxsrc : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hbase
  have hsum := g_inner_eq_chart_sum (I := I) g α (x := γ t) hxbase hxsrc
    (velocity (I := I) γ t) (velocity (I := I) γ t)
  rw [hsum]
  have hvel := velocity_eq_snd_of_isMIntegralCurveAt (I := I) g α
    hproj hpath hbase
  have hclm_eq : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        (γ t)) (velocity (I := I) γ t) = chartFiberCoord (I := I) α (f t) := by
    have hcoord_eq := chartFiberCoord_eq_clmAt_of_mem (I := I) α
      (velocity (I := I) γ t) hbase
    rw [← hcoord_eq]
    have hpt_eq : (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M) = f t := by
      rw [hvel]
      refine Bundle.TotalSpace.ext (hproj t).symm ?_
      change HEq ((hproj t) ▸ (f t).2 : TangentSpace I (γ t)) (f t).2
      exact eqRec_heq (hproj t) ((f t).2)
    rw [hpt_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hrepri : ((chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t)
        (velocity (I := I) γ t))) i =
      chartCoord (E := E) i (chartFiberCoord (I := I) α (f t)) := by
    rw [hclm_eq]; rfl
  have hreprj : ((chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t)
        (velocity (I := I) γ t))) j =
      chartCoord (E := E) j (chartFiberCoord (I := I) α (f t)) := by
    rw [hclm_eq]; rfl
  rw [hrepri, hreprj]
  -- After rw, goal is:
  --   chartGramOnE g α i j (yCoord α γ t) * chartCoord i (vCoord α f t) * chartCoord j (vCoord α f t)
  -- = chartCoord i (chartFiberCoord α (f t)) * chartCoord j (chartFiberCoord α (f t))
  --   * chartGramOnE g α i j (extChartAt I α (γ t)).
  -- yCoord α γ t = extChartAt I α (γ t), vCoord α f t = chartFiberCoord α (f t) (both rfl).
  change chartGramOnE (I := I) g α i j (extChartAt I α (γ t)) *
      chartCoord (E := E) i (chartFiberCoord (I := I) α (f t)) *
      chartCoord (E := E) j (chartFiberCoord (I := I) α (f t)) =
    chartCoord (E := E) i (chartFiberCoord (I := I) α (f t)) *
      chartCoord (E := E) j (chartFiberCoord (I := I) α (f t)) *
      chartGramOnE (I := I) g α i j (extChartAt I α (γ t))
  ring

/-! ### Differentiability of `speedSqChart` at chart-α-domain points -/

private lemma chartCoord_vCoord_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t := by
  classical
  have hv_da := hasDerivAt_vCoord (I := I) g α hproj hpath hbase
  have hv_diff : DifferentiableAt ℝ (vCoord (I := I) α f) t :=
    hv_da.differentiableAt
  set L : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hL_diff : DifferentiableAt ℝ L (vCoord (I := I) α f t) := L.differentiableAt
  have hcomp : DifferentiableAt ℝ (fun s => L (vCoord (I := I) α f s)) t :=
    hL_diff.comp t hv_diff
  have hfun : (fun s => L (vCoord (I := I) α f s)) =
      (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) := by
    funext s; rfl
  rw [hfun] at hcomp
  exact hcomp

private lemma chartGramOnE_yCoord_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) t := by
  classical
  have hy_da := hasDerivAt_yCoord (I := I) g α hproj hpath hbase
  have hy_diff : DifferentiableAt ℝ (yCoord (I := I) α γ) t := hy_da.differentiableAt
  have hxsrc : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hbase
  have htgt : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hint : extChartAt I α (γ t) ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α htgt
  have hG_cdo : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  have hG_cda : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (γ t)) :=
    hG_cdo.contDiffAt (isOpen_interior.mem_nhds hint)
  have hG_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (γ t)) :=
    hG_cda.differentiableAt (by simp)
  have : DifferentiableAt ℝ
      (chartGramOnE (I := I) g α i j ∘ yCoord (I := I) α γ) t :=
    hG_diff.comp t hy_diff
  exact this

private lemma speedSqChart_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (speedSqChart (I := I) g α γ f) t := by
  classical
  unfold speedSqChart
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  refine DifferentiableAt.fun_sum (fun j _ => ?_)
  exact ((chartGramOnE_yCoord_differentiableAt (I := I) g α hproj hpath hbase i j).mul
    (chartCoord_vCoord_differentiableAt (I := I) g α hproj hpath hbase i)).mul
    (chartCoord_vCoord_differentiableAt (I := I) g α hproj hpath hbase j)

/-! ### Derivative computations on the chart-α domain -/

private lemma deriv_chartCoord_vCoord
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    deriv (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t =
      chartCoord (E := E) i
        (- chartChristoffelContraction (I := I) g α
          (vCoord (I := I) α f t) (vCoord (I := I) α f t)
          (yCoord (I := I) α γ t)) := by
  classical
  have hv_da := hasDerivAt_vCoord (I := I) g α hproj hpath hbase
  set L : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hL_HD : HasDerivAt (fun s => L (vCoord (I := I) α f s))
      (L (- chartChristoffelContraction (I := I) g α
        (vCoord (I := I) α f t) (vCoord (I := I) α f t)
        (yCoord (I := I) α γ t))) t :=
    L.hasFDerivAt.comp_hasDerivAt t hv_da
  have hfun : (fun s => L (vCoord (I := I) α f s)) =
      (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) := by
    funext s; rfl
  rw [hfun] at hL_HD
  exact hL_HD.deriv

private lemma deriv_chartGramOnE_yCoord
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    deriv (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) t =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (vCoord (I := I) α f t) *
          partialDeriv (E := E) k
            (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t) := by
  classical
  have hy_da := hasDerivAt_yCoord (I := I) g α hproj hpath hbase
  have hxsrc : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hbase
  have htgt : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hint : extChartAt I α (γ t) ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α htgt
  have hG_cdo : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  have hG_cda : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j)
      (yCoord (I := I) α γ t) :=
    hG_cdo.contDiffAt (isOpen_interior.mem_nhds hint)
  have hG_fd : HasFDerivAt (chartGramOnE (I := I) g α i j)
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t))
      (yCoord (I := I) α γ t) :=
    (hG_cda.differentiableAt (by simp)).hasFDerivAt
  have hcomp_fd : HasDerivAt
      (chartGramOnE (I := I) g α i j ∘ yCoord (I := I) α γ)
      ((fderiv ℝ (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t))
        (vCoord (I := I) α f t)) t :=
    hG_fd.comp_hasDerivAt t hy_da
  have hfun : (chartGramOnE (I := I) g α i j) ∘ yCoord (I := I) α γ =
      (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) := rfl
  rw [hfun] at hcomp_fd
  have hderiv_eq : deriv (fun s => chartGramOnE (I := I) g α i j
      (yCoord (I := I) α γ s)) t =
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t))
        (vCoord (I := I) α f t) := hcomp_fd.deriv
  rw [hderiv_eq]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  set v : E := vCoord (I := I) α f t with hv_def
  have hv_decomp : v = ∑ k, b.repr v k • b k := (Module.Basis.sum_repr b v).symm
  set L : E →L[ℝ] ℝ := fderiv ℝ (chartGramOnE (I := I) g α i j)
    (yCoord (I := I) α γ t)
  have hLv : L v = L (∑ k, b.repr v k • b k) := by rw [← hv_decomp]
  rw [hLv]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, smul_eq_mul]
  change ((chartModelBasis E).repr v) k *
      fderiv ℝ (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t)
        ((chartModelBasis E) k) =
    chartCoord (E := E) k v * partialDeriv (E := E) k
      (chartGramOnE (I := I) g α i j) (yCoord (I := I) α γ t)
  rfl

/-- Helper: triple-product derivative formula. -/
private lemma deriv_triple_product (f g h : ℝ → ℝ) {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t)
    (hh : DifferentiableAt ℝ h t) :
    deriv (fun s => f s * g s * h s) t =
      deriv f t * g t * h t + f t * deriv g t * h t + f t * g t * deriv h t := by
  classical
  have hfg : DifferentiableAt ℝ (fun s => f s * g s) t := hf.mul hg
  rw [deriv_fun_mul hfg hh, deriv_fun_mul hf hg]
  ring

/-- **Derivative of `speedSqChart` is zero on the chart-α domain.**
This is the load-bearing 4-index cancellation. -/
private lemma deriv_speedSqChart_eq_zero
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    deriv (speedSqChart (I := I) g α γ f) t = 0 := by
  classical
  set n := Module.finrank ℝ E
  set y : E := yCoord (I := I) α γ t with hy_def
  set v : E := vCoord (I := I) α f t with hv_def
  -- Differentiability of factors.
  have hvi_diff : ∀ i : Fin n,
      DifferentiableAt ℝ (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t :=
    fun i => chartCoord_vCoord_differentiableAt (I := I) g α hproj hpath hbase i
  have hGij_diff : ∀ i j : Fin n,
      DifferentiableAt ℝ (fun s => chartGramOnE (I := I) g α i j
        (yCoord (I := I) α γ s)) t :=
    fun i j => chartGramOnE_yCoord_differentiableAt (I := I) g α hproj hpath hbase i j
  have hijsum_diff : ∀ i j : Fin n,
      DifferentiableAt ℝ
        (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s) *
          chartCoord (E := E) i (vCoord (I := I) α f s) *
          chartCoord (E := E) j (vCoord (I := I) α f s)) t := fun i j =>
    ((hGij_diff i j).mul (hvi_diff i)).mul (hvi_diff j)
  have hjsum_diff : ∀ i : Fin n,
      DifferentiableAt ℝ
        (fun s => ∑ j : Fin n,
          chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s) *
            chartCoord (E := E) i (vCoord (I := I) α f s) *
            chartCoord (E := E) j (vCoord (I := I) α f s)) t := fun i =>
    DifferentiableAt.fun_sum (fun j _ => hijsum_diff i j)
  unfold speedSqChart
  rw [deriv_fun_sum (fun i _ => hjsum_diff i)]
  -- Convert each inner derivative.
  have hcompute : (∑ i : Fin n,
      deriv (fun s => ∑ j : Fin n,
        chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s) *
          chartCoord (E := E) i (vCoord (I := I) α f s) *
          chartCoord (E := E) j (vCoord (I := I) α f s)) t) =
    ∑ i : Fin n, ∑ j : Fin n,
      (deriv (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) t *
        chartCoord (E := E) i (vCoord (I := I) α f t) *
        chartCoord (E := E) j (vCoord (I := I) α f t) +
      chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
        deriv (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t *
        chartCoord (E := E) j (vCoord (I := I) α f t) +
      chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
        chartCoord (E := E) i (vCoord (I := I) α f t) *
        deriv (fun s => chartCoord (E := E) j (vCoord (I := I) α f s)) t) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [deriv_fun_sum (fun j _ => hijsum_diff i j)]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact deriv_triple_product
      (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s))
      (fun s => chartCoord (E := E) i (vCoord (I := I) α f s))
      (fun s => chartCoord (E := E) j (vCoord (I := I) α f s))
      (hGij_diff i j) (hvi_diff i) (hvi_diff j)
  rw [hcompute]
  -- Shorthands.
  set vv : Fin n → ℝ := fun i => chartCoord (E := E) i (vCoord (I := I) α f t)
    with hvv_def
  set Gij : Fin n → Fin n → ℝ := fun i j => chartGramOnE (I := I) g α i j y
    with hGij_def
  set Γkil : Fin n → Fin n → Fin n → ℝ := fun k i l =>
    chartChristoffel (I := I) g α k i l y with hΓ_def
  -- Identify each deriv.
  have hdv_eq : ∀ i : Fin n,
      deriv (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t =
        - ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b := by
    intro i
    rw [deriv_chartCoord_vCoord (I := I) g α hproj hpath hbase i]
    have hneg : chartCoord (E := E) i
        (- chartChristoffelContraction (I := I) g α v v y) =
        - chartCoord (E := E) i (chartChristoffelContraction (I := I) g α v v y) := by
      change ((chartModelBasis E).repr (- _)) i = - _
      rw [map_neg]; rfl
    rw [hneg]
    have hcontract :
        chartCoord (E := E) i (chartChristoffelContraction (I := I) g α v v y) =
          ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b := by
      unfold chartChristoffelContraction
      have hcoord_basis_sum : ∀ (c : Fin n → ℝ),
          chartCoord (E := E) i (∑ k : Fin n, c k • (chartModelBasis E k)) = c i := by
        intro c
        change ((chartModelBasis E).repr (∑ k : Fin n, c k • (chartModelBasis E k))) i = c i
        rw [show ((chartModelBasis E).repr (∑ k : Fin n, c k • (chartModelBasis E k))) =
            ∑ k : Fin n, c k • ((chartModelBasis E).repr (chartModelBasis E k)) by
          rw [map_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); rw [map_smul]]
        rw [Finsupp.finset_sum_apply]
        have hsum_eq : ∑ k : Fin n,
            (c k • (chartModelBasis E).repr (chartModelBasis E k)) i =
          ∑ k : Fin n, if k = i then c k else 0 := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [(chartModelBasis E).repr_self, Finsupp.coe_smul, Pi.smul_apply,
            Finsupp.single_apply]
          by_cases hk : k = i
          · subst hk; simp
          · simp [hk]
        rw [hsum_eq, Finset.sum_ite_eq' Finset.univ i (fun k => c k)]
        simp
      rw [hcoord_basis_sum]
    rw [hcontract]
  -- Identify deriv of chartGramOnE.
  have hxsrc : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hbase
  have htgt : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hint : y ∈ interior (extChartAt I α).target := by
    rw [hy_def]
    change extChartAt I α (γ t) ∈ interior (extChartAt I α).target
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α htgt
  have hpd_eq : ∀ i j k : Fin n,
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
        (∑ l : Fin n, Γkil k i l * Gij l j) +
        (∑ l : Fin n, Γkil k j l * Gij l i) :=
    fun i j k => partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k hint
  have hdG_eq : ∀ i j : Fin n,
      deriv (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) t =
        ∑ k : Fin n, vv k *
          ((∑ l : Fin n, Γkil k i l * Gij l j) +
           (∑ l : Fin n, Γkil k j l * Gij l i)) := by
    intro i j
    rw [deriv_chartGramOnE_yCoord (I := I) g α hproj hpath hbase i j]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hpd_eq i j k]
  have hG_at : ∀ i j : Fin n, chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) =
      Gij i j := by intros; rfl
  -- Substitute.
  have hRHS_subst :
      (∑ i : Fin n, ∑ j : Fin n,
          (deriv (fun s => chartGramOnE (I := I) g α i j (yCoord (I := I) α γ s)) t *
            chartCoord (E := E) i (vCoord (I := I) α f t) *
            chartCoord (E := E) j (vCoord (I := I) α f t) +
          chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
            deriv (fun s => chartCoord (E := E) i (vCoord (I := I) α f s)) t *
            chartCoord (E := E) j (vCoord (I := I) α f t) +
          chartGramOnE (I := I) g α i j (yCoord (I := I) α γ t) *
            chartCoord (E := E) i (vCoord (I := I) α f t) *
            deriv (fun s => chartCoord (E := E) j (vCoord (I := I) α f s)) t)) =
      (∑ i : Fin n, ∑ j : Fin n,
          ((∑ k : Fin n, vv k *
              ((∑ l : Fin n, Γkil k i l * Gij l j) +
               (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j +
           Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j +
           Gij i j * vv i *
             (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hdG_eq i j, hG_at i j, hdv_eq i, hdv_eq j]
  rw [hRHS_subst]
  -- Convert each term to a 4-fold sum, then cancel via index swaps + G symmetry.
  -- T1 ("positive A1") = ∑_{i,j,k,l} vv k * Γ^l_{ki} * G_{lj} * vv i * vv j
  -- T2 ("positive A2") = ∑_{i,j,k,l} vv k * Γ^l_{kj} * G_{li} * vv i * vv j
  -- T3 ("negative B") = -∑_{i,j,a,b} G_{ij} * Γ^i_{ab} * vv a * vv b * vv j
  -- T4 ("negative C") = -∑_{i,j,a,b} G_{ij} * vv i * Γ^j_{ab} * vv a * vv b
  -- Goal: T1 + T2 + T3 + T4 = 0.
  -- Reindexings: T3 = -T1 (via (a,b,i,j) ↦ (k,i,l,j)) and T4 = -T2 (via swap + G symmetry).
  set S : Fin n → Fin n → Fin n → Fin n → ℝ := fun i j k l =>
    vv k * Γkil k i l * Gij l j * vv i * vv j with hS_def
  -- Step 1: split the outer expression into four 4-fold sums in canonical form.
  -- Convert A (positive piece).
  have hA_split :
      (∑ i : Fin n, ∑ j : Fin n,
          (∑ k : Fin n, vv k *
              ((∑ l : Fin n, Γkil k i l * Gij l j) +
               (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          vv k * Γkil k i l * Gij l j * vv i * vv j) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          vv k * Γkil k j l * Gij l i * vv i * vv j) := by
    -- First, rewrite LHS as a 4-fold sum of a SUM of two scalars.
    have hLHS_4 :
        (∑ i : Fin n, ∑ j : Fin n,
            (∑ k : Fin n, vv k *
                ((∑ l : Fin n, Γkil k i l * Gij l j) +
                 (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            (vv k * Γkil k i l * Gij l j * vv i * vv j +
             vv k * Γkil k j l * Gij l i * vv i * vv j)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      -- Goal at this point:
      -- vv k * ((∑ l, ...) + (∑ l, ...)) * vv i * vv j = ∑ l, (S₁(k,i,j,l) + S₂(k,i,j,l)).
      calc vv k *
            ((∑ l : Fin n, Γkil k i l * Gij l j) +
             (∑ l : Fin n, Γkil k j l * Gij l i)) * vv i * vv j
          = (∑ l : Fin n, Γkil k i l * Gij l j) * (vv k * vv i * vv j) +
            (∑ l : Fin n, Γkil k j l * Gij l i) * (vv k * vv i * vv j) := by ring
        _ = (∑ l : Fin n, Γkil k i l * Gij l j * (vv k * vv i * vv j)) +
            (∑ l : Fin n, Γkil k j l * Gij l i * (vv k * vv i * vv j)) := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ = ∑ l : Fin n,
              (Γkil k i l * Gij l j * (vv k * vv i * vv j) +
               Γkil k j l * Gij l i * (vv k * vv i * vv j)) := by
            rw [← Finset.sum_add_distrib]
        _ = ∑ l : Fin n,
              (vv k * Γkil k i l * Gij l j * vv i * vv j +
               vv k * Γkil k j l * Gij l i * vv i * vv j) := by
            refine Finset.sum_congr rfl (fun l _ => ?_); ring
    rw [hLHS_4]
    -- Split the inner sum-of-sums.
    rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            (vv k * Γkil k i l * Gij l j * vv i * vv j +
             vv k * Γkil k j l * Gij l i * vv i * vv j)) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            vv k * Γkil k i l * Gij l j * vv i * vv j) +
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            vv k * Γkil k j l * Gij l i * vv i * vv j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib]]
  -- Convert B (negative piece in i, contraction via Γ^i_{ab}).
  have hB_eq :
      (∑ i : Fin n, ∑ j : Fin n,
          Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j) =
      - ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          Gij i j * Γkil a b i * vv a * vv b * vv j := by
    -- Step 1: pull the negation through the outer two sums.
    have hpull :
        (∑ i : Fin n, ∑ j : Fin n,
            Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j) =
        (∑ i : Fin n, ∑ j : Fin n,
            - (Gij i j * (∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hpull]
    -- Step 2: pull negation out of the j-sum, then the i-sum.
    rw [show (∑ i : Fin n, ∑ j : Fin n,
            - (Gij i j * (∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j)) =
        - (∑ i : Fin n, ∑ j : Fin n,
            Gij i j * (∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j) from by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]]
    congr 1
    -- Step 3: expand the inner double sum into a 4-fold sum.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- Convert C (negative piece in j, contraction via Γ^j_{ab}).
  have hC_eq :
      (∑ i : Fin n, ∑ j : Fin n,
          Gij i j * vv i *
            (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b)) =
      - ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          Gij i j * vv i * Γkil a b j * vv a * vv b := by
    have hpull :
        (∑ i : Fin n, ∑ j : Fin n,
            Gij i j * vv i *
              (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b)) =
        (∑ i : Fin n, ∑ j : Fin n,
            - (Gij i j * vv i *
              (∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hpull]
    rw [show (∑ i : Fin n, ∑ j : Fin n,
            - (Gij i j * vv i *
              (∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) =
        - (∑ i : Fin n, ∑ j : Fin n,
            Gij i j * vv i *
              (∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b)) from by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- Step 2: split the entire LHS expression into A + B + C, then apply hA_split, hB_eq, hC_eq.
  -- We use the structural identity: ∑_{i,j} (a + b + c) = (∑ a) + (∑ b) + (∑ c).
  have hLHS_eq :
      (∑ i : Fin n, ∑ j : Fin n,
          ((∑ k : Fin n, vv k *
              ((∑ l : Fin n, Γkil k i l * Gij l j) +
               (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j +
           Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j +
           Gij i j * vv i *
             (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) =
      ((∑ i : Fin n, ∑ j : Fin n,
          (∑ k : Fin n, vv k *
              ((∑ l : Fin n, Γkil k i l * Gij l j) +
               (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j) +
       (∑ i : Fin n, ∑ j : Fin n,
          Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j) +
       (∑ i : Fin n, ∑ j : Fin n,
          Gij i j * vv i *
            (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) := by
    -- Split outer i-sum first.
    rw [show (∑ i : Fin n, ∑ j : Fin n,
            ((∑ k : Fin n, vv k *
                ((∑ l : Fin n, Γkil k i l * Gij l j) +
                 (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j +
             Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j +
             Gij i j * vv i *
               (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b))) =
        (∑ i : Fin n,
          ((∑ j : Fin n,
              (∑ k : Fin n, vv k *
                  ((∑ l : Fin n, Γkil k i l * Gij l j) +
                   (∑ l : Fin n, Γkil k j l * Gij l i))) * vv i * vv j) +
           (∑ j : Fin n,
              Gij i j * (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b i * vv a * vv b) * vv j) +
           (∑ j : Fin n,
              Gij i j * vv i *
                (- ∑ a : Fin n, ∑ b : Fin n, Γkil a b j * vv a * vv b)))) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hLHS_eq, hA_split, hB_eq, hC_eq]
  -- Step 3: reindexing identities for cancellation. T3 = -T1 via rename
  -- (i, j, a, b) → (l, j, k, i) and a 5-step `Finset.sum_comm` permutation.
  have hT3_eq_T1 :
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          Gij i j * Γkil a b i * vv a * vv b * vv j) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          vv k * Γkil k i l * Gij l j * vv i * vv j) := by
    -- Alpha-rename `∑ i ∑ j ∑ a ∑ b f(i,j,a,b)` to `∑ l ∑ j ∑ k ∑ i f(l,j,k,i)` (rfl).
    have hren : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            Gij i j * Γkil a b i * vv a * vv b * vv j) =
        (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) := rfl
    rw [hren]
    -- Reorder ∑ l ∑ j ∑ k ∑ i to ∑ i ∑ j ∑ k ∑ l via 5 `Finset.sum_comm` swaps.
    have hstep1 :
        (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) =
        (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Finset.sum_comm
    have hstep2 :
        (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) =
        (∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact Finset.sum_comm
    have hstep3 :
        (∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) =
        (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) :=
      Finset.sum_comm
    have hstep4 :
        (∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact Finset.sum_comm
    have hstep5 :
        (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ k : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            Gij l j * Γkil k i l * vv k * vv i * vv j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Finset.sum_comm
    rw [hstep1, hstep2, hstep3, hstep4, hstep5]
    -- Now both are ∑_{i,j,k,l} of two scalars that match by ring.
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  -- T4 reindex: ∑_{i,j,a,b} G_{ij} vi Γ^j_{ab} va vb = ∑_{i,j,k,l} vv k * Γ^l_{kj} * G_{li} * vv i * vv j
  -- (= T2). Use G-symmetry to convert G_il to G_li after renaming b→l, a→k, j→l, i→i.
  have hT4_eq_T2 :
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          Gij i j * vv i * Γkil a b j * vv a * vv b) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          vv k * Γkil k j l * Gij l i * vv i * vv j) := by
    -- Rename (i, j, a, b) → (i', l, k, j) (so old j → l, old a → k, old b → j).
    -- The Lean expression `∑ i ∑ j ∑ a ∑ b f` is alpha-equivalent to `∑ i' ∑ l ∑ k ∑ j' f(i', l, k, j')`.
    -- Then reorder.
    have hren : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            Gij i j * vv i * Γkil a b j * vv a * vv b) =
        (∑ i : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) := rfl
    rw [hren]
    -- Now reorder ∑ i ∑ l ∑ k ∑ j to ∑ i ∑ j ∑ k ∑ l. Use G symmetry on Gij i l → Gij l i.
    -- Steps: ∑ l ∑ k ∑ j (within each i) → ∑ j ∑ k ∑ l (a 3-permutation).
    -- Step 1: ∑ l ∑ k = ∑ k ∑ l (within (i, ∑ j inner)).
    --   ∑ l ∑ k ∑ j = ∑ k ∑ l ∑ j (Finset.sum_comm on outer l, k with f l k = ∑ j ...).
    -- Step 2: ∑ k ∑ l ∑ j = ∑ k ∑ j ∑ l (swap inner l, j).
    -- Step 3: ∑ k ∑ j ∑ l = ∑ j ∑ k ∑ l (swap outer k, j).
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : (∑ l : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) =
        (∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) := by
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun l k => ∑ j : Fin n, Gij i l * vv i * Γkil k j l * vv k * vv j)]
    have h2 : (∑ k : Fin n, ∑ l : Fin n, ∑ j : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) =
        (∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact Finset.sum_comm
    have h3 : (∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) =
        (∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            Gij i l * vv i * Γkil k j l * vv k * vv j) :=
      Finset.sum_comm
    rw [h1, h2, h3]
    -- Now align scalars via G symmetry.
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hGsymm : Gij i l = Gij l i := by
      change chartGramOnE (I := I) g α i l y = chartGramOnE (I := I) g α l i y
      exact chartGramOnE_symm (I := I) g α i l y
    rw [hGsymm]
    ring
  -- Step 4: Final cancellation.
  rw [hT3_eq_T1, hT4_eq_T2]
  -- Goal: T1 + T2 + (-T1) + (-T2) = 0.
  ring

end ChartAlpha

/-! ## Gluing to a constant function on ℝ

We assemble the pieces. The chart-α-relative squared speed `speedSqChart`
has derivative zero on the open chart-α domain `S = γ⁻¹((chartAt H α).source)`,
and agrees with `speedSq` there. Outside `S`, the intrinsic `speedSq` is
zero by the off-chart-source vanishing argument. By continuity of
`speedSq` (a consequence of `C²` smoothness of `γ`), `speedSq` is
constant on ℝ. -/

section Gluing

variable [I.Boundaryless] [CompleteSpace E]

/-- **Continuity of `speedSq` for a `C²` curve.** -/
private lemma speedSq_continuous {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    Continuous (speedSq (I := I) g γ) := by
  classical
  refine continuous_iff_continuousAt.mpr ?_
  intro t
  -- At t, locally `speedSq = chart-sum` by `g_inner_eq_chart_sum_along_eventually`
  -- (with V = W = velocity γ).
  have hVel := velocityLift_contMDiff_of_contMDiff_two (I := I) hγ_smooth
  have hev_inner := g_inner_eq_chart_sum_along_eventually (I := I) g γ
    (contMDiff_one_of_contMDiff_two (I := I) hγ_smooth)
    (velocity (I := I) γ) (velocity (I := I) γ) t
  refine ContinuousAt.congr ?_ hev_inner.symm
  have hcfa_cont : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousAt (chartFiberCoordAlong (I := I) γ (velocity (I := I) γ) t i) t :=
    fun i => (chartFiberCoordAlong_differentiableAt (I := I) γ
      (velocity (I := I) γ) hVel t i).continuousAt
  have hcG_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (chartGramAlong (I := I) g γ t i j) t :=
    fun i j => (chartGramAlong_differentiableAt (I := I) g γ
      (contMDiff_one_of_contMDiff_two (I := I) hγ_smooth) t i j).continuousAt
  -- Continuity of the double sum at t: induct on the Finset of indices via tendsto_finset_sum.
  have hsummand : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun s => chartFiberCoordAlong (I := I) γ
            (velocity (I := I) γ) t i s *
          chartFiberCoordAlong (I := I) γ (velocity (I := I) γ) t j s *
          chartGramAlong (I := I) g γ t i j s) t :=
    fun i j => ((hcfa_cont i).mul (hcfa_cont j)).mul (hcG_cont i j)
  have hjcont : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousAt (fun s => ∑ j : Fin (Module.finrank ℝ E),
          chartFiberCoordAlong (I := I) γ (velocity (I := I) γ) t i s *
          chartFiberCoordAlong (I := I) γ (velocity (I := I) γ) t j s *
          chartGramAlong (I := I) g γ t i j s) t := by
    intro i
    -- `ContinuousAt f t = Tendsto f (𝓝 t) (𝓝 (f t))`.
    -- The function is `fun s => ∑ j, summand_ij s`.
    -- At s = t, the value is `∑ j, summand_ij t`. By tendsto_finset_sum:
    exact tendsto_finset_sum _ (fun j _ => hsummand i j)
  exact tendsto_finset_sum _ (fun i _ => hjcont i)

/-- **Differentiability of `speedSq` at chart-α-domain points.** -/
private lemma speedSq_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {t : ℝ} (hbase : γ t ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (speedSq (I := I) g γ) t := by
  classical
  -- On a neighborhood of t, speedSq = speedSqChart, which is differentiable.
  have hγ_cont : Continuous γ := hγ_smooth.continuous
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hev_chart : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H α).source :=
    hγ_cont.continuousAt.preimage_mem_nhds (hop.mem_nhds hbase)
  have hev_eq : (speedSq (I := I) g γ) =ᶠ[𝓝 t] (speedSqChart (I := I) g α γ f) := by
    filter_upwards [hev_chart] with s hs
    exact (speedSqChart_eq_speedSq (I := I) g α hproj
      (hpath.isMIntegralCurveAt s) hs).symm
  have hssq_chart_diff : DifferentiableAt ℝ (speedSqChart (I := I) g α γ f) t :=
    speedSqChart_differentiableAt (I := I) g α hproj
      (hpath.isMIntegralCurveAt t) hbase
  exact hssq_chart_diff.congr_of_eventuallyEq hev_eq

/-- **Derivative of `speedSq` is zero on the chart-α domain.** -/
private lemma deriv_speedSq_eq_zero_on_chartAlpha
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {t : ℝ} (hbase : γ t ∈ (chartAt H α).source) :
    deriv (speedSq (I := I) g γ) t = 0 := by
  classical
  have hγ_cont : Continuous γ := hγ_smooth.continuous
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hev_chart : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H α).source :=
    hγ_cont.continuousAt.preimage_mem_nhds (hop.mem_nhds hbase)
  have hev_eq : (speedSq (I := I) g γ) =ᶠ[𝓝 t] (speedSqChart (I := I) g α γ f) := by
    filter_upwards [hev_chart] with s hs
    exact (speedSqChart_eq_speedSq (I := I) g α hproj
      (hpath.isMIntegralCurveAt s) hs).symm
  have hderiv_eq := Filter.EventuallyEq.deriv_eq hev_eq
  rw [hderiv_eq]
  exact deriv_speedSqChart_eq_zero (I := I) g α hproj
    (hpath.isMIntegralCurveAt t) hbase

-- The chart-α "in chart" set as a subset of ℝ: simply
-- `γ ⁻¹' (chartAt H α).source`. We don't introduce a named abbreviation.

/-- **Speed-zero off-chart helper.** When `t ∈ Sᶜ`, the speedSq vanishes
at `t` (just unpacking the off-chart vanishing). -/
private lemma speedSq_eq_zero_of_notMem_chartAlphaSet
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    {t : ℝ} (ht : t ∉ γ ⁻¹' (chartAt H α).source) :
    speedSq (I := I) g γ t = 0 := by
  classical
  have ht_not : γ t ∉ (chartAt H α).source := ht
  exact speedSq_eq_zero_of_proj_notMem (I := I) hproj
    (hpath.isMIntegralCurveAt t) ht_not

/-- **Right-half preconnected interval lemma**: if `t₀ ∈ S`, `c ∉ S` with `t₀ < c`,
then `speedSq t₀ = 0`. -/
private lemma speedSq_eq_zero_of_left_of_off_chart
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {t₀ c : ℝ}
    (h0 : t₀ ∈ γ ⁻¹' (chartAt H α).source)
    (hc : c ∉ γ ⁻¹' (chartAt H α).source)
    (hlt : t₀ < c) :
    speedSq (I := I) g γ t₀ = 0 := by
  classical
  set S : Set ℝ := γ ⁻¹' (chartAt H α).source
  have hγ_cont : Continuous γ := hγ_smooth.continuous
  have hS_open : IsOpen S := hγ_cont.isOpen_preimage _ (chartAt H α).open_source
  have hSc_closed : IsClosed (Sᶜ : Set ℝ) := hS_open.isClosed_compl
  -- Let K = Sᶜ ∩ Icc t₀ c. K is closed (intersection of closed sets) and nonempty (c ∈ K).
  set K : Set ℝ := (Sᶜ : Set ℝ) ∩ Icc t₀ c
  have hK_closed : IsClosed K := hSc_closed.inter isClosed_Icc
  have hK_nonempty : K.Nonempty := ⟨c, hc, le_of_lt hlt, le_refl _⟩
  have hK_bdd : BddBelow K := ⟨t₀, fun x hx => hx.2.1⟩
  set c' : ℝ := sInf K
  have hc'_mem : c' ∈ K := hK_closed.csInf_mem hK_nonempty hK_bdd
  have hc'_not_in_S : c' ∈ (Sᶜ : Set ℝ) := hc'_mem.1
  have hc'_in_Icc : c' ∈ Icc t₀ c := hc'_mem.2
  have hc'_ge_t₀ : t₀ ≤ c' := hc'_in_Icc.1
  have hc'_le_c : c' ≤ c := hc'_in_Icc.2
  -- t₀ ≠ c' since t₀ ∈ S but c' ∉ S.
  have hc'_ne_t₀ : c' ≠ t₀ := by
    intro heq
    apply hc'_not_in_S
    rw [heq]; exact h0
  have hc'_gt_t₀ : t₀ < c' := lt_of_le_of_ne hc'_ge_t₀ (Ne.symm hc'_ne_t₀)
  -- For s ∈ Ico t₀ c', s ∈ S: since s ∉ K (s < c' = inf K), and s ∈ Icc t₀ c,
  -- so s ∉ Sᶜ, i.e., s ∈ S.
  have hIco_subset_S : ∀ s ∈ Ico t₀ c', s ∈ S := by
    intro s hs
    have hs1 : t₀ ≤ s := hs.1
    have hs2 : s < c' := hs.2
    have hs_in_Icc : s ∈ Icc t₀ c :=
      ⟨hs1, le_trans (le_of_lt hs2) hc'_le_c⟩
    -- Suppose s ∈ Sᶜ. Then s ∈ K, so c' = sInf K ≤ s. Contradiction with s < c'.
    by_contra hs_not
    have hs_in_K : s ∈ K := ⟨hs_not, hs_in_Icc⟩
    have hc'_le_s : c' ≤ s := csInf_le hK_bdd hs_in_K
    exact not_le.mpr hs2 hc'_le_s
  -- For x ∈ Ico t₀ c', speedSq has zero right-derivative.
  -- HasDerivWithinAt G 0 (Ici x) x — derived from HasDerivAt G 0 x via inclusion.
  have hderiv_right : ∀ x ∈ Ico t₀ c',
      HasDerivWithinAt (speedSq (I := I) g γ) 0 (Ici x) x := by
    intro x hx
    have hx_in_S : x ∈ S := hIco_subset_S x hx
    have hbase : γ x ∈ (chartAt H α).source := hx_in_S
    -- HasDerivAt from differentiability + zero deriv.
    have hdiff := speedSq_differentiableAt (I := I) g α hproj hpath hγ_smooth hbase
    have hderiv_zero := deriv_speedSq_eq_zero_on_chartAlpha (I := I) g α
      hproj hpath hγ_smooth hbase
    have hHD : HasDerivAt (speedSq (I := I) g γ) 0 x := by
      rw [← hderiv_zero]
      exact hdiff.hasDerivAt
    exact hHD.hasDerivWithinAt
  -- Apply `constant_of_has_deriv_right_zero` on Icc t₀ c'.
  have hcont : ContinuousOn (speedSq (I := I) g γ) (Icc t₀ c') :=
    (speedSq_continuous (I := I) hγ_smooth).continuousOn
  have hconst := constant_of_has_deriv_right_zero hcont hderiv_right
  -- Goal: speedSq t₀ = 0. Specialize at x = c': speedSq c' = speedSq t₀.
  have hc'_eq : speedSq (I := I) g γ c' = speedSq (I := I) g γ t₀ :=
    hconst c' ⟨hc'_ge_t₀, le_refl _⟩
  -- And speedSq c' = 0 since c' ∉ S.
  have hc'_zero : speedSq (I := I) g γ c' = 0 :=
    speedSq_eq_zero_of_notMem_chartAlphaSet (I := I) hproj hpath hc'_not_in_S
  linarith [hc'_eq, hc'_zero]

/-- **Left-half preconnected interval lemma**: if `t₀ ∈ S`, `c ∉ S` with `c < t₀`,
then `speedSq t₀ = 0`. (Symmetric of the previous lemma.) -/
private lemma speedSq_eq_zero_of_right_of_off_chart
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {t₀ c : ℝ}
    (h0 : t₀ ∈ γ ⁻¹' (chartAt H α).source)
    (hc : c ∉ γ ⁻¹' (chartAt H α).source)
    (hlt : c < t₀) :
    speedSq (I := I) g γ t₀ = 0 := by
  classical
  -- Symmetric argument: take the sup of K = Sᶜ ∩ Icc c t₀.
  set S : Set ℝ := γ ⁻¹' (chartAt H α).source
  have hγ_cont : Continuous γ := hγ_smooth.continuous
  have hS_open : IsOpen S := hγ_cont.isOpen_preimage _ (chartAt H α).open_source
  have hSc_closed : IsClosed (Sᶜ : Set ℝ) := hS_open.isClosed_compl
  set K : Set ℝ := (Sᶜ : Set ℝ) ∩ Icc c t₀
  have hK_closed : IsClosed K := hSc_closed.inter isClosed_Icc
  have hK_nonempty : K.Nonempty := ⟨c, hc, le_refl _, le_of_lt hlt⟩
  have hK_bdd : BddAbove K := ⟨t₀, fun x hx => hx.2.2⟩
  set c' : ℝ := sSup K
  have hc'_mem : c' ∈ K := hK_closed.csSup_mem hK_nonempty hK_bdd
  have hc'_not_in_S : c' ∈ (Sᶜ : Set ℝ) := hc'_mem.1
  have hc'_in_Icc : c' ∈ Icc c t₀ := hc'_mem.2
  have hc'_ge_c : c ≤ c' := hc'_in_Icc.1
  have hc'_le_t₀ : c' ≤ t₀ := hc'_in_Icc.2
  have hc'_ne_t₀ : c' ≠ t₀ := by
    intro heq
    apply hc'_not_in_S
    rw [heq]; exact h0
  have hc'_lt_t₀ : c' < t₀ := lt_of_le_of_ne hc'_le_t₀ hc'_ne_t₀
  -- For s ∈ Ioc c' t₀, s ∈ S.
  have hIoc_subset_S : ∀ s ∈ Ioc c' t₀, s ∈ S := by
    intro s hs
    have hs1 : c' < s := hs.1
    have hs2 : s ≤ t₀ := hs.2
    have hs_in_Icc : s ∈ Icc c t₀ :=
      ⟨le_trans hc'_ge_c (le_of_lt hs1), hs2⟩
    by_contra hs_not
    have hs_in_K : s ∈ K := ⟨hs_not, hs_in_Icc⟩
    have hs_le_c' : s ≤ c' := le_csSup hK_bdd hs_in_K
    exact not_lt.mpr hs_le_c' hs1
  -- Strategy: show ∀ x ∈ Ioc c' t₀, speedSq x = speedSq t₀, then take continuity from the right.
  -- Strategy: ∀ x ∈ Ioc c' t₀, speedSq x = speedSq t₀ (via constant_of_has_deriv_right_zero on Icc x t₀).
  -- Then take continuity at c' from the right: speedSq c' = lim_{x↓c'} speedSq x = speedSq t₀.
  -- Since speedSq c' = 0, conclude speedSq t₀ = 0.
  have hconst_on_Ioc : ∀ x ∈ Ioc c' t₀,
      speedSq (I := I) g γ x = speedSq (I := I) g γ t₀ := by
    intro x hx
    have hx1 : c' < x := hx.1
    have hx2 : x ≤ t₀ := hx.2
    -- All y ∈ Ico x t₀ are in Ioc c' t₀ ⊂ S, so HasDerivAt 0.
    have hderiv_right : ∀ y ∈ Ico x t₀,
        HasDerivWithinAt (speedSq (I := I) g γ) 0 (Ici y) y := by
      intro y hy
      have hy1 : x ≤ y := hy.1
      have hy2 : y < t₀ := hy.2
      have hy_gt_c' : c' < y := lt_of_lt_of_le hx1 hy1
      have hy_in_Ioc : y ∈ Ioc c' t₀ := ⟨hy_gt_c', le_of_lt hy2⟩
      have hy_in_S : y ∈ S := hIoc_subset_S y hy_in_Ioc
      have hbase : γ y ∈ (chartAt H α).source := hy_in_S
      have hdiff := speedSq_differentiableAt (I := I) g α hproj hpath hγ_smooth hbase
      have hderiv_zero := deriv_speedSq_eq_zero_on_chartAlpha (I := I) g α
        hproj hpath hγ_smooth hbase
      have hHD : HasDerivAt (speedSq (I := I) g γ) 0 y := by
        rw [← hderiv_zero]
        exact hdiff.hasDerivAt
      exact hHD.hasDerivWithinAt
    have hcont : ContinuousOn (speedSq (I := I) g γ) (Icc x t₀) :=
      (speedSq_continuous (I := I) hγ_smooth).continuousOn
    have hconst := constant_of_has_deriv_right_zero hcont hderiv_right
    -- hconst : ∀ z ∈ Icc x t₀, speedSq z = speedSq x. Apply at z = t₀.
    have ht₀_eq : speedSq (I := I) g γ t₀ = speedSq (I := I) g γ x :=
      hconst t₀ ⟨hx2, le_refl _⟩
    exact ht₀_eq.symm
  -- Continuity at c' from the right (within (c', t₀]).
  have hcont_c' : ContinuousAt (speedSq (I := I) g γ) c' :=
    (speedSq_continuous (I := I) hγ_smooth).continuousAt
  -- Tendsto speedSq (𝓝[Ioc c' t₀] c') (𝓝 (speedSq c')).
  have hcont_within : Filter.Tendsto (speedSq (I := I) g γ) (𝓝[Set.Ioc c' t₀] c')
      (𝓝 (speedSq (I := I) g γ c')) :=
    hcont_c'.tendsto.mono_left nhdsWithin_le_nhds
  -- Eventually equality: ∀ᶠ t in 𝓝[Ioc c' t₀] c', speedSq t = speedSq t₀.
  have hev_const : (speedSq (I := I) g γ) =ᶠ[𝓝[Set.Ioc c' t₀] c']
      (fun _ => speedSq (I := I) g γ t₀) := by
    refine eventually_nhdsWithin_iff.mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact hconst_on_Ioc x hx
  -- The same Tendsto with target speedSq t₀.
  have hlim_eq : Filter.Tendsto (speedSq (I := I) g γ) (𝓝[Set.Ioc c' t₀] c')
      (𝓝 (speedSq (I := I) g γ t₀)) := by
    refine (Filter.Tendsto.congr' hev_const.symm ?_)
    exact tendsto_const_nhds
  -- The filter is nontrivial: c' is in closure of (c', t₀] since c' < t₀.
  have hne : (𝓝[Set.Ioc c' t₀] c').NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioc hc'_lt_t₀.ne]
    exact ⟨le_refl _, hc'_le_t₀⟩
  have hlimit_unique : speedSq (I := I) g γ c' = speedSq (I := I) g γ t₀ :=
    tendsto_nhds_unique hcont_within hlim_eq
  have hc'_zero : speedSq (I := I) g γ c' = 0 :=
    speedSq_eq_zero_of_notMem_chartAlphaSet (I := I) hproj hpath hc'_not_in_S
  linarith [hlimit_unique, hc'_zero]

/-- **`speedSq` is zero at any chart-α-domain point when Sᶜ is non-empty.**
This combines the left-half and right-half cases. -/
private lemma speedSq_eq_zero_of_witness_chart_in_with_off_chart_witness
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {t₀ c : ℝ}
    (h0 : t₀ ∈ γ ⁻¹' (chartAt H α).source)
    (hc : c ∉ γ ⁻¹' (chartAt H α).source) :
    speedSq (I := I) g γ t₀ = 0 := by
  rcases lt_trichotomy t₀ c with hlt | heq | hgt
  · exact speedSq_eq_zero_of_left_of_off_chart (I := I) g α
      hproj hpath hγ_smooth h0 hc hlt
  · -- t₀ = c. But t₀ ∈ S and c ∉ S, so t₀ ≠ c. Contradiction.
    exact absurd (heq ▸ h0) hc
  · exact speedSq_eq_zero_of_right_of_off_chart (I := I) g α
      hproj hpath hγ_smooth h0 hc hgt

/-- **Main gluing**: for a global geodesic `γ` (witnessed by chart
basepoint `α` and lift `f`) that is `C²`, the squared speed agrees at
any two times. -/
private theorem speedSq_eq_of_isGeodesic_witness
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    {α : M} {f : ℝ → TangentBundle I M}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurve f (geodesicVectorFieldChart (I := I) g α))
    (t₀ t₁ : ℝ) :
    speedSq (I := I) g γ t₀ = speedSq (I := I) g γ t₁ := by
  classical
  set S : Set ℝ := γ ⁻¹' (chartAt H α).source
  have hγ_cont : Continuous γ := hγ_smooth.continuous
  have hS_open : IsOpen S := hγ_cont.isOpen_preimage _ (chartAt H α).open_source
  by_cases hSall : S = Set.univ
  · -- S = ℝ: apply IsOpen.is_const_of_deriv_eq_zero on ℝ.
    have hS_preconn : IsPreconnected S := by
      rw [hSall]; exact isPreconnected_univ
    have hF_diff : DifferentiableOn ℝ (speedSq (I := I) g γ) S := by
      intro t ht
      have hbase : γ t ∈ (chartAt H α).source := ht
      exact (speedSq_differentiableAt (I := I) g α hproj hpath hγ_smooth hbase).differentiableWithinAt
    have hF_deriv : S.EqOn (deriv (speedSq (I := I) g γ)) 0 := by
      intro t ht
      have hbase : γ t ∈ (chartAt H α).source := ht
      change deriv (speedSq (I := I) g γ) t = 0
      exact deriv_speedSq_eq_zero_on_chartAlpha (I := I) g α
        hproj hpath hγ_smooth hbase
    have ht₀_in_S : t₀ ∈ S := by rw [hSall]; trivial
    have ht₁_in_S : t₁ ∈ S := by rw [hSall]; trivial
    exact hS_open.is_const_of_deriv_eq_zero hS_preconn hF_diff hF_deriv ht₀_in_S ht₁_in_S
  · -- Sᶜ ≠ ∅. Pick c ∈ Sᶜ.
    have hSc_nonempty : (Sᶜ : Set ℝ).Nonempty := by
      rw [Set.nonempty_compl]; exact hSall
    obtain ⟨c, hc⟩ := hSc_nonempty
    -- Show: speedSq t₀ = 0 and speedSq t₁ = 0.
    have hsq_t : ∀ t : ℝ, speedSq (I := I) g γ t = 0 := by
      intro t
      by_cases ht : t ∈ S
      · exact speedSq_eq_zero_of_witness_chart_in_with_off_chart_witness
          (I := I) g α hproj hpath hγ_smooth ht hc
      · exact speedSq_eq_zero_of_notMem_chartAlphaSet
          (I := I) hproj hpath ht
    rw [hsq_t t₀, hsq_t t₁]

end Gluing

/-! ## The headline -/

section Headline

variable [I.Boundaryless] [CompleteSpace E]

/-- **Constant speed of geodesics.** For a `C²` geodesic `γ` on a smooth
Riemannian manifold `(M, g)`, the squared speed is constant in time. -/
theorem IsGeodesic.inner_velocity_const
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 2 γ)
    (hγ : IsGeodesic (I := I) g γ) (t₀ t₁ : ℝ) :
    g.inner (γ t₀) (velocity (I := I) γ t₀) (velocity (I := I) γ t₀) =
    g.inner (γ t₁) (velocity (I := I) γ t₁) (velocity (I := I) γ t₁) := by
  classical
  obtain ⟨α, f, hproj, hpath⟩ := hγ
  exact speedSq_eq_of_isGeodesic_witness (I := I) hγ_smooth hproj hpath t₀ t₁

end Headline

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
