import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart
import DifferentialGeometry.Geometry.Riemannian.Curve.CovDerivAlong
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option linter.unusedSectionVars false

/-!
# Smoothness packaging for the velocity lift along a `C²` curve

For a curve `γ : ℝ → M` with `ContMDiff 𝓘(ℝ, ℝ) I 2 γ`, the intrinsic
velocity lift `t ↦ ⟨γ t, velocity γ t⟩ : TangentBundle I M` is `C¹` as
a manifold map. This is the smoothness hypothesis required by the
chart-local covariant-derivative operator
`covDerivAlong` (see `Geometry/Riemannian/Curve/CovDerivAlong.lean`) on
the velocity vector field along `γ`.

The identification `velocityLift γ t = tangentMap 𝓘(ℝ, ℝ) I γ ⟨t, 1⟩`
expresses the lift as the bundled derivative of `γ` evaluated on the
canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ`. Mathlib's `ContMDiff.contMDiff_tangentMap`
gives `C¹` smoothness of `tangentMap γ` when `γ` is `C²`; the canonical
section is `C^∞` because the tangent bundle of `(ℝ, 𝓘(ℝ, ℝ))` is
trivially `ℝ × ℝ` with all chart transitions equal to the identity.

We provide:

* `velocityLift_contMDiff_of_contMDiff_two` — the `C¹` smoothness of
  the velocity lift along a `C²` curve.
* `velocityLift_smoothness` — convenient alias for use as the second
  smoothness hypothesis of `covDerivAlong`.

## Intrinsic bridge to the covariant-derivative equation

For a `C¹` curve `γ` on a boundaryless smooth manifold modelled on a
complete inner-product space, the geodesic predicate
`IsGeodesicAt g γ t₀` (from
`Geometry/Riemannian/Geodesic/Equation.lean`) should be equivalent to
the vanishing of the covariant derivative of `velocity γ` along `γ` at
`t₀`.

This file ships the **forward direction restricted to a basepoint-aligned
witness**: when `γ` admits a lift `f` that is a local integral curve of
the chart-fixed geodesic vector field at `α := γ t₀`, the covariant
derivative of `velocity γ` along `γ` vanishes at `t₀`. The headline
theorem is `covDerivAlong_velocity_eq_zero_of_basepoint_aligned`.

The general forward direction with an arbitrary chart basepoint `α`,
and either direction of the headline iff, are obstructed; see the
"Status of the headline iff" note at the end of this file.
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

/-! ## Canonical unit-tangent section of `TangentBundle 𝓘(ℝ, ℝ) ℝ` -/

/-- The canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ`. Composed with `tangentMap γ` this expresses
the velocity lift of `γ`. -/
def realUnitTangentSection : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ :=
  fun t => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)

@[simp] lemma realUnitTangentSection_proj (t : ℝ) :
    (realUnitTangentSection t).proj = t := rfl

@[simp] lemma realUnitTangentSection_snd (t : ℝ) :
    (realUnitTangentSection t).2 = (1 : ℝ) := rfl

/-- On `ℝ`, every chart's `extChartAt` is the identity. Pure
unwrapping of the trivial chart structure. -/
private lemma extChartAt_real_apply (p z : ℝ) :
    extChartAt 𝓘(ℝ, ℝ) p z = z := rfl

private lemma extChartAt_real_symm_apply (p z : ℝ) :
    (extChartAt 𝓘(ℝ, ℝ) p).symm z = z := by
  have h : extChartAt 𝓘(ℝ, ℝ) p = PartialEquiv.refl ℝ :=
    extChartAt_model_space_eq_id ℝ p
  rw [h]
  rfl

/-- On `ℝ`, the tangent-bundle coordinate change between any two charts
at any point is the identity (acting on the fibre `ℝ`). -/
private lemma tangentCoordChange_real (x y z : ℝ) (v : ℝ) :
    tangentCoordChange 𝓘(ℝ, ℝ) x y z v = v := by
  classical
  -- `tangentCoordChange x y z = fderivWithin (extChartAt y ∘ (extChartAt x).symm)
  --   (range 𝓘(ℝ, ℝ)) (extChartAt x z)`. On `ℝ` the inner function is
  -- the identity, and `range 𝓘(ℝ, ℝ) = univ`.
  rw [tangentCoordChange_def]
  have hcomp_id : (extChartAt 𝓘(ℝ, ℝ) y ∘ (extChartAt 𝓘(ℝ, ℝ) x).symm) =
      (fun z : ℝ => z) := by
    funext w
    rw [Function.comp_apply, extChartAt_real_symm_apply, extChartAt_real_apply]
  rw [hcomp_id]
  have hrange : range (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ) = Set.univ := by
    rw [ModelWithCorners.range_eq_univ]
  rw [hrange, fderivWithin_univ]
  rw [fderiv_id']
  rfl

/-- The canonical "unit-tangent" section `t ↦ ⟨t, 1⟩` of
`TangentBundle 𝓘(ℝ, ℝ) ℝ` is `C^∞`. -/
theorem realUnitTangentSection_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞ realUnitTangentSection := by
  classical
  -- Apply `Trivialization.contMDiff_iff` at the basepoint `α := 0`.
  set α : ℝ := 0
  set e := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) α with he_def
  -- Source membership for the trivialisation: every base point is on `ℝ`'s chart.
  have hsrc : ∀ t : ℝ, realUnitTangentSection t ∈ e.source := by
    intro t
    rw [Trivialization.mem_source, he_def, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source ℝ t
  refine (e.contMDiff_iff (IM := 𝓘(ℝ, ℝ)) (IB := 𝓘(ℝ, ℝ))
    (n := (∞ : WithTop ℕ∞)) hsrc).mpr ⟨?_, ?_⟩
  · -- Base smoothness: `(realUnitTangentSection t).proj = t`, smooth as `id`.
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (realUnitTangentSection t).proj)
    have hid : (fun t : ℝ => (realUnitTangentSection t).proj) = (fun t : ℝ => t) := rfl
    rw [hid]
    exact contMDiff_id
  · -- Fibre smoothness: the fibre coord under the trivialisation at `α = 0`
    -- is constant (= 1) along the section.
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (e (realUnitTangentSection t)).2)
    have hfibre_const : (fun t : ℝ => (e (realUnitTangentSection t)).2) =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      -- `e ⟨t, 1⟩ .2 = tangentCoordChange t α t 1 = 1` by `tangentCoordChange_real`.
      have h : (e (realUnitTangentSection t)).2 =
          tangentCoordChange 𝓘(ℝ, ℝ) t α t (1 : ℝ) := rfl
      rw [h, tangentCoordChange_real]
    rw [hfibre_const]
    exact contMDiff_const

/-! ## Velocity lift via `tangentMap` -/

/-- The intrinsic velocity lift `t ↦ ⟨γ t, velocity γ t⟩` is exactly the
composition of `tangentMap 𝓘(ℝ, ℝ) I γ` with the canonical unit-tangent
section `t ↦ ⟨t, 1⟩`. -/
lemma velocityLift_eq_tangentMap_comp (γ : ℝ → M) :
    (fun t : ℝ => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) =
      (tangentMap 𝓘(ℝ, ℝ) I γ) ∘ realUnitTangentSection := by
  funext t
  rfl

/-- **The velocity lift is `C¹`.** If `γ : ℝ → M` is `C²`, the
total-space velocity lift `t ↦ ⟨γ t, velocity γ t⟩` is `C¹` as a
manifold map `ℝ → TangentBundle I M`.

This is precisely the smoothness hypothesis required by
`covDerivAlong g γ (velocity γ) …`. -/
theorem velocityLift_contMDiff_of_contMDiff_two
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) := by
  classical
  rw [velocityLift_eq_tangentMap_comp (I := I) γ]
  -- `tangentMap γ` is `C¹` because `γ` is `C²`.
  have htm : ContMDiff 𝓘(ℝ, ℝ).tangent I.tangent 1
      (tangentMap 𝓘(ℝ, ℝ) I γ) := by
    have hle : (1 : WithTop ℕ∞) + 1 ≤ 2 := by
      exact_mod_cast (by decide : (1 : ℕ∞) + 1 ≤ 2)
    exact hγ.contMDiff_tangentMap hle
  -- The canonical section is `C^∞`, downgrade to `C¹`.
  have hsec : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1 realUnitTangentSection :=
    realUnitTangentSection_contMDiff.of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact htm.comp hsec

/-- Convenient alias: the velocity-lift `C¹` smoothness from a `C²` curve. -/
def velocityLift_smoothness {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)) :=
  velocityLift_contMDiff_of_contMDiff_two (I := I) hγ

/-- The `C¹` smoothness of `γ` derived from `C²` smoothness, packaged as
the first smoothness hypothesis of `covDerivAlong`. -/
lemma contMDiff_one_of_contMDiff_two {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    ContMDiff 𝓘(ℝ, ℝ) I 1 γ :=
  hγ.of_le (by exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2))

/-! ## Chart-curve velocity at the basepoint

The chart-coordinate curve `s ↦ extChartAt I (γ t₀) (γ s)`, used by
`covDerivAlong` to extract chart velocity, has derivative
`velocity γ t₀` at `s = t₀`. This follows from the chain rule together
with `mfderiv_extChartAt_self` (the manifold derivative of `extChartAt`
at the basepoint is the identity on the model fibre `E`). -/

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- Chart-velocity equals intrinsic velocity at the basepoint. -/
lemma hasDerivAt_chartCurveAt_self
    {γ : ℝ → M} {t₀ : ℝ} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    HasDerivAt (chartCurveAt (I := I) γ t₀) (velocity (I := I) γ t₀) t₀ := by
  classical
  have hγ_mf : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t₀ :=
    hγ.mdifferentiableAt one_ne_zero
  have hchart_mf : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀) :=
    mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t₀))
  have hcomp_mf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((extChartAt I (γ t₀)) ∘ γ) t₀
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t₀)) :=
    hchart_mf.hasMFDerivAt.comp _ hγ_mf.hasMFDerivAt
  have hcomp_fd : HasFDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t₀)) t₀ :=
    hcomp_mf.hasFDerivAt
  have hcomp_da : HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t₀)) (1 : ℝ)) t₀ :=
    hcomp_fd.hasDerivAt
  -- `mfderiv_extChartAt_self`: `mfderiv (extChartAt I α) α = id`.
  have hmfd_self : mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀) =
      ContinuousLinearMap.id ℝ E := mfderiv_extChartAt_self
  have hval : (((mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t₀)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t₀)) (1 : ℝ)) =
        velocity (I := I) γ t₀ := by
    rw [ContinuousLinearMap.comp_apply, hmfd_self]
    rfl
  rw [hval] at hcomp_da
  -- `chartCurveAt γ t₀ = extChartAt I (γ t₀) ∘ γ` definitionally.
  exact hcomp_da

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- Consequence: `deriv (chartCurveAt γ t₀) t₀ = velocity γ t₀`. -/
lemma deriv_chartCurveAt_self
    {γ : ℝ → M} {t₀ : ℝ} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    deriv (chartCurveAt (I := I) γ t₀) t₀ = velocity (I := I) γ t₀ :=
  (hasDerivAt_chartCurveAt_self (I := I) hγ).deriv

/-! ## Chart-fibre identification along a geodesic lift

In a neighbourhood of `t₀`, the chart-fibre representation of
`velocity γ` (in the chart at `γ t₀`, as used by `covDerivAlong`)
agrees with the chart-fibre coordinate of any α-witnessed lift of `γ`,
under the hypothesis that the base path `γ` stays in the chart at the
witness basepoint `α` near `t₀`. This is the analytic vehicle that
will let downstream developments extract derivatives of
`chartFiberAlong γ (velocity γ) t₀` at `t₀` from the chart-pushed
derivative of the lift.
-/

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- Pointwise: at any time `s` in the chart at the witness basepoint,
the chart-fibre representation of the velocity matches the chart-fibre
coordinate of the lift. -/
lemma chartFiberAlong_velocity_at_eq_chartFiberCoord
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t₀ s : ℝ}
    (hproj : ∀ t, (f t).proj = γ t)
    (hpath_s : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) s)
    (hbase_s : γ s ∈ (chartAt H α).source) :
    chartFiberAlong (I := I) γ (velocity (I := I) γ) t₀ s =
      chartFiberCoord (I := I) (γ t₀) (f s) := by
  classical
  -- Rosetta stone: `velocity γ s = hproj s ▸ (f s).2`.
  have hvel : velocity (I := I) γ s =
      (hproj s ▸ (f s).2 : TangentSpace I (γ s)) :=
    velocity_eq_snd_of_isMIntegralCurveAt (I := I) g α
      hproj hpath_s hbase_s
  -- The chart-fibre representation of velocity at `s` (in chart at `γ t₀`)
  -- equals the chart-fibre coordinate of `⟨γ s, velocity γ s⟩`.
  -- Identify `⟨γ s, velocity γ s⟩ = f s` as bundle points.
  have hpt_eq : (⟨γ s, velocity (I := I) γ s⟩ : TangentBundle I M) = f s := by
    rw [hvel]
    refine Bundle.TotalSpace.ext (hproj s).symm ?_
    change HEq ((hproj s) ▸ (f s).2 : TangentSpace I (γ s)) (f s).2
    exact eqRec_heq (hproj s) ((f s).2)
  unfold chartFiberAlong
  rw [hpt_eq]

/-- A local integral curve at `t₀` is locally an integral curve in a
neighbourhood: for `s` in a neighbourhood of `t₀`, the curve is a local
integral curve at `s` as well. This is a routine `eventually`
manipulation: `IsMIntegralCurveAt` is an `∀ᶠ t in 𝓝 t₀, …` predicate,
and the inner predicate is open in `t`, so the property propagates to
every `s` close enough to `t₀`. -/
lemma IsMIntegralCurveAt.eventually_isMIntegralCurveAt
    {f : ℝ → TangentBundle I M}
    {V : (p : TangentBundle I M) → TangentSpace I.tangent p} {t₀ : ℝ}
    (hf : IsMIntegralCurveAt f V t₀) :
    ∀ᶠ s in 𝓝 t₀, IsMIntegralCurveAt f V s := by
  -- `hf : ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent f t ((1).smulRight (V (f t)))`.
  -- Extract a neighbourhood `U ∈ 𝓝 t₀` on which the formula holds for every `t ∈ U`.
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hf
  obtain ⟨U, hU_nhds, hU⟩ := hf
  rw [Metric.mem_nhds_iff] at hU_nhds
  obtain ⟨ε, hε, hε_sub⟩ := hU_nhds
  -- For every `s` within `ε/2` of `t₀`, every `t` within `ε/2` of `s` is in `U`.
  filter_upwards [Metric.ball_mem_nhds t₀ (half_pos hε)] with s hs
  rw [Metric.mem_ball] at hs
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem]
  refine ⟨Metric.ball s (ε / 2), Metric.ball_mem_nhds _ (half_pos hε), ?_⟩
  intro t ht
  rw [Metric.mem_ball] at ht
  refine hU t (hε_sub ?_)
  -- `dist t t₀ ≤ dist t s + dist s t₀ < ε/2 + ε/2 = ε`.
  rw [Metric.mem_ball]
  calc dist t t₀ ≤ dist t s + dist s t₀ := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by linarith

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- Eventual identification: the chart-fibre representation of `velocity γ`
in chart at `γ t₀` agrees with the chart-fibre coordinate of any
α-witnessed lift `f`, on a neighbourhood of `t₀` (under chart-α
membership at `t₀`). -/
lemma chartFiberAlong_velocity_eventuallyEq_chartFiberCoord
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hproj : ∀ t, (f t).proj = γ t)
    (hpath : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g α) t₀)
    (hbase : γ t₀ ∈ (chartAt H α).source) :
    (fun s => chartFiberAlong (I := I) γ (velocity (I := I) γ) t₀ s) =ᶠ[𝓝 t₀]
      (fun s => chartFiberCoord (I := I) (γ t₀) (f s)) := by
  classical
  -- For `s` near `t₀`, (a) `γ s ∈ chart at α`, and (b) `IsMIntegralCurveAt f V s`.
  -- Continuity of `γ` at `t₀` from `f` continuous + projection.
  have hcont : ContinuousAt γ t₀ := by
    have hf_cont : ContinuousAt f t₀ := hpath.continuousAt
    have hπ_cont : ContinuousAt
        (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t₀) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
    have hcomp : ContinuousAt (fun t => (f t).proj) t₀ := hπ_cont.comp hf_cont
    have heq : (fun t => (f t).proj) = γ := funext hproj
    rw [heq] at hcomp
    exact hcomp
  have hop : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hev_chart : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H α).source :=
    hcont.preimage_mem_nhds (hop.mem_nhds hbase)
  have hev_path :=
    IsMIntegralCurveAt.eventually_isMIntegralCurveAt (I := I)
      (f := f) (V := geodesicVectorFieldChart (I := I) g α)
      (t₀ := t₀) hpath
  filter_upwards [hev_chart, hev_path] with s hs_chart hs_path
  exact chartFiberAlong_velocity_at_eq_chartFiberCoord (I := I)
    (g := g) (α := α) (γ := γ) (f := f) (t₀ := t₀) (s := s)
    hproj hs_path hs_chart

/-! ## Decomposition of the chart-pushed lift into base and fibre components

The chart-pushed lift `chartPushLift f t₀ s = extChartAt I.tangent (f t₀) (f s)`
factors through the product structure of the tangent bundle's extended
chart. We make the decomposition explicit, identifying the two
components with `chartCurveAt γ t₀ s` (the chart-base curve) and
`chartFiberCoord (γ t₀) (f s)` (the chart-fibre coordinate of the
lift, in the chart at `γ t₀`). -/

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- The chart-pushed lift decomposes into chart-base curve and
chart-fibre coordinate. -/
lemma chartPushLift_eq_pair
    {γ : ℝ → M} {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t) (t₀ s : ℝ) :
    chartPushLift (I := I) f t₀ s =
      (chartCurveAt (I := I) γ t₀ s,
        chartFiberCoord (I := I) (γ t₀) (f s)) := by
  classical
  unfold chartPushLift
  have hfb := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
    (x := f t₀)
  rw [hproj t₀] at hfb
  change extChartAt I.tangent (f t₀) (f s) = _
  rw [hfb]
  refine Prod.ext ?_ ?_
  · -- 1st coord: chart of `(triv (f s)).1 = (f s).proj = γ s`.
    change extChartAt I (γ t₀)
      ((trivializationAt E (TangentSpace I) (γ t₀)).toPartialEquiv (f s)).1 =
        extChartAt I (γ t₀) (γ s)
    have hfst : ((trivializationAt E (TangentSpace I) (γ t₀)).toPartialEquiv (f s)).1 =
        (f s).proj :=
      TangentBundle.trivializationAt_fst (I := I) (γ t₀) (f s)
    rw [hfst, hproj s]
  · -- 2nd coord: `(triv (f s)).2 = chartFiberCoord (γ t₀) (f s)` by definition.
    change ((trivializationAt E (TangentSpace I) (γ t₀)).toPartialEquiv (f s)).2 =
      chartFiberCoord (I := I) (γ t₀) (f s)
    rfl

/-! ## Trivialisation of `T(TM)` at the zero section reduces to identity

A subtle but crucial point: even though `T(TM)` is a *non-trivial* vector
bundle in general, its trivialisations attached to two points `⟨α, 0⟩`
and `p` with `p.proj = α` are derived from the chart at the same
projection-point `α` on `M`, and the chart on `TM` at points with
matching projection are *the same partial homeomorphism*
(`FiberBundle.chartedSpace_chartAt` shows the chart depends only on the
projection). Hence the `tangentBundleCore` coordChange between the two
charts is the identity (by `coordChange_self`), and the trivialisation
`(trivAt _ _ ⟨α, 0⟩).symm` at `p` acts as the identity on `E × E`
whenever `p.proj = α`.

This is the analytic key to the basepoint-aligned forward direction. -/

/-- The chart at `q : TM` on `TM` depends only on `q.proj`: any two
points with the same projection have the same chart in the canonical
atlas on `TM`. -/
lemma chartAt_eq_of_proj_eq {q₁ q₂ : TangentBundle I M}
    (hq : q₁.proj = q₂.proj) :
    chartAt (ModelProd H E) q₁ = chartAt (ModelProd H E) q₂ := by
  classical
  rw [FiberBundle.chartedSpace_chartAt, FiberBundle.chartedSpace_chartAt, hq]

/-- The `achart` element of the atlas at `q : TM` depends only on
`q.proj`. -/
lemma achart_eq_of_proj_eq {q₁ q₂ : TangentBundle I M}
    (hq : q₁.proj = q₂.proj) :
    achart (ModelProd H E) q₁ = achart (ModelProd H E) q₂ := by
  apply Subtype.ext
  rw [coe_achart, coe_achart]
  exact chartAt_eq_of_proj_eq (I := I) hq

/-- **Trivialisation at the zero section evaluated at a point with the
same projection equals the identity.** When `p : TM` has `p.proj = α`,
the trivialisation `(trivAt (E × E) (TangentSpace I.tangent) ⟨α, 0⟩)`
acts as the identity on the fibre `E × E` at the point `p`.

Specifically: `(triv … ⟨α, 0⟩).symmL ℝ p X = X` for any `X ∈ E × E`,
because the relevant coordChange in the `tangentBundleCore I.tangent TM`
is between two atlas elements that depend only on the projection — and
the projections agree at `⟨α, 0⟩` and `p`. -/
lemma symmL_trivializationAt_tangent_zeroSection
    {α : M} {p : TangentBundle I M} (hp : p.proj = α)
    (hp_src : p ∈ (chartAt (ModelProd H E)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).source) (X : E × E) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p X = X := by
  classical
  -- Step 1: rewrite the symmL as a tangentBundleCore coordChange.
  rw [TangentBundle.symmL_trivializationAt_eq_core
      (I := I.tangent) (M := TangentBundle I M) hp_src]
  -- Step 2: the two acharts are equal (both depend only on `(·).proj`).
  have hach : achart (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M) =
      achart (ModelProd H E) p := by
    refine achart_eq_of_proj_eq (I := I) ?_
    -- `⟨α, 0⟩.proj = α = p.proj`.
    exact hp.symm
  -- Step 3: with equal acharts, coordChange is the identity.
  rw [hach]
  -- `coordChange achart achart p X = X` whenever `p ∈ baseSet`.
  apply (tangentBundleCore I.tangent (TangentBundle I M)).coordChange_self
  -- We need `p ∈ baseSet of (achart p)`.
  -- `baseSet = chartAt … p.source`, and `p ∈ chartAt … p.source` always.
  -- Need to express this concretely for `tangentBundleCore I.tangent TM`.
  rw [tangentBundleCore_baseSet, coe_achart]
  exact mem_chart_source _ p

/-- **Chart-fibre identity for the geodesic vector field at the
basepoint witness.** When the chart basepoint `α` matches the
projection of `p`, the chart-fixed geodesic vector field at `p` agrees
as an element of `E × E` with the chart-fibre data
`geodesicVectorFieldChartFiber g α p`. -/
lemma geodesicVectorFieldChart_eq_chartFiber_of_proj_eq
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {α : M} {p : TangentBundle I M}
    (hp : p.proj = α) (hp_src : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChartFiber (I := I) g α p := by
  classical
  unfold geodesicVectorFieldChart
  -- Source membership for the tangent-bundle chart at `⟨α, 0⟩`.
  have hp' : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp_src
  -- `e.symm p y = e.symmL ℝ p y` as values (definition unfolding).
  -- Use `symmL_trivializationAt_tangent_zeroSection` to reduce to identity.
  have hsymm : (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).symm p
        (geodesicVectorFieldChartFiber (I := I) g α p) =
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p
        (geodesicVectorFieldChartFiber (I := I) g α p) := rfl
  rw [hsymm]
  exact symmL_trivializationAt_tangent_zeroSection (I := I) hp hp' _

/-! ## The forward direction along a basepoint-aligned witness

We bring the helper lemmas together: given a `C¹` curve `γ` and a lift
`f : ℝ → TangentBundle I M` projecting to `γ` that is a local integral
curve of the chart-fixed geodesic vector field at the *basepoint*
`α := γ t₀`, we show
`covDerivAlong g γ (velocity γ) … t₀ = 0`. -/

section BasepointAlignedForward

variable [I.Boundaryless] [CompleteSpace E]

open DifferentialGeometry.Geometry.Riemannian.Curve in
/-- **Forward direction, basepoint-aligned witness.** A curve `γ` whose
geodesic lift is witnessed by the chart basepoint `α := γ t₀` has
vanishing covariant derivative of `velocity γ` along `γ` at `t₀`.

This is the diagonal specialisation of the intended general forward
direction `IsGeodesicAt g γ t₀ ⇒ covDerivAlong … t₀ = 0`. Witnesses of
this shape arise canonically from the existence theorem
`exists_geodesic_at`. -/
theorem covDerivAlong_velocity_eq_zero_of_basepoint_aligned
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hVel : ContMDiff 𝓘(ℝ, ℝ) I.tangent 1
        (fun t => (⟨γ t, velocity (I := I) γ t⟩ : TangentBundle I M)))
    {f : ℝ → TangentBundle I M} (hproj : ∀ t, (f t).proj = γ t)
    (hpath : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    covDerivAlong (I := I) g γ (velocity (I := I) γ) hγ hVel t₀ = 0 := by
  classical
  -- (Step 0) Basic setup.
  have hbase : γ t₀ ∈ (chartAt H (γ t₀)).source := mem_chart_source H (γ t₀)
  set y₀ : E := chartCurveAt (I := I) γ t₀ t₀ with hy₀_def
  have hy₀ : y₀ = extChartAt I (γ t₀) (γ t₀) := rfl
  -- (Step 1) chart-pushed `HasDerivAt` formula near t₀, with α := γ t₀.
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := γ t₀) (t₀ := t₀) (f := f) hpath
  -- (Step 2) The chart-pushed lift = (chartCurveAt, chartFiberCoord ∘ f).
  have hsplit_pt := chartPushLift_eq_pair (I := I) (γ := γ) (f := f) hproj t₀
  have hsplit : ∀ᶠ s in 𝓝 t₀,
      chartPushLift (I := I) f t₀ s =
        (chartCurveAt (I := I) γ t₀ s,
          chartFiberCoord (I := I) (γ t₀) (f s)) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    exact chartPushLift_eq_pair (I := I) (γ := γ) (f := f) hproj t₀ s
  -- (Step 3) From the chart-pushed formula, extract the 2nd-coord HasDerivAt.
  -- For `s` near `t₀`, `HasDerivAt (s ↦ chartFiberCoord (γ t₀) (f s))
  --   ((chartPushVF g (γ t₀) f t₀ s).2) s`.
  -- Pull this from `hpush` via Prod.snd (HasFDerivAt.snd).
  have hpush_snd : ∀ᶠ s in 𝓝 t₀, HasDerivAt
      (fun s => chartFiberCoord (I := I) (γ t₀) (f s))
      (chartPushVF (I := I) g (γ t₀) f t₀ s).2 s := by
    filter_upwards [hpush, hsplit] with s hs_push hs_split
    -- Convert chartPushLift's HasDerivAt to HasFDerivAt and project via .snd.
    have hsnd_fd : HasFDerivAt (fun u => (chartPushLift (I := I) f t₀ u).2)
      (ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (chartPushVF (I := I) g (γ t₀) f t₀ s)))
      s := hs_push.hasFDerivAt.snd
    have hsnd_da : HasDerivAt (fun u => (chartPushLift (I := I) f t₀ u).2)
      ((ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (chartPushVF (I := I) g (γ t₀) f t₀ s)))
          (1 : ℝ))
      s := hsnd_fd.hasDerivAt
    -- Simplify the derivative value: snd ∘ ((1).smulRight X) applied to 1 = X.2.
    have hval : (ContinuousLinearMap.snd ℝ E E |>.comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (chartPushVF (I := I) g (γ t₀) f t₀ s)))
          (1 : ℝ) = (chartPushVF (I := I) g (γ t₀) f t₀ s).2 := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply]
    rw [hval] at hsnd_da
    -- Now `hsnd_da : HasDerivAt (u ↦ (chartPushLift f t₀ u).2) … s`.
    -- We want `HasDerivAt (u ↦ chartFiberCoord (γ t₀) (f u)) … s`.
    -- Use the pointwise equality (function-level identity since `chartPushLift_eq_pair`
    -- holds for every `s`).
    have hfun_eq : (fun u => (chartPushLift (I := I) f t₀ u).2) =
        (fun u => chartFiberCoord (I := I) (γ t₀) (f u)) := by
      funext u
      rw [chartPushLift_eq_pair (I := I) (γ := γ) (f := f) hproj t₀ u]
    rw [hfun_eq] at hsnd_da
    exact hsnd_da
  -- (Step 4) At `s = t₀`, evaluate `(chartPushVF g (γ t₀) f t₀ t₀).2`.
  have hpushVF_t₀ : chartPushVF (I := I) g (γ t₀) f t₀ t₀ =
      geodesicVectorFieldChart (I := I) g (γ t₀) (f t₀) := by
    unfold chartPushVF
    apply tangentCoordChange_self
    exact mem_extChartAt_source (I := I.tangent) (f t₀)
  -- (Step 5) `geodesicVectorFieldChart g (γ t₀) (f t₀) = geodesicVectorFieldChartFiber g (γ t₀) (f t₀)`.
  have hgvfChart_eq : geodesicVectorFieldChart (I := I) g (γ t₀) (f t₀) =
      geodesicVectorFieldChartFiber (I := I) g (γ t₀) (f t₀) := by
    apply geodesicVectorFieldChart_eq_chartFiber_of_proj_eq (I := I)
    · exact hproj t₀
    · rw [hproj t₀]; exact hbase
  -- (Step 6) The fiber data's 2nd coord: `-Γ_{γt₀}(v, v)(y₀)` with v = chartFiberCoord (γ t₀) (f t₀).
  have hsnd_fiber : (geodesicVectorFieldChartFiber (I := I) g (γ t₀) (f t₀)).2 =
      - chartChristoffelContraction (I := I) g (γ t₀)
        (chartFiberCoord (I := I) (γ t₀) (f t₀))
        (chartFiberCoord (I := I) (γ t₀) (f t₀))
        (extChartAt I (γ t₀) (f t₀).proj) := rfl
  -- (Step 7) `chartFiberCoord (γ t₀) (f t₀) = velocity γ t₀`.
  -- By `velocity_eq_snd_of_isMIntegralCurveAt` applied at α = γ t₀ and t = t₀:
  have hvel_eq : velocity (I := I) γ t₀ =
      (hproj t₀ ▸ (f t₀).2 : TangentSpace I (γ t₀)) :=
    velocity_eq_snd_of_isMIntegralCurveAt (I := I) g (γ t₀)
      hproj hpath hbase
  -- The chartFiberCoord at the basepoint equals `velocity γ t₀`.
  have hfc_eq_vel : chartFiberCoord (I := I) (γ t₀) (f t₀) =
      velocity (I := I) γ t₀ := by
    -- `chartFiberCoord (γ t₀) (f t₀) = ((trivAt γt₀) (f t₀)).2`.
    -- Use `chartFiberCoord_eq_clmAt_of_mem` to get fibre-linearity.
    -- Direct route: `f t₀ = ⟨γ t₀, (f t₀).2 (transported)⟩` as bundle pts.
    have hpt_eq : (⟨γ t₀, velocity (I := I) γ t₀⟩ : TangentBundle I M) = f t₀ := by
      rw [hvel_eq]
      refine Bundle.TotalSpace.ext (hproj t₀).symm ?_
      change HEq ((hproj t₀) ▸ (f t₀).2 : TangentSpace I (γ t₀)) (f t₀).2
      exact eqRec_heq (hproj t₀) ((f t₀).2)
    -- `chartFiberCoord (γ t₀) ⟨γ t₀, velocity γ t₀⟩ = velocity γ t₀` by self.
    have hself := chartFiberCoord_self (I := I) (γ t₀) (velocity (I := I) γ t₀)
    -- Now `chartFiberCoord (γ t₀) (f t₀) = chartFiberCoord (γ t₀) ⟨γ t₀, velocity γ t₀⟩`.
    -- This is just rewriting the input via hpt_eq.
    rw [← hpt_eq, hself]
  -- (Step 8) Combine: deriv (chartFiberCoord (γ t₀) ∘ f) t₀ = -Γ_{γt₀}(velocity, velocity)(y₀).
  -- Use hpush_snd at t₀ + hpushVF_t₀ + hgvfChart_eq + hsnd_fiber + hfc_eq_vel.
  have hpush_snd_t₀ : HasDerivAt
      (fun s => chartFiberCoord (I := I) (γ t₀) (f s))
      (chartPushVF (I := I) g (γ t₀) f t₀ t₀).2 t₀ := hpush_snd.self_of_nhds
  rw [hpushVF_t₀, hgvfChart_eq, hsnd_fiber, hfc_eq_vel, hproj t₀] at hpush_snd_t₀
  -- `hpush_snd_t₀ : HasDerivAt (s ↦ chartFiberCoord (γ t₀) (f s))
  --   (-Γ_{γt₀}(velocity γ t₀, velocity γ t₀)(extChartAt I (γt₀)(γt₀))) t₀`.
  -- (Step 9) Transfer to chartFiberAlong via the eventual equality.
  have hev_eq := chartFiberAlong_velocity_eventuallyEq_chartFiberCoord (I := I)
    (g := g) (α := γ t₀) (γ := γ) (f := f) (t₀ := t₀) hproj hpath hbase
  have hcfAlong_da : HasDerivAt
      (chartFiberAlong (I := I) γ (velocity (I := I) γ) t₀)
      (- chartChristoffelContraction (I := I) g (γ t₀)
          (velocity (I := I) γ t₀) (velocity (I := I) γ t₀)
          (extChartAt I (γ t₀) (γ t₀))) t₀ :=
    hpush_snd_t₀.congr_of_eventuallyEq hev_eq
  -- (Step 10) Combine with the chart-curve derivative.
  have hcurve_da := hasDerivAt_chartCurveAt_self (I := I) (γ := γ) (t₀ := t₀) hγ
  -- Now `covDerivAlong = (-Γ) + Γ = 0`.
  rw [covDerivAlong_def]
  -- `deriv (chartFiberAlong γ V t₀) t₀ = -Γ(velocity, velocity)(y₀)`.
  rw [hcfAlong_da.deriv]
  -- `deriv (chartCurveAt γ t₀) t₀ = velocity γ t₀`.
  rw [hcurve_da.deriv]
  -- `chartCurveAt γ t₀ t₀ = extChartAt I (γ t₀) (γ t₀)`.
  -- Goal: `-Γ + Γ = 0`.
  have : (- chartChristoffelContraction (I := I) g (γ t₀)
      (velocity (I := I) γ t₀) (velocity (I := I) γ t₀)
      (extChartAt I (γ t₀) (γ t₀))) +
      chartChristoffelContraction (I := I) g (γ t₀)
        (velocity (I := I) γ t₀) (velocity (I := I) γ t₀)
        (chartCurveAt (I := I) γ t₀ t₀) = 0 := by
    have hcca : chartCurveAt (I := I) γ t₀ t₀ = extChartAt I (γ t₀) (γ t₀) := rfl
    rw [hcca]
    -- E-valued algebra: `-x + x = 0`. Done by neg_add_cancel modulo TangentSpace identification.
    -- The arithmetic here is in `TangentSpace I (γ t₀) = E`.
    change (- _) + _ = (0 : E)
    exact neg_add_cancel _
  -- Apply the algebra.
  exact this

end BasepointAlignedForward

/-! ## Status of the headline iff

The intended headline iff

```
IsGeodesicAt g γ t₀ ↔ covDerivAlong g γ (velocity γ) … t₀ = 0
```

is held back by two distinct obstructions:

* **Forward direction (`IsGeodesicAt ⇒ covDerivAlong = 0`)**, **general
  `α` case**: the chart-pushed derivative formula provides
  `(geodesicVectorFieldChart g α (f t₀)).2` as the relevant chart-fibre
  derivative, while `covDerivAlong` uses chart-`γ t₀` Christoffel
  symbols. Bridging requires the chart-overlap law for the geodesic
  vector field across chart changes (the Christoffel symbols
  transforming as a connection). This is recorded as a pending
  mathematical prerequisite.

  The diagonal case `α := γ t₀` is however accessible — when the
  witness basepoint matches the time-`t₀` foot, the trivialisation of
  `T(TM)` at `⟨γ t₀, 0⟩` evaluated at `f t₀` reduces to the identity
  (by `achart_eq_of_proj_eq` together with
  `(tangentBundleCore I.tangent TM).coordChange_self`), and the
  chart-pushed second component collapses to the explicit chart-`γ t₀`
  Christoffel form. The basepoint-aligned forward bridge is recorded
  below.

* **Reverse direction (`covDerivAlong = 0 ⇒ IsGeodesicAt`)**: the
  hypothesis `covDerivAlong … t₀ = 0` is a *single-point* assertion,
  while `IsGeodesicAt` is an `∀ᶠ t in 𝓝 t₀`-eventual integral-curve
  property of the lift. Pointwise vanishing of the second covariant
  derivative does not in general force the integral-curve property on
  any neighbourhood; the natural neighbourhood-version reverse bridge
  reads
  `(∀ᶠ t in 𝓝 t₀, covDerivAlong g γ (velocity γ) … t = 0) ⇒
    IsGeodesicAt g γ t₀`
  and uses Picard-Lindelöf uniqueness of the chart-pushed second-order
  ODE in the model space `E` (this is the standard "geodesic equation
  ↔ integral curve of the geodesic vector field" textbook
  equivalence). Both directions of this neighbourhood-version
  iff still bridge the chart-`γ t₀` Christoffel formulation
  (covDerivAlong) with the chart-`α` Christoffel formulation
  (`IsGeodesicAt`), so the chart-overlap law is again required when
  `α ≠ γ t₀`. -/

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
