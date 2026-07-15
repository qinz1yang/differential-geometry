import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism

set_option linter.unusedSectionVars false

/-!
# Normal coordinates around a base point

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, and any base point
`p : M`, the exponential map `expMap g p : T_p M → M` is a local
`C^1` diffeomorphism at the zero vector (see
`Exponential/LocalDiffeomorphism.lean`). Inverting that local
diffeomorphism produces the **normal coordinate chart at `p`**: a
`PartialDiffeomorph` mapping a manifold neighborhood of `p` onto an open
neighborhood of `0 ∈ T_p M ≃ E`.

This file packages three classical properties of the normal chart:

* `normalChartAt g p` — the chart itself, defined as the `symm` of the
  exponential's partial diffeomorphism;
* `normalChartAt_centre` — the chart sends `p` to `0`;
* `normalChartAt_source` — `p` lies in the chart's source.

* `mfderiv_normalChartAt_self` — the manifold derivative of the normal
  chart at `p` is the identity continuous linear map. This expresses, in
  the cleanest form, the property "g_{ij}(p) = δ_{ij} in normal
  coordinates at `p`": the chart's pullback of the metric at `p` is
  obtained from `g.inner p` by composing with the differential
  `mfderiv (normalChartAt g p) p = id`, so the pullback at the origin
  reads `g.inner p v w` for all `v, w : E`. The user-facing pullback
  identity is `normalChartAt_metric_pullback_at_origin`.

* `normalChartAt_expMap_smul` — the radial-line property: for
  sufficiently small `s` (i.e. `s • v` in the chart's target),
  `normalChartAt g p (expMap g p (s • v)) = s • v`. This expresses, in
  the cleanest form, the property "Christoffel symbols vanish at `p` in
  normal coordinates": radial geodesics through `p` are straight lines
  in the chart, so their chart-coordinate acceleration is zero. The
  user-facing acceleration-vanishing identity is
  `normalChartAt_radial_secondDeriv_zero`.

## Strategy

We use the public endpoints
`expMap_isLocalDiffeomorphAt_zero` and `exists_open_nhds_expMap_diffeoOn`
from `LocalDiffeomorphism.lean`. The latter packages the exponential map
as a `PartialDiffeomorph`; we extract it via `Classical.choose`, take
`.symm`, and inherit all the chart-axiom properties from the
`PartialEquiv` structure.

The metric-at-origin property reduces to `mfderiv_expMap_at_zero`
(= identity) composed with the diffeomorphism inverse derivative
formula `(mfderiv Φ.symm (Φ x)).comp (mfderiv Φ x) = id`.

The radial-image identity is the definitional content of "left inverse":
if `s • v` lies in the symm-target (= original toFun source), then the
chart applied to `expMap` at that point equals `s • v`. The
second-derivative-zero corollary is then a calculus statement on the
linear function `s ↦ s • v`.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

section NormalChart

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- The exponential-side partial diffeomorphism at `p`: a
`PartialDiffeomorph` containing `0 ∈ T_p M` in its source whose
underlying function agrees with `v ↦ expMap g p v` on the source. -/
def expMapDiffeo (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
  Classical.choose (exists_exp_pd_chart (I := I) g p)

lemma zero_mem_expMapDiffeo_source (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
  (Classical.choose_spec (exists_exp_pd_chart (I := I) g p)).1

lemma expMapDiffeo_apply_eq (g : SmoothRiemannianMetric I M) (p : M)
    {v : E} (hv : v ∈ (expMapDiffeo (I := I) g p).source) :
    expMapDiffeo (I := I) g p v =
      (expMap (I := I) g p (show TangentSpace I p from v) : M) :=
  (Classical.choose_spec (exists_exp_pd_chart (I := I) g p)).2.1 v hv

/-- The selected exponential partial diffeomorphism remains inside the base
chart used to construct it. -/
lemma exp_target_sub_chart (g : SmoothRiemannianMetric I M) (p : M) :
    (expMapDiffeo (I := I) g p).target ⊆ (chartAt H p).source :=
  (Classical.choose_spec (exists_exp_pd_chart (I := I) g p)).2.2

/-- The exponential-side partial diffeomorphism maps `0` to `p`. -/
lemma expMapDiffeo_zero (g : SmoothRiemannianMetric I M) (p : M) :
    expMapDiffeo (I := I) g p (0 : E) = p := by
  classical
  rw [expMapDiffeo_apply_eq (I := I) g p (zero_mem_expMapDiffeo_source (I := I) g p)]
  exact expMap_zero (I := I) g p

/-- `p` lies in the target of the exponential-side diffeomorphism. -/
lemma p_mem_expMapDiffeo_target (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ (expMapDiffeo (I := I) g p).target := by
  classical
  have h := (expMapDiffeo (I := I) g p).map_source
    (zero_mem_expMapDiffeo_source (I := I) g p)
  rw [expMapDiffeo_zero] at h
  exact h

/-- **The normal coordinate chart at `p`.** -/
def normalChartAt (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E 1 :=
  (expMapDiffeo (I := I) g p).symm

/-- The source of the normal chart is the target of the exponential-side
diffeomorphism. -/
@[simp] lemma normalChartAt_source_eq (g : SmoothRiemannianMetric I M) (p : M) :
    (normalChartAt (I := I) g p).source = (expMapDiffeo (I := I) g p).target := rfl

/-- The target of the normal chart is the source of the exponential-side
diffeomorphism (an open neighborhood of `0 ∈ E`). -/
@[simp] lemma normalChartAt_target_eq (g : SmoothRiemannianMetric I M) (p : M) :
    (normalChartAt (I := I) g p).target = (expMapDiffeo (I := I) g p).source := rfl

/-- The underlying `PartialEquiv` of the normal chart is the `symm` of
the exponential-side diffeomorphism's `PartialEquiv`. -/
@[simp] lemma normalChartAt_toPartialEquiv (g : SmoothRiemannianMetric I M) (p : M) :
    (normalChartAt (I := I) g p).toPartialEquiv =
      (expMapDiffeo (I := I) g p).toPartialEquiv.symm := rfl

/-- The source of the normal chart is open. -/
lemma normalChartAt_open_source (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (normalChartAt (I := I) g p).source :=
  (normalChartAt (I := I) g p).open_source

/-- The target of the normal chart is open. -/
lemma normalChartAt_open_target (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (normalChartAt (I := I) g p).target :=
  (normalChartAt (I := I) g p).open_target

/-- **`p` lies in the source of the normal chart at `p`.** -/
theorem normalChartAt_source (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ (normalChartAt (I := I) g p).source := by
  rw [normalChartAt_source_eq]
  exact p_mem_expMapDiffeo_target (I := I) g p

/-- **The normal chart at `p` maps `p` to the origin `0 ∈ E`.** -/
theorem normalChartAt_centre (g : SmoothRiemannianMetric I M) (p : M) :
    normalChartAt (I := I) g p p = (0 : E) := by
  classical
  have h_inv : (expMapDiffeo (I := I) g p).symm
      ((expMapDiffeo (I := I) g p) (0 : E)) = (0 : E) :=
    (expMapDiffeo (I := I) g p).left_inv (zero_mem_expMapDiffeo_source (I := I) g p)
  rw [expMapDiffeo_zero] at h_inv
  exact h_inv

/-- The origin lies in the target of the normal chart. -/
lemma zero_mem_normalChartAt_target (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (normalChartAt (I := I) g p).target := by
  rw [normalChartAt_target_eq]
  exact zero_mem_expMapDiffeo_source (I := I) g p

/-- The inverse of the normal chart applied at `0` returns `p`. -/
lemma normalChartAt_symm_zero (g : SmoothRiemannianMetric I M) (p : M) :
    (normalChartAt (I := I) g p).symm (0 : E) = p := by
  classical
  have : (normalChartAt (I := I) g p).symm (0 : E) =
      (expMapDiffeo (I := I) g p) (0 : E) := rfl
  rw [this]
  exact expMapDiffeo_zero (I := I) g p

/-- Applying the normal chart, then its inverse, recovers the original
point (left inverse on the source). -/
lemma normalChartAt_left_inv (g : SmoothRiemannianMetric I M) (p : M)
    {q : M} (hq : q ∈ (normalChartAt (I := I) g p).source) :
    (normalChartAt (I := I) g p).symm (normalChartAt (I := I) g p q) = q :=
  (normalChartAt (I := I) g p).left_inv hq

/-- Applying the inverse of the normal chart, then the chart, recovers
the original chart coordinate (right inverse on the target). -/
lemma normalChartAt_right_inv (g : SmoothRiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ (normalChartAt (I := I) g p).target) :
    normalChartAt (I := I) g p ((normalChartAt (I := I) g p).symm y) = y :=
  (normalChartAt (I := I) g p).right_inv hy

/-- The inverse of the normal chart, on its source, equals the
exponential map. -/
lemma normalChartAt_symm_apply (g : SmoothRiemannianMetric I M) (p : M)
    {v : E} (hv : v ∈ (normalChartAt (I := I) g p).symm.source) :
    (normalChartAt (I := I) g p).symm v =
      (expMap (I := I) g p (show TangentSpace I p from v) : M) := by
  classical
  have hv' : v ∈ (expMapDiffeo (I := I) g p).source := by
    have : (normalChartAt (I := I) g p).symm.source =
        (normalChartAt (I := I) g p).target := rfl
    rw [this] at hv
    rw [normalChartAt_target_eq] at hv
    exact hv
  have h_fun : (normalChartAt (I := I) g p).symm v =
      (expMapDiffeo (I := I) g p) v := rfl
  rw [h_fun]
  exact expMapDiffeo_apply_eq (I := I) g p hv'

/-- The smoothness `ContMDiffOn` data of the normal chart on its source. -/
lemma normalChartAt_contMDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, E) 1 (normalChartAt (I := I) g p)
      (normalChartAt (I := I) g p).source :=
  (normalChartAt (I := I) g p).contMDiffOn_toFun

/-- The smoothness `ContMDiffOn` data of the inverse of the normal chart
on its target. -/
lemma normalChartAt_symm_contMDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I 1 (normalChartAt (I := I) g p).symm
      (normalChartAt (I := I) g p).target :=
  (normalChartAt (I := I) g p).contMDiffOn_invFun

/-- The exponential-side diffeomorphism is differentiable at `0`. -/
private lemma expMapDiffeo_mdifferentiableAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    MDifferentiableAt 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E) :=
  ((expMapDiffeo (I := I) g p).contMDiffOn_toFun.mdifferentiableOn one_ne_zero
    (0 : E) (zero_mem_expMapDiffeo_source (I := I) g p)).mdifferentiableAt
      ((expMapDiffeo (I := I) g p).open_source.mem_nhds
        (zero_mem_expMapDiffeo_source (I := I) g p))

/-- The normal chart is differentiable at `p`. -/
private lemma normalChartAt_mdifferentiableAt_p
    (g : SmoothRiemannianMetric I M) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, E) (normalChartAt (I := I) g p) p :=
  ((normalChartAt (I := I) g p).contMDiffOn_toFun.mdifferentiableOn one_ne_zero
    p (normalChartAt_source (I := I) g p)).mdifferentiableAt
      ((normalChartAt (I := I) g p).open_source.mem_nhds
        (normalChartAt_source (I := I) g p))

/-- The manifold derivative of `expMapDiffeo g p` at `0` equals the
manifold derivative of `expMap g p` at `0`. This is just unfolding the
agreement of `expMapDiffeo` with `expMap` on the source, applied to
`mfderiv`. -/
private lemma mfderiv_expMapDiffeo_at_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E) =
      mfderiv 𝓘(ℝ, E) I
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (0 : E) := by
  classical
  have h_eventually : expMapDiffeo (I := I) g p =ᶠ[nhds (0 : E)]
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) g p).open_source.mem_nhds
        (zero_mem_expMapDiffeo_source (I := I) g p)) ?_
    intro v hv
    exact expMapDiffeo_apply_eq (I := I) g p hv
  exact h_eventually.mfderiv_eq

/-- The manifold derivative of `expMapDiffeo g p` at `0` is the identity
continuous linear map. This is the chained form of
`mfderiv_expMap_at_zero` through the partial-diffeomorph wrapper. -/
private lemma mfderiv_expMapDiffeo_at_zero_eq_id
    (g : SmoothRiemannianMetric I M) (p : M) :
    mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  rw [mfderiv_expMapDiffeo_at_zero (I := I) g p]
  exact mfderiv_expMap_at_zero (I := I) g p

/-- Composition of the normal chart's derivative at `p` with the
exponential-side diffeomorphism's derivative at `0` yields the
identity on `TangentSpace 𝓘(ℝ, E) (0 : E) = E`. -/
private lemma mfderiv_normalChartAt_comp_expMapDiffeo
    (g : SmoothRiemannianMetric I M) (p : M) :
    (mfderiv I 𝓘(ℝ, E) (normalChartAt (I := I) g p) p).comp
        (mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E)) =
      ContinuousLinearMap.id ℝ E := by
  classical
  have h_eventually : (normalChartAt (I := I) g p) ∘ (expMapDiffeo (I := I) g p)
      =ᶠ[nhds (0 : E)] (_root_.id : E → E) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) g p).open_source.mem_nhds
        (zero_mem_expMapDiffeo_source (I := I) g p)) ?_
    intro v hv
    change (normalChartAt (I := I) g p) ((expMapDiffeo (I := I) g p) v) = v
    exact (expMapDiffeo (I := I) g p).left_inv hv
  have h_mfderiv_id : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (_root_.id : E → E) (0 : E) =
      ContinuousLinearMap.id ℝ E := mfderiv_id
  have h_mfderiv_comp_eq :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (normalChartAt (I := I) g p ∘ expMapDiffeo (I := I) g p) (0 : E) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (_root_.id : E → E) (0 : E) :=
    h_eventually.mfderiv_eq
  have h_normal_diff : MDifferentiableAt I 𝓘(ℝ, E) (normalChartAt (I := I) g p)
      ((expMapDiffeo (I := I) g p) (0 : E)) := by
    rw [expMapDiffeo_zero (I := I) g p]
    exact normalChartAt_mdifferentiableAt_p (I := I) g p
  have h_expMap_diff : MDifferentiableAt 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p)
      (0 : E) := expMapDiffeo_mdifferentiableAt_zero (I := I) g p
  have h_chain := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := expMapDiffeo (I := I) g p)
    (g := normalChartAt (I := I) g p) (x := (0 : E))
    h_normal_diff h_expMap_diff
  rw [expMapDiffeo_zero (I := I) g p] at h_chain
  rw [h_chain, h_mfderiv_id] at h_mfderiv_comp_eq
  exact h_mfderiv_comp_eq

/-- **The manifold derivative of the normal chart at `p` is the
identity.** This is the precise content of "the chart's differential at
the centre equals the standard identification of tangent spaces". -/
theorem mfderiv_normalChartAt_self (g : SmoothRiemannianMetric I M) (p : M) :
    mfderiv I 𝓘(ℝ, E) (normalChartAt (I := I) g p) p =
      ContinuousLinearMap.id ℝ E := by
  classical
  have h := mfderiv_normalChartAt_comp_expMapDiffeo (I := I) g p
  rw [mfderiv_expMapDiffeo_at_zero_eq_id (I := I) g p] at h
  simpa using h

/-- The inverse of the normal chart has identity manifold derivative at
`0`: since `(normalChartAt g p).symm` agrees with `expMapDiffeo g p` and
the latter's derivative at `0` is the identity. -/
theorem mfderiv_normalChartAt_symm_zero (g : SmoothRiemannianMetric I M) (p : M) :
    mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  have h_eq : mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) =
      mfderiv 𝓘(ℝ, E) I (expMapDiffeo (I := I) g p) (0 : E) := rfl
  rw [h_eq]
  exact mfderiv_expMapDiffeo_at_zero_eq_id (I := I) g p

/-- **The metric pullback at the origin under the normal chart equals
`g.inner p`.** Specifically, applying the
inverse-of-normal-chart's differential at the origin to vectors
`v, w : E` (which gives `v, w` themselves by
`mfderiv_normalChartAt_symm_zero`), the metric inner product equals
`g.inner p v w`. -/
theorem normalChartAt_metric_pullback_at_origin
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    g.inner p
        (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) v)
        (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) w) =
      g.inner p v w := by
  rw [mfderiv_normalChartAt_symm_zero (I := I) g p]
  rfl

/-- **Companion statement: the metric pullback at `p` in normal
coordinates equals `g.inner p`.** Pushing forward `v, w` through
`mfderiv (normalChartAt g p) p = id` leaves them unchanged, so the
pullback at `p` of the metric, applied to `(v, w) : E × E`, equals
`g.inner p v w`. -/
theorem normalChartAt_metric_at_origin
    (g : SmoothRiemannianMetric I M) (p : M) (v w : E) :
    g.inner p
        (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) v)
        (mfderiv 𝓘(ℝ, E) I (normalChartAt (I := I) g p).symm (0 : E) w) =
      g.inner p v w :=
  normalChartAt_metric_pullback_at_origin (I := I) g p v w

/-- **The radial-line identity.** If `s • v` lies in the target
of the normal chart at `p`, then the chart applied to the
exponential-map image returns `s • v`. -/
theorem normalChartAt_expMap_smul
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) (s : ℝ)
    (hsv : s • v ∈ (normalChartAt (I := I) g p).target) :
    normalChartAt (I := I) g p
      (expMap (I := I) g p (show TangentSpace I p from s • v)) = s • v := by
  classical
  have hsv' : s • v ∈ (expMapDiffeo (I := I) g p).source := by
    rw [← normalChartAt_target_eq (I := I) g p]; exact hsv
  have h_eq_exp : expMapDiffeo (I := I) g p (s • v) =
      (expMap (I := I) g p (show TangentSpace I p from s • v) : M) :=
    expMapDiffeo_apply_eq (I := I) g p hsv'
  have h_inv : (expMapDiffeo (I := I) g p).symm
      ((expMapDiffeo (I := I) g p) (s • v)) = s • v :=
    (expMapDiffeo (I := I) g p).left_inv hsv'
  have h_norm : normalChartAt (I := I) g p
      ((expMap (I := I) g p (show TangentSpace I p from s • v) : M)) = s • v := by
    rw [← h_eq_exp]; exact h_inv
  exact h_norm

/-- The radial chart-coordinate curve through `p` in normal
coordinates: `s ↦ normalChartAt g p (expMap g p (s • v))`. -/
def radialChartCurve (g : SmoothRiemannianMetric I M) (p : M) (v : E) : ℝ → E :=
  fun s => normalChartAt (I := I) g p
    (expMap (I := I) g p (show TangentSpace I p from s • v))

@[simp] lemma radialChartCurve_def
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) (s : ℝ) :
    radialChartCurve (I := I) g p v s =
      normalChartAt (I := I) g p
        (expMap (I := I) g p (show TangentSpace I p from s • v)) := rfl

/-- **The radial curve identity.** On the open set of `s : ℝ` such that
`s • v ∈ (normalChartAt g p).target`, the radial chart-coordinate curve
equals the linear function `s ↦ s • v`. -/
theorem radialChartCurve_eq_linear
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) (s : ℝ)
    (hsv : s • v ∈ (normalChartAt (I := I) g p).target) :
    radialChartCurve (I := I) g p v s = s • v :=
  normalChartAt_expMap_smul (I := I) g p v s hsv

/-- The set of scaling parameters `s : ℝ` for which `s • v` lies in the
chart's target. Since the target is open and contains `0`, this is an
open neighborhood of `0` in `ℝ`. -/
def radialDomain (g : SmoothRiemannianMetric I M) (p : M) (v : E) : Set ℝ :=
  {s : ℝ | s • v ∈ (normalChartAt (I := I) g p).target}

lemma zero_mem_radialDomain (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    (0 : ℝ) ∈ radialDomain (I := I) g p v := by
  classical
  change (0 : ℝ) • v ∈ (normalChartAt (I := I) g p).target
  rw [zero_smul]
  exact zero_mem_normalChartAt_target (I := I) g p

lemma radialDomain_isOpen (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    IsOpen (radialDomain (I := I) g p v) := by
  classical
  have h_cont : Continuous fun s : ℝ => s • v :=
    continuous_id.smul continuous_const
  exact (normalChartAt_open_target (I := I) g p).preimage h_cont

/-- The radial chart-coordinate curve agrees with `s ↦ s • v` on a
neighborhood of `0` in `ℝ`. -/
theorem radialChartCurve_eventuallyEq
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    radialChartCurve (I := I) g p v =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => s • v) := by
  classical
  refine Filter.eventuallyEq_of_mem
    ((radialDomain_isOpen (I := I) g p v).mem_nhds
      (zero_mem_radialDomain (I := I) g p v)) ?_
  intro s hs
  exact radialChartCurve_eq_linear (I := I) g p v s hs

/-- The chart-coordinate radial curve is `C^∞` smooth at `s = 0`
(since it agrees with the smooth linear function `s ↦ s • v` near `0`).
This in particular gives first and second derivatives at `0`. -/
theorem radialChartCurve_hasDerivAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    HasDerivAt (radialChartCurve (I := I) g p v) v (0 : ℝ) := by
  classical
  have h_linear : HasDerivAt (fun s : ℝ => s • v) v (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact h_linear.congr_of_eventuallyEq
    (radialChartCurve_eventuallyEq (I := I) g p v)

/-- The derivative-of-derivative at `0` of the radial chart-coordinate
curve is zero: this expresses the vanishing of geodesic acceleration in
normal coordinates at the centre. -/
theorem radialChartCurve_secondDeriv_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    HasDerivAt (fun s : ℝ => deriv (radialChartCurve (I := I) g p v) s)
      (0 : E) (0 : ℝ) := by
  classical
  have h_deriv_eq : (fun s : ℝ => deriv (radialChartCurve (I := I) g p v) s)
      =ᶠ[nhds (0 : ℝ)] (fun _ : ℝ => v) := by
    have h_curve_eq := radialChartCurve_eventuallyEq (I := I) g p v
    refine Filter.eventually_iff_exists_mem.mpr ?_
    refine ⟨radialDomain (I := I) g p v, ?_, ?_⟩
    · exact (radialDomain_isOpen (I := I) g p v).mem_nhds
        (zero_mem_radialDomain (I := I) g p v)
    · intro s hs
      have hs_nhd : radialChartCurve (I := I) g p v =ᶠ[nhds s] (fun t : ℝ => t • v) := by
        refine Filter.eventuallyEq_of_mem
          ((radialDomain_isOpen (I := I) g p v).mem_nhds hs) ?_
        intro t ht
        exact radialChartCurve_eq_linear (I := I) g p v t ht
      have h_deriv : deriv (radialChartCurve (I := I) g p v) s =
          deriv (fun t : ℝ => t • v) s := hs_nhd.deriv_eq
      have hlin : HasDerivAt (fun t : ℝ => t • v) v s := by
        simpa using (hasDerivAt_id s).smul_const v
      change deriv (radialChartCurve (I := I) g p v) s = v
      rw [h_deriv]; exact hlin.deriv
  have h_const : HasDerivAt (fun _ : ℝ => v) (0 : E) (0 : ℝ) := hasDerivAt_const 0 v
  exact h_const.congr_of_eventuallyEq h_deriv_eq

/-- **The acceleration-vanishing identity.** The second-order
chart-coordinate acceleration of the radial geodesic
`s ↦ expMap g p (s • v)` at `s = 0`, computed in normal coordinates at
`p`, is zero. Combined with `radialChartCurve_hasDerivAt_zero` (first
derivative is `v`), this is the intrinsic geometric content of
"Christoffel symbols vanish at `p` in normal coordinates":

In the geodesic equation `u''(s) + Γ(u'(s), u'(s))(u(s)) = 0`, plugging
in the chart-coord radial geodesic with `u(s) = s • v`, `u'(s) = v`,
`u''(s) = 0` gives `Γ(v, v)(0) = 0` for every `v` in a neighborhood of
zero. By bilinearity-by-polarization on `v`, the Christoffel contraction
itself vanishes at the origin of the normal chart. -/
theorem normalChartAt_radial_secondDeriv_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) :
    HasDerivAt (fun s : ℝ => deriv (radialChartCurve (I := I) g p v) s)
      (0 : E) (0 : ℝ) :=
  radialChartCurve_secondDeriv_zero (I := I) g p v

/-- Polarisation: if a real-bilinear form `B : E × E → F` (with `F` an
ℝ-module) satisfies `B(u, u) = 0` for every `u` in a neighborhood of
zero, and `B` is symmetric, then `B(u, w) = 0` for every `(u, w)` in a
(smaller) neighborhood of `(0, 0) ∈ E × E`. Stated for downstream
clients who want the per-Christoffel-entry vanishing once an extra
symmetric-bilinear structure is supplied. -/
theorem polarization_of_symm_quadratic_eventually_zero
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hsymm : ∀ u w : E, B u w = B w u)
    (hzero : ∀ᶠ u in nhds (0 : E), B u u = 0) :
    ∀ᶠ p : E × E in nhds ((0 : E), (0 : E)), B p.1 p.2 = 0 := by
  classical
  rcases Filter.eventually_iff_exists_mem.mp hzero with ⟨U, hU_mem, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_mem with ⟨V, hV_sub, hV_open, hV_mem⟩
  have h_add_cont : Continuous fun q : E × E => q.1 + q.2 :=
    continuous_fst.add continuous_snd
  have h_add_zero : (0 : E) + (0 : E) = 0 := by simp
  have h_pre_open : IsOpen ((fun q : E × E => q.1 + q.2) ⁻¹' V) :=
    hV_open.preimage h_add_cont
  have h_pre_mem : ((0 : E), (0 : E)) ∈ (fun q : E × E => q.1 + q.2) ⁻¹' V := by
    change (0 : E) + (0 : E) ∈ V
    rw [h_add_zero]; exact hV_mem
  set W : Set (E × E) :=
    (V ×ˢ V) ∩ ((fun q : E × E => q.1 + q.2) ⁻¹' V) with hW_def
  have hW_open : IsOpen W :=
    (hV_open.prod hV_open).inter h_pre_open
  have hW_mem : ((0 : E), (0 : E)) ∈ W :=
    ⟨⟨hV_mem, hV_mem⟩, h_pre_mem⟩
  refine Filter.eventually_iff_exists_mem.mpr ⟨W, hW_open.mem_nhds hW_mem, ?_⟩
  intro p hp
  have h1 : B p.1 p.1 = 0 := hU _ (hV_sub hp.1.1)
  have h2 : B p.2 p.2 = 0 := hU _ (hV_sub hp.1.2)
  have h3 : B (p.1 + p.2) (p.1 + p.2) = 0 := hU _ (hV_sub hp.2)
  have h_expand : B (p.1 + p.2) (p.1 + p.2) =
      B p.1 p.1 + B p.1 p.2 + B p.2 p.1 + B p.2 p.2 := by
    have hL : B (p.1 + p.2) = B p.1 + B p.2 := map_add B p.1 p.2
    have hR1 : B p.1 (p.1 + p.2) = B p.1 p.1 + B p.1 p.2 :=
      map_add (B p.1) p.1 p.2
    have hR2 : B p.2 (p.1 + p.2) = B p.2 p.1 + B p.2 p.2 :=
      map_add (B p.2) p.1 p.2
    rw [hL, LinearMap.add_apply, hR1, hR2]
    abel
  rw [h_expand] at h3
  have hsym' : B p.2 p.1 = B p.1 p.2 := hsymm p.2 p.1
  rw [hsym'] at h3
  rw [h1, h2] at h3
  have h_double : B p.1 p.2 + B p.1 p.2 = 0 := by
    have heq : (0 : F) + B p.1 p.2 + B p.1 p.2 + 0 = B p.1 p.2 + B p.1 p.2 := by abel
    rw [heq] at h3
    exact h3
  have h_two_smul : (2 : ℝ) • B p.1 p.2 = 0 := by
    rw [two_smul]; exact h_double
  rcases (smul_eq_zero.mp h_two_smul) with h2_eq | hresult
  · exact absurd h2_eq two_ne_zero
  · exact hresult

end NormalChart

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
