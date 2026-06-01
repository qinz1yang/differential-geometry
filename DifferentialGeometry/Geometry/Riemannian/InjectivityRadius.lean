import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import Mathlib.Data.ENNReal.Real

set_option linter.unusedSectionVars false

/-!
# Injectivity radius at a point

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, and any base point
`p : M`, the exponential map `expMap g p : T_p M → M` is a local
diffeomorphism at the zero vector (see
`Exponential/LocalDiffeomorphism.lean`). Consequently, there is an open
ball around `0 ∈ T_p M` on which `expMap g p` is injective.

The **injectivity radius at `p`** is the supremum, over `r : ℝ≥0∞`, of
the radii of balls in `T_p M ≃ E` on which `expMap g p` is injective. We
take the supremum in `ℝ≥0∞` so that a complete manifold (such as `ℝ^n`
with the flat metric) can have `injRadius g p = ∞`.

## Main results

* `injRadius g p` — the injectivity radius at `p`, as an element of
  `ℝ≥0∞`. The set used in the supremum is the family of radii `r` such
  that `expMap g p` is injective on the (extended) ball of radius `r`
  around `0 ∈ E`.

* `injRadius_pos` — for every `p`, the injectivity radius is strictly
  positive. This is the unconditional positivity statement.

* `mem_injRadiusSet_iff`, `injRadiusSet_downward_closed`,
  `injRadius_eq_sSup` and `injOn_expMap_eball_of_lt_injRadius` are the
  shape and monotonicity lemmas characterising the members of the
  supremum set and the defining injectivity property.

* `injRadius_iInf_pos_of_compact_of_lowerSemicontinuous` — on a compact
  manifold, when `p ↦ injRadius g p` is lower semicontinuous, the
  infimum is strictly positive. The lower-semicontinuity hypothesis is a
  separable assumption that follows from joint smoothness of the
  exponential map in `(p, v)`; the joint smoothness itself is not yet
  established at this point in the project, so we expose it as a
  hypothesis to be discharged elsewhere.

## Strategy

The supremum-set
`S g p = {r : ℝ≥0∞ | InjOn (expMap g p) (Metric.eball 0 r)}`
contains `0` (since `Metric.eball 0 0 = ∅`, on which every function is
vacuously injective). Positivity of the supremum follows from the
local diffeomorphism endpoint: `expMapDiffeo g p` is an injective
partial diffeomorphism whose source is an open neighborhood of `0`, so
it contains some `Metric.ball 0 r₀` with `r₀ > 0`. Translating the
real ball into an `eball` via `Metric.eball_ofReal` and using the
agreement `expMapDiffeo g p = expMap g p` on the source, we obtain
`ENNReal.ofReal r₀ ∈ S g p`, hence `injRadius g p ≥ ENNReal.ofReal r₀
> 0`.

On a compact manifold, given lower semicontinuity, the infimum of a
positive lower-semicontinuous function over a compact set is positive
by a standard compactness argument.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

section InjectivityRadius

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- The set of radii `r : ℝ≥0∞` such that `expMap g p`, viewed as a
function `E → M`, is injective on the (extended) open ball
`Metric.eball 0 r ⊆ E`. -/
def injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) : Set ℝ≥0∞ :=
  { r : ℝ≥0∞ |
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) }

/-- **The injectivity radius at `p ∈ M`.**

This is the supremum, taken in `ℝ≥0∞`, of all radii `r` such that
`expMap g p : E → M` is injective on the open ball of radius `r`
around the origin. We work in `ℝ≥0∞` so that `injRadius g p = ∞` is
permitted (e.g. the flat metric on `ℝ^n`). -/
def injRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup (injRadiusSet (I := I) g p)

/-- Membership in `injRadiusSet` is just the injectivity condition. -/
lemma mem_injRadiusSet_iff (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} :
    r ∈ injRadiusSet (I := I) g p ↔
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.eball (0 : E) r) := Iff.rfl

/-- `injRadiusSet` is downward closed: if injectivity holds on the ball of
radius `r`, it holds on the ball of any smaller radius. -/
lemma injRadiusSet_downward_closed (g : SmoothRiemannianMetric I M) (p : M)
    {r r' : ℝ≥0∞} (h : r' ≤ r) (hr : r ∈ injRadiusSet (I := I) g p) :
    r' ∈ injRadiusSet (I := I) g p := by
  refine InjOn.mono ?_ hr
  exact Metric.eball_subset_eball h

/-- The radius `0` is always in `injRadiusSet`. (The corresponding ball
is empty, so any function is vacuously injective on it.) -/
lemma zero_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : ℝ≥0∞) ∈ injRadiusSet (I := I) g p := by
  classical
  change InjOn _ (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

/-- `injRadiusSet` is nonempty. -/
lemma injRadiusSet_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (injRadiusSet (I := I) g p).Nonempty :=
  ⟨0, zero_mem_injRadiusSet (I := I) g p⟩

/-- Any element of `injRadiusSet` is below the injectivity radius. -/
lemma le_injRadius_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} (hr : r ∈ injRadiusSet (I := I) g p) :
    r ≤ injRadius (I := I) g p :=
  le_sSup hr

/-- The open `Metric.ball 0` of some positive radius is contained in
the source of `expMapDiffeo g p`. -/
lemma exists_metric_ball_subset_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.ball (0 : E) r₀ ⊆ (expMapDiffeo (I := I) g p).source := by
  classical
  have h_open : IsOpen (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).open_source
  have h_mem : (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
    zero_mem_expMapDiffeo_source (I := I) g p
  exact Metric.isOpen_iff.mp h_open (0 : E) h_mem

/-- On the source of `expMapDiffeo g p`, the function `expMapDiffeo g p`
coincides with `expMap g p`. In particular, since `expMapDiffeo g p`
is injective on its source (as a `PartialEquiv`/`PartialDiffeomorph`),
so is `expMap g p`. -/
lemma injOn_expMap_on_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expMapDiffeo (I := I) g p).source := by
  classical
  have h_inj_diffeo : InjOn (expMapDiffeo (I := I) g p)
      (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).toPartialEquiv.injOn
  intro v hv w hw hvw
  apply h_inj_diffeo hv hw
  rw [expMapDiffeo_apply_eq (I := I) g p hv,
      expMapDiffeo_apply_eq (I := I) g p hw]
  exact hvw

/-- **The key positive witness**: there exists `r₀ > 0` such that
`expMap g p` is injective on the metric ball of radius `r₀` around the
origin. -/
lemma exists_pos_injOn_metric_ball
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ :=
    exists_metric_ball_subset_expMapDiffeo_source (I := I) g p
  refine ⟨r₀, hr₀_pos, ?_⟩
  exact (injOn_expMap_on_expMapDiffeo_source (I := I) g p).mono hr₀_sub

/-- The same witness, packaged with `eball` (i.e. an `ℝ≥0∞` radius) so
that the result lies directly in `injRadiusSet`. -/
lemma exists_pos_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ≥0∞, 0 < r ∧ r ∈ injRadiusSet (I := I) g p := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_inj⟩ :=
    exists_pos_injOn_metric_ball (I := I) g p
  refine ⟨ENNReal.ofReal r₀, ?_, ?_⟩
  · exact ENNReal.ofReal_pos.mpr hr₀_pos
  · change InjOn _ (Metric.eball (0 : E) (ENNReal.ofReal r₀))
    rw [Metric.eball_ofReal]
    exact hr₀_inj

/-- The injectivity radius at every point `p : M` is strictly positive,
`0 < injRadius g p`. This holds unconditionally: `expMap g p` is a local
diffeomorphism at `0 ∈ T_p M`, hence injective on a ball of some positive
radius, so that radius witnesses a positive element of `injRadiusSet g p`. -/
theorem injRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < injRadius (I := I) g p := by
  classical
  obtain ⟨r, hr_pos, hr_mem⟩ := exists_pos_mem_injRadiusSet (I := I) g p
  exact lt_of_lt_of_le hr_pos (le_injRadius_of_mem (I := I) g p hr_mem)

/-- The injectivity radius is the supremum of `injRadiusSet`. -/
@[simp] lemma injRadius_eq_sSup (g : SmoothRiemannianMetric I M) (p : M) :
    injRadius (I := I) g p = sSup (injRadiusSet (I := I) g p) := rfl

/-- **The defining injectivity property**: `expMap g p` is injective on
any ball of radius strictly below the injectivity radius. -/
theorem injOn_expMap_eball_of_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ≥0∞}
    (hr : r < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  have hr_le_r' : r ≤ r' := le_of_lt hr_lt_r'
  exact (mem_injRadiusSet_iff (I := I) g p).mp hr'_mem |>.mono
    (Metric.eball_subset_eball hr_le_r')

/-- A real-radius corollary of the defining property: `expMap g p` is
injective on the (real) open ball of radius `r₀` whenever
`ENNReal.ofReal r₀ < injRadius g p`. -/
theorem injOn_expMap_ball_of_ofReal_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r₀ : ℝ}
    (hr : ENNReal.ofReal r₀ < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.ball (0 : E) r₀) := by
  classical
  have h := injOn_expMap_eball_of_lt_injRadius (I := I) g p hr
  rwa [Metric.eball_ofReal] at h

/-- On a compact nonempty manifold, the infimum `⨅ p, injRadius g p` of the
injectivity radius is strictly positive, under the hypothesis that
`p ↦ injRadius g p` is lower semicontinuous.

The lower-semicontinuity hypothesis is a genuine assumption on the statement:
it is the classical regularity ingredient (it follows from joint smoothness of
the exponential map in `(p, v)`, which is not yet available at this point in
the project). Given it, a lower-semicontinuous function on a compact nonempty
space attains its minimum at some `p₀` (via
`LowerSemicontinuousOn.exists_isMinOn`), and the infimum equals the pointwise
value there, which is positive by `injRadius_pos`. -/
theorem injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    0 < ⨅ p : M, injRadius (I := I) g p := by
  classical
  have h_lsc_on : LowerSemicontinuousOn (fun p : M => injRadius (I := I) g p)
      Set.univ := lowerSemicontinuousOn_univ_iff.mpr h_lsc
  obtain ⟨p₀, _hp₀_mem, h_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (f := fun p : M => injRadius (I := I) g p)
      (s := (Set.univ : Set M)) Set.univ_nonempty isCompact_univ h_lsc_on
  have h_iInf_eq : ⨅ p : M, injRadius (I := I) g p = injRadius (I := I) g p₀ := by
    apply le_antisymm
    · exact iInf_le _ p₀
    · refine le_iInf fun p => ?_
      have := h_min (Set.mem_univ p)
      simpa using this
  rw [h_iInf_eq]
  exact injRadius_pos (I := I) g p₀

/-- A useful packaging: under the same lower-semicontinuity hypothesis,
there exists a single positive real number `r₀` such that `expMap g p`
is injective on the open ball of radius `r₀` for every `p : M`. -/
theorem exists_uniform_injectivity_radius_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ p : M,
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  have h_inf_pos := injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (I := I) g h_lsc
  set R : ℝ≥0∞ := ⨅ p : M, injRadius (I := I) g p with hR_def
  by_cases hRtop : R = (⊤ : ℝ≥0∞)
  · refine ⟨1, one_pos, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_lt : ENNReal.ofReal 1 < injRadius (I := I) g p := by
      rw [hRtop] at h_le_inf
      have : ENNReal.ofReal 1 < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
      exact lt_of_lt_of_le this h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt
  · have hR_ne_top : R ≠ (⊤ : ℝ≥0∞) := hRtop
    have hR_pos : 0 < R := h_inf_pos
    have hR_toReal_pos : 0 < R.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hR_pos, lt_top_iff_ne_top.mpr hR_ne_top⟩
    refine ⟨R.toReal / 2, by positivity, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_ofReal_lt_R : ENNReal.ofReal (R.toReal / 2) < R := by
      have hhalf_lt : R.toReal / 2 < R.toReal := by linarith
      calc ENNReal.ofReal (R.toReal / 2)
          < ENNReal.ofReal R.toReal := by
            exact (ENNReal.ofReal_lt_ofReal_iff hR_toReal_pos).mpr hhalf_lt
        _ = R := ENNReal.ofReal_toReal hR_ne_top
    have h_lt : ENNReal.ofReal (R.toReal / 2) < injRadius (I := I) g p :=
      lt_of_lt_of_le h_ofReal_lt_R h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt

end InjectivityRadius

end Riemannian
end Geometry
end DifferentialGeometry

end
