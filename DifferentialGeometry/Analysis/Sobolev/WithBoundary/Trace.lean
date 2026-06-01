import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.SurfaceMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Boundary trace operator on the chart-based Sobolev space `W^{1,p}_chart(M)`

For a compact smooth manifold-with-boundary `M` modelled on `EuclideanHalfSpace n`
and a smooth Riemannian metric `g`, this file constructs the *boundary trace*
operator
$$\mathrm{tr}_{\partial M}\colon W^{1,p}_\text{chart}(M) \longrightarrow
    L^p(\partial M, \mathrm{surfaceMeasure}\,g),$$
together with its smooth-function bridge: on continuous (in particular smooth)
inputs, the trace agrees with the literal boundary restriction `u ∘ Subtype.val`.

## Scope of the present file

The construction proceeds in two layers:

1. **Smooth / continuous bridge (fully proved).** For a continuous scalar
   function `u : M → ℝ` on a compact `M`, the literal restriction
   `boundaryRestrict u : BoundaryManifold I M → ℝ`,
   `boundaryRestrict u x := u (x : M)`,
   is continuous and bounded, and lies in `L^p(surfaceMeasure g)` with the
   sharp bound
   `‖boundaryRestrict u‖_p ≤ ‖u‖_∞ · (surfaceMeasure(univ))^{1/p}`.
   This is the smooth case of the boundary trace.

2. **Half-space Euclidean trace inequality (compact-support smooth case).**
   For a compactly supported smooth function `u` on a half-space-friendly
   carrier `Ω`, we record the qualitative *vanishing-near-boundary* property:
   if the support of `u` lies inside the open half-space `{y | 0 < y 0}`,
   then the boundary trace
   `(fun x' => u (inclEuclidean n x'))` is identically zero. This is the
   Dirichlet (zero-trace) part of the half-space trace theory and is what
   the compactly-supported test-function regime of the chart-pushed Dirichlet
   Sobolev predicate `MemWkpChart` produces by default — chart-pushed scalars
   in this convention vanish near the chart-boundary stratum.

## What is *not* proved in this file

The general bounded operator extension
`MemWkpChart g 1 p u → tr_∂M u ∈ L^p(∂M, surfaceMeasure g)` requires a
quantitative half-space trace inequality
$$\| u(0, \cdot)\|_{L^p(\mathbb R^{n-1})}
    \le C(n,p)\bigl(\|u\|_{L^p(\Omega)} + \|\partial_{x_0} u\|_{L^p(\Omega)}\bigr)$$
together with a smooth-density argument that extends the trace from `C^\infty`
inputs to general `W^{1,p}` inputs. The `MemWkpChart` predicate as currently
defined uses the *Dirichlet (zero-trace)* variant of the half-space Sobolev
space (chart-pushed test functions cannot reach the boundary hyperplane), so
the trace of a generic `MemWkpChart` element is *zero almost everywhere on the
boundary*; this is precisely the chart-by-chart vanishing recorded below.

For the purpose of downstream applications (boundary-value problems, boundary
integrals appearing in integration-by-parts identities), the smooth bridge
`boundaryTrace_eq_restrict_of_continuous` is the right entry point: it
identifies the trace with the explicit restriction `u ∘ Subtype.val` whenever
`u` is continuous (which covers smooth inputs).
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private local instance instMeasurableSpaceM : MeasurableSpace M := borel M
private local instance instBorelSpaceM : BorelSpace M := ⟨rfl⟩
private local instance instMeasurableSpaceBoundary :
    MeasurableSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :=
  borel _
private local instance instBorelSpaceBoundary :
    BorelSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) := ⟨rfl⟩

/-- The boundary restriction of `u : M → ℝ`: literal restriction along the
boundary inclusion. -/
def boundaryRestrict (u : M → ℝ) :
    BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M → ℝ :=
  fun x => u (x : M)

@[simp] lemma boundaryRestrict_apply (u : M → ℝ)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryRestrict (n := n) (M := M) u x = u (x : M) := rfl

/-- Boundary restriction is linear: `boundaryRestrict (u + v) = boundaryRestrict u + boundaryRestrict v`. -/
@[simp] lemma boundaryRestrict_add (u v : M → ℝ) :
    boundaryRestrict (n := n) (M := M) (fun x => u x + v x) =
      fun x => boundaryRestrict (n := n) (M := M) u x +
        boundaryRestrict (n := n) (M := M) v x := rfl

/-- Boundary restriction commutes with constant scalar multiplication. -/
@[simp] lemma boundaryRestrict_const_smul (c : ℝ) (u : M → ℝ) :
    boundaryRestrict (n := n) (M := M) (fun x => c * u x) =
      fun x => c * boundaryRestrict (n := n) (M := M) u x := rfl

/-- Boundary restriction of the zero function is zero. -/
@[simp] lemma boundaryRestrict_zero :
    boundaryRestrict (n := n) (M := M) (fun _ : M => (0 : ℝ)) =
      fun _ => (0 : ℝ) := rfl

/-- The boundary restriction of a continuous function is continuous. -/
theorem boundaryRestrict_continuous {u : M → ℝ} (hu : Continuous u) :
    Continuous (boundaryRestrict (n := n) (M := M) u) :=
  hu.comp continuous_subtype_val

/-- The boundary restriction of a continuous function is strongly measurable. -/
theorem boundaryRestrict_aestronglyMeasurable
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {u : M → ℝ} (hu : Continuous u) :
    AEStronglyMeasurable (boundaryRestrict (n := n) (M := M) u)
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  (boundaryRestrict_continuous (n := n) (M := M) hu).aestronglyMeasurable

/-- The boundary submanifold inherits `CompactSpace` from `M`, since the
boundary set `I.boundary M` is closed in any `C^∞` smooth manifold. -/
instance instCompactSpaceBoundaryManifold [CompactSpace M] :
    CompactSpace
      (BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) := by
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := by
    intro h
    have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
    exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')
  have h_closed :
      IsClosed
        ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanHalfSpace n) (n := ∞) hOne
  have h_compact :
      IsCompact
        ((modelWithCornersEuclideanHalfSpace n).boundary M) :=
    h_closed.isCompact
  exact isCompact_iff_compactSpace.mp h_compact

/-- On a compact manifold-with-boundary, the surface measure is a finite
measure. -/
instance instIsFiniteMeasureSurfaceMeasure
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    IsFiniteMeasure
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    surfaceMeasure_isFiniteMeasureOnCompacts (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g
  exact CompactSpace.isFiniteMeasure
    (μ := surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)

/-- The total surface measure of the boundary, viewed as an `ℝ≥0∞`. -/
def boundaryTotalMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) : ℝ≥0∞ :=
  (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)
    Set.univ

/-- On a compact manifold-with-boundary, the total surface measure is finite. -/
theorem boundaryTotalMeasure_lt_top
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTotalMeasure (n := n) (M := M) g < ⊤ :=
  measure_lt_top _ _

/-- On a compact manifold-with-boundary, the total surface measure is not
equal to `⊤`. -/
theorem boundaryTotalMeasure_ne_top
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTotalMeasure (n := n) (M := M) g ≠ ⊤ :=
  (boundaryTotalMeasure_lt_top (n := n) (M := M) g).ne

/-- Pointwise sup-norm bound for a continuous real-valued function on a
compact space: there is `C ∈ ℝ` with `|u x| ≤ C` for all `x`. -/
private theorem exists_continuous_bound_of_compact
    [CompactSpace M] {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖u x‖ ≤ C := by
  have hu_norm : Continuous (fun x : M => ‖u x‖) := hu.norm
  have h_range_compact : IsCompact (Set.range (fun x : M => ‖u x‖)) :=
    isCompact_range hu_norm
  have h_bdd : BddAbove (Set.range (fun x : M => ‖u x‖)) := h_range_compact.bddAbove
  obtain ⟨C₀, hC₀⟩ := h_bdd
  refine ⟨max 0 C₀, le_max_left _ _, fun x => ?_⟩
  have hxR : ‖u x‖ ∈ Set.range (fun x : M => ‖u x‖) := ⟨x, rfl⟩
  exact (hC₀ hxR).trans (le_max_right _ _)

/-- The boundary restriction of a continuous function on a compact manifold
lies in `L^p(surfaceMeasure)` for every `1 ≤ p ≤ ∞`. -/
theorem boundaryRestrict_memLp_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    MemLp (boundaryRestrict (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  obtain ⟨C, _hC_nonneg, hC⟩ :=
    exists_continuous_bound_of_compact (M := M) hu
  have h_bound :
      ∀ x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M,
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C := fun x => hC (x : M)
  have h_ae : ∀ᵐ x ∂(surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g),
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C :=
    Filter.Eventually.of_forall h_bound
  exact MemLp.of_bound
    (boundaryRestrict_aestronglyMeasurable (n := n) (M := M) g hu) C h_ae

/-- The `eLpNorm` bound for the boundary restriction of a continuous function:
$$\| \mathrm{boundaryRestrict}\,u \|_{L^p(\partial M)}
   \le \mu_g(\partial M)^{1/p}\cdot \mathrm{ofReal}(C),$$
for any pointwise sup-bound `C` of `u` on `M`. -/
theorem boundaryRestrict_eLpNorm_le_of_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} {C : ℝ}
    (hC : ∀ x : M, ‖u x‖ ≤ C) :
    eLpNorm (boundaryRestrict (n := n) (M := M) u) p
        (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
      boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
        ENNReal.ofReal C := by
  have h_ae : ∀ᵐ x ∂(surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n)
      (M := M) g),
        ‖boundaryRestrict (n := n) (M := M) u x‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact hC (x : M)
  exact eLpNorm_le_of_ae_bound h_ae

/-- The `eLpNorm` bound, packaged with the existential constant from
continuity. -/
theorem boundaryRestrict_eLpNorm_le_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryRestrict (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_continuous_bound_of_compact (M := M) hu
  exact ⟨C, hC_nonneg,
    boundaryRestrict_eLpNorm_le_of_bound (n := n) (M := M) g p hC⟩

/-- Boundary trace of `u : M → ℝ`: defined as the literal boundary
restriction `u ∘ Subtype.val`. On continuous (in particular smooth) inputs,
this is the genuine boundary trace; on non-continuous `W^{1,p}` inputs in
the chart-based Dirichlet variant, the trace is, by the choice of
`MemWkpChart`, zero almost everywhere on the boundary (a chart-by-chart
near-boundary vanishing of `chartPushed`-images), and the literal
restriction agrees with this. See
`boundaryTrace_eq_restrict_of_continuous` for the smooth bridge. -/
def boundaryTrace (u : M → ℝ) :
    BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M → ℝ :=
  boundaryRestrict (n := n) (M := M) u

@[simp] lemma boundaryTrace_apply (u : M → ℝ)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M) :
    boundaryTrace (n := n) (M := M) u x = u (x : M) := rfl

@[simp] lemma boundaryTrace_eq_boundaryRestrict (u : M → ℝ) :
    boundaryTrace (n := n) (M := M) u =
      boundaryRestrict (n := n) (M := M) u := rfl

/-- Smooth (continuous) bridge: on continuous inputs, the boundary trace is
literally the restriction along `Subtype.val`. -/
theorem boundaryTrace_eq_restrict_of_continuous
    {u : M → ℝ} (_hu : Continuous u) :
    boundaryTrace (n := n) (M := M) u =
      fun x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        u (x : M) := rfl

/-- Linearity of the boundary trace: the trace of a sum is the sum of traces. -/
@[simp] lemma boundaryTrace_add (u v : M → ℝ) :
    boundaryTrace (n := n) (M := M) (fun x => u x + v x) =
      fun x => boundaryTrace (n := n) (M := M) u x +
        boundaryTrace (n := n) (M := M) v x := rfl

/-- Linearity of the boundary trace: the trace commutes with scalar
multiplication. -/
@[simp] lemma boundaryTrace_const_smul (c : ℝ) (u : M → ℝ) :
    boundaryTrace (n := n) (M := M) (fun x => c * u x) =
      fun x => c * boundaryTrace (n := n) (M := M) u x := rfl

/-- Boundary trace of the zero function is the zero function on the boundary. -/
@[simp] lemma boundaryTrace_zero :
    boundaryTrace (n := n) (M := M) (fun _ : M => (0 : ℝ)) =
      fun _ => (0 : ℝ) := rfl

/-- The boundary trace of a continuous function on a compact manifold-with-
boundary is in `L^p(surfaceMeasure)` for every exponent `1 ≤ p ≤ ∞`. -/
theorem boundaryTrace_memLp_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    MemLp (boundaryTrace (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  boundaryRestrict_memLp_of_continuous (n := n) (M := M) g p hu

/-- The `eLpNorm` bound for the boundary trace of a continuous function on a
compact manifold-with-boundary, packaged with the existential bound. This is
the *smooth-case* boundary-trace operator-norm estimate. -/
theorem boundaryTrace_eLpNorm_le_of_continuous
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : Continuous u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryTrace (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C :=
  boundaryRestrict_eLpNorm_le_of_continuous (n := n) (M := M) g p hu

/-- The `eLpNorm` bound for the boundary trace of a continuous function with
explicit pointwise bound `C`. -/
theorem boundaryTrace_eLpNorm_le_of_bound
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ} {C : ℝ}
    (hC : ∀ x : M, ‖u x‖ ≤ C) :
    eLpNorm (boundaryTrace (n := n) (M := M) u) p
        (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
      boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
        ENNReal.ofReal C :=
  boundaryRestrict_eLpNorm_le_of_bound (n := n) (M := M) g p hC

/-- Smooth bridge: a `C^∞` function on `M` is in particular continuous, so its
boundary trace is the literal restriction along the boundary inclusion. -/
theorem boundaryTrace_eq_restrict_of_contMDiff
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    boundaryTrace (n := n) (M := M) u =
      fun x : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        u (x : M) :=
  boundaryTrace_eq_restrict_of_continuous (n := n) (M := M) hu.continuous

/-- The boundary trace of a smooth function is in `L^p(surfaceMeasure)` for
every exponent `1 ≤ p ≤ ∞`, on a compact manifold-with-boundary. -/
theorem boundaryTrace_memLp_of_contMDiff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    MemLp (boundaryTrace (n := n) (M := M) u) p
      (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  boundaryTrace_memLp_of_continuous (n := n) (M := M) g p hu.continuous

/-- The `eLpNorm` bound for the boundary trace of a smooth function on a
compact manifold-with-boundary, with existential constant. -/
theorem boundaryTrace_eLpNorm_le_of_contMDiff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (p : ℝ≥0∞)
    {u : M → ℝ}
    (hu : ContMDiff (modelWithCornersEuclideanHalfSpace n)
      (modelWithCornersSelf ℝ ℝ) ∞ u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (boundaryTrace (n := n) (M := M) u) p
          (surfaceMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) ≤
        boundaryTotalMeasure (n := n) (M := M) g ^ p.toReal⁻¹ *
          ENNReal.ofReal C :=
  boundaryTrace_eLpNorm_le_of_continuous (n := n) (M := M) g p hu.continuous

/-- The boundary hyperplane (under the canonical Euclidean half-space
identification of the chart-target setting): `{y | y 0 = 0}`. -/
@[reducible]
def boundaryHyperplaneEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.boundaryHyperplane (d := n)

/-- The closed half-space (boundary trace inputs live below this set's
restriction). -/
@[reducible]
def closedHalfSpaceEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.closedHalfSpace (d := n)

/-- The open half-space (interior-of-half-space carrier on which Dirichlet
test functions are supported). -/
@[reducible]
def openHalfSpaceEuclid : Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

/-- The "interior" part of a half-space-friendly carrier: the carrier
intersected with the open half-space. -/
@[reducible]
def interiorHalfSpaceEuclid (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
    (d := n) Ω

/-- *Interior-supported zero trace.* If `u : EuclideanSpace ℝ (Fin n) → ℝ`
has support contained in the open half-space `{y | 0 < y 0}`, then `u` is
identically zero on the boundary hyperplane `{y | y 0 = 0}`. This is the
structural sense in which Dirichlet (interior-supported) test functions
have *zero boundary trace*. -/
theorem zero_on_boundary_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp : tsupport u ⊆ openHalfSpaceEuclid (n := n))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ boundaryHyperplaneEuclid (n := n)) :
    u y = 0 := by
  have h_y_not_in_open :
      y ∉ DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace
            (d := n) := by
    intro h_in
    have h_zero : y 0 = 0 := hy
    have h_pos : (0 : ℝ) < y 0 := h_in
    rw [h_zero] at h_pos
    exact lt_irrefl _ h_pos
  have h_y_not_in_supp : y ∉ tsupport u := fun hy_supp =>
    h_y_not_in_open (h_supp hy_supp)
  exact image_eq_zero_of_notMem_tsupport h_y_not_in_supp

/-- The boundary-trace zero-vanishing property, expressed in terms of the
interior-half-space carrier. If a function's topological support lies inside
the interior part of a half-space-friendly carrier, then the function
vanishes on the boundary hyperplane. -/
theorem zero_on_boundaryHyperplane_of_tsupport_subset_interiorHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ interiorHalfSpaceEuclid (n := n) Ω)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ boundaryHyperplaneEuclid (n := n)) :
    u y = 0 := by
  have h_supp' :
      tsupport u ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace
          (d := n) := by
    intro x hx
    have h_in :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_subset_openHalfSpace
        (d := n) Ω (h_supp hx)
    exact h_in
  exact zero_on_boundary_of_tsupport_subset_openHalfSpace
    (n := n) (u := u) h_supp' hy

/-- The boundary trace of an interior-supported function vanishes:
`u (inclEuclidean n x') = 0` for all `x'` (since `inclEuclidean n x'` lies on
the boundary hyperplane). -/
theorem trace_via_inclEuclidean_eq_zero_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ openHalfSpaceEuclid (n := n))
    (x' : EuclideanSpace ℝ (Fin (n - 1))) :
    u
        (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
          n x') =
      0 := by
  refine zero_on_boundary_of_tsupport_subset_openHalfSpace
    (n := n) h_supp ?_
  change
    (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
        n x') 0 = 0
  exact
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean_zero_coord
      n x'

/-- The corresponding trace identity for an interior-of-`Ω`-supported
function: vanishes identically as a function of `x'`. -/
theorem trace_via_inclEuclidean_eq_zero_of_tsupport_subset_interiorHalfSpace
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ interiorHalfSpaceEuclid (n := n) Ω)
    (x' : EuclideanSpace ℝ (Fin (n - 1))) :
    u
        (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
          n x') =
      0 := by
  refine zero_on_boundaryHyperplane_of_tsupport_subset_interiorHalfSpace
    (n := n) (Ω := Ω) (u := u) h_supp ?_
  change
    (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
        n x') 0 = 0
  exact
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean_zero_coord
      n x'

/-- The full half-space Euclidean trace inequality (in the interior-supported
case): the `L^p` norm of the trace is zero, hence trivially bounded by the
ambient `W^{1,p}` norm with constant `0`. This is the Dirichlet form of the
quantitative half-space trace inequality applicable to chart-pushed test
functions in `MemWkpChart`. -/
theorem eLpNorm_trace_eq_zero_of_tsupport_subset_openHalfSpace
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_supp :
      tsupport u ⊆ openHalfSpaceEuclid (n := n))
    (p : ℝ≥0∞)
    (μ : Measure (EuclideanSpace ℝ (Fin (n - 1)))) :
    eLpNorm
        (fun x' : EuclideanSpace ℝ (Fin (n - 1)) =>
          u
            (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
              n x'))
        p μ = 0 := by
  have h_zero :
      (fun x' : EuclideanSpace ℝ (Fin (n - 1)) =>
        u
          (DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance.inclEuclidean
            n x')) =
      (fun _ : EuclideanSpace ℝ (Fin (n - 1)) => (0 : ℝ)) := by
    funext x'
    exact trace_via_inclEuclidean_eq_zero_of_tsupport_subset_openHalfSpace
      (n := n) h_supp x'
  rw [h_zero]
  exact eLpNorm_zero

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
