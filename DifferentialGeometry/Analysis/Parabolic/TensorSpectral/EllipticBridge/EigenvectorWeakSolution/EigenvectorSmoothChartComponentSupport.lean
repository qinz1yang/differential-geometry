import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSEpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.PouCutoffComponentBridge
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# Off-support vanishing of the eigenvector partition-of-unity chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `Q`, the chart
`Q`-component `eigenvectorChartComponentFun g r s h_atlas i α Q` of the
resolvent eigenvector of the connection Laplacian is the function-coercion of the
abstract partition-of-unity chart component
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_atlas i) α Q`.

The committed off-kernel vanishing
`eigenvectorChartComponentFun_ae_zero_off_chartPouKernel` is keyed on the
**closed** partition-of-unity kernel `chartPouKernel α` — the chart image of
`tsupport (chartAtlasPOU α)`. A downstream chart-component-matching argument
instead needs the vanishing keyed on the locus where the pushed
partition-of-unity weight `chartPushedPouWeight α` vanishes, i.e. on the
complement of the **open** support of that weight.

## The support-version off-support vanishing

`eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero` is the
headline: almost everywhere on the Euclidean chart target, wherever the pushed
partition-of-unity weight `chartPushedPouWeight α` vanishes, so does the
eigenvector chart `Q`-component.

The mechanism is the committed partition-of-unity ↔ cutoff chart-component bridge
`tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` ("D.a"). Applied at the
abstract `L²` element `u := tensorResolventEigenbasisVec h_atlas i`, the bridge
gives, almost everywhere on the chart `L²` measure,

`eigenvectorChartComponentFun g r s h_atlas i α Q
   =ᵐ fun y => chartPushedPouWeight α y * (cutoff chart component) y`,

since `chartPushedPouWeight α` is by definition the chart pushforward
`chartPushedRaw α (chartAtlasPOU α)` of the partition-of-unity weight. Wherever
the first factor `chartPushedPouWeight α y` is zero the product vanishes, so the
eigenvector chart component vanishes there almost everywhere.

## Main results

* `eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero` — the
  implication-almost-everywhere off-support vanishing on the chart `L²` measure.
* `eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero` — the
  same statement as an almost-everywhere identity on the chart `L²` measure
  restricted to the zero locus of the pushed partition-of-unity weight.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The eigenvector chart component as a pushed-weight multiple of the cutoff
component

Specialising the committed partition-of-unity ↔ cutoff bridge
`tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` at the abstract `L²`
element `tensorResolventEigenbasisVec h_atlas i` rewrites the eigenvector chart
component, almost everywhere, as the pushed partition-of-unity weight
`chartPushedPouWeight α` times the cutoff chart component. -/

/-- The eigenvector chart `Q`-component equals, almost everywhere on the chart
`L²` measure, the pushed partition-of-unity weight `chartPushedPouWeight α` times
the cutoff chart `Q`-component of the resolvent eigenvector.

This is the partition-of-unity ↔ cutoff bridge
`tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` specialised at the abstract
`L²` element `tensorResolventEigenbasisVec h_atlas i`; the pushed
partition-of-unity weight `chartPushedPouWeight α` is, by definition, the chart
pushforward `chartPushedRaw α (chartAtlasPOU α)` appearing on the right of the
bridge. -/
private lemma eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedPouWeight (I := I) (M := M) α y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  -- `eigenvectorChartComponentFun` is the function-coercion of the abstract
  -- partition-of-unity chart component of the resolvent eigenvector; the D.a
  -- bridge rewrites that, almost everywhere, as `chartPushedRaw α (chartAtlasPOU
  -- α)` times the cutoff chart component. The pushed partition-of-unity weight
  -- `chartPushedPouWeight α` is by definition that chart pushforward.
  exact tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α Q

/-! ## The support-version off-support vanishing -/

/-- **Off-support vanishing of the eigenvector partition-of-unity chart
component (support version).**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `Q`, almost everywhere
on the chart `L²` measure `chartL2Measure α`, wherever the pushed
partition-of-unity weight `chartPushedPouWeight α` vanishes the eigenvector chart
`Q`-component `eigenvectorChartComponentFun g r s h_atlas i α Q` vanishes too.

Unlike the committed `eigenvectorChartComponentFun_ae_zero_off_chartPouKernel`,
which is keyed on the **closed** partition-of-unity kernel `chartPouKernel α`,
this is keyed on the zero locus of the pushed partition-of-unity weight — the
complement of its **open** support — which is what a downstream
chart-component-matching argument consumes.

The proof specialises the committed partition-of-unity ↔ cutoff chart-component
bridge `tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` at the abstract `L²`
element `tensorResolventEigenbasisVec h_atlas i`: the eigenvector chart
component equals, almost everywhere, the pushed partition-of-unity weight times
the cutoff chart component, so wherever the first factor is zero the product —
hence the eigenvector chart component — vanishes. -/
theorem eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α Q y = 0 := by
  -- The eigenvector chart component is, almost everywhere, the pushed
  -- partition-of-unity weight times the cutoff chart component.
  filter_upwards [eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
    (I := I) (M := M) g r s h_atlas i α Q] with y hy hy_zero
  -- Where the weight is zero the product is zero.
  rw [hy, hy_zero, zero_mul]

/-- **Off-support vanishing of the eigenvector partition-of-unity chart component
(restricted-measure version).**

The eigenvector chart `Q`-component `eigenvectorChartComponentFun g r s h_atlas
i α Q` is, almost everywhere on the chart `L²` measure restricted to the zero
locus `{y | chartPushedPouWeight α y = 0}` of the pushed partition-of-unity
weight, equal to the zero function.

This is the restricted-measure repackaging of
`eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero`: the
implication-almost-everywhere statement on the full chart `L²` measure is
equivalent to the almost-everywhere vanishing on the measure restricted to the
zero locus of the pushed partition-of-unity weight. -/
theorem eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- The zero locus of the pushed partition-of-unity weight is measurable: the
  -- pushed weight is a measurable function (chart pushforward of the `C^∞`
  -- partition-of-unity weight).
  have h_meas : MeasurableSet
      {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0} :=
    measurableSet_eq_fun (chartPushedPouWeight_measurable (I := I) (M := M) α)
      measurable_const
  -- Translate the implication-a.e. statement on the full measure to an a.e.
  -- identity on the measure restricted to the zero locus.
  rw [Filter.EventuallyEq, ae_restrict_iff' h_meas]
  filter_upwards [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s h_atlas i α Q] with y hy hy_zero
  exact hy hy_zero

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α Q y = 0 :=
  eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s h_atlas i α Q

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (I := I) (M := M) g r s h_atlas i α Q

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations above are keyed on the chart-selection witness
`HasLocallyConstantChartAt`. We now build the chart-locality-free twins, re-keying
the eigenvector chart component onto the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec_ofCompact` via the canonical unconditional chart
component `eigenvectorChartComponentFun_unconditional`. The originals above are
kept intact. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff`. -/
private lemma eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedPouWeight (I := I) (M := M) α y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  -- `eigenvectorChartComponentFun_unconditional` is the function-coercion of the
  -- abstract partition-of-unity chart component of the intrinsic eigenbasis
  -- vector; the D.a bridge rewrites that, almost everywhere, as
  -- `chartPushedRaw α (chartAtlasPOU α)` times the cutoff chart component. The
  -- pushed partition-of-unity weight `chartPushedPouWeight α` is by definition
  -- that chart pushforward.
  exact tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i) α Q

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero`. -/
theorem eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 := by
  -- The eigenvector chart component is, almost everywhere, the pushed
  -- partition-of-unity weight times the cutoff chart component.
  filter_upwards
    [eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff_unconditional
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  -- Where the weight is zero the product is zero.
  rw [hy, hy_zero, zero_mul]

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero`. -/
theorem eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- The zero locus of the pushed partition-of-unity weight is measurable: the
  -- pushed weight is a measurable function (chart pushforward of the `C^∞`
  -- partition-of-unity weight).
  have h_meas : MeasurableSet
      {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0} :=
    measurableSet_eq_fun (chartPushedPouWeight_measurable (I := I) (M := M) α)
      measurable_const
  -- Translate the implication-a.e. statement on the full measure to an a.e.
  -- identity on the measure restricted to the zero locus.
  rw [Filter.EventuallyEq, ae_restrict_iff' h_meas]
  filter_upwards
    [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero_unconditional
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  exact hy hy_zero

/-! ## Sanity tests (chart-locality-free) -/

section ElaborationTestsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 :=
  eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero_unconditional
    (I := I) (M := M) g r s i α Q

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero_unconditional
    (I := I) (M := M) g r s i α Q

end ElaborationTestsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
