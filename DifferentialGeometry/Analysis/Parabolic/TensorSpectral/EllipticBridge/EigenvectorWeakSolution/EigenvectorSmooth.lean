import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartFrameSection
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.PouCutoffComponentBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransition
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransitionTransport
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartTransitionTransportCLM

/-!
# A smooth representative of a connection-Laplacian resolvent eigenvector

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and an intrinsic
compact-operator eigenbasis index `i`, the eigenvector of the `L²`-side tensor
resolvent is an abstract element of the metric `L²` Hilbert space
`TensorL2 r s g`: it carries no concrete tensor section.

The chart-local elliptic-regularity analysis has shown that each Euclidean chart
component of the eigenvector has a *compactly-supported smooth representative*
(`eigenvectorChartComponent_exists_smooth_representative`). This
module assembles those per-chart, per-component smooth representatives into a
single genuine **smooth compactly-supported tensor section** that *is* the
eigenvector inside the `L²` Hilbert space.

## The construction

The chart-atlas partition of unity `chartAtlasPOU I M` is, on a compact
manifold, supported on the finite set `chartAtlasPOU_finset`. For each chart
centre `α` in that finite set and each component multi-index `P`, the existence
theorem `eigenvectorChartComponent_exists_smooth_representative`
produces a smooth, compactly-supported chart-`α` Euclidean component function,
almost everywhere equal to the eigenvector's chart-`α` `P`-component. Feeding
that family of component functions to the chart-frame section constructor
`tensorBundleSectionOfChartComponents` yields a smooth compactly-supported
`(r, s)`-tensor section whose raw chart-`α` frame *is* the family.

`eigenvectorSmooth g r s i` is the finite sum, over the chart
centres `α`, of those per-chart sections.

## Main definitions

* `eigenvectorSmooth g r s i` — the smooth compactly-supported
  `(r, s)`-tensor section realising the eigenvector.

## The identification argument

By the chart-component separation theorem `tensorL2_eq_of_chartComponent_eq`, it
suffices to match the canonical Euclidean chart components of `eigenvectorSmooth`
and of the eigenvector at every chart centre `β` and component multi-index `P₀`.

`eigenvectorSmooth` is a smooth section, so its canonical chart `β`-component is
the `L²` class of the concrete partition-of-unity-weighted Euclidean chart
component `tensorChartComponent g r s eigenvectorSmooth β P₀`. The eigenvector's
canonical chart `β`-component is governed, by the abstract
partition-of-unity transport law `tensorL2ChartComponent_ae_eq_pou_transport_sum`,
by a finite sum — over the transport chart centres `γ` and component
multi-indices `Q` — of the chart-transition transport of the eigenvector's
chart-`γ` `Q`-components.

The raw chart-`β` frame component of `eigenvectorSmooth = ∑_α S_α` is, by
additivity, the finite sum of the raw chart-`β` components of the summands
`S_α`. Each summand `S_α` is supported inside the chart-`α` source, so its raw
chart-`β` component vanishes off that source; on the chart overlap the
`(r, s)`-tensor transformation law `tensorChartComponentRaw_eq_transitionCoeff_sum`
expresses it through the raw chart-`α` components of `S_α`, which the section
constructor pins to the chart-`α` smooth representatives — themselves almost
everywhere the eigenvector's chart-`α` components. The chart-kernel cutoffs are
identically `1` wherever the relevant partition-of-unity weights are nonzero, so
the two finite sums coincide almost everywhere, and the chart components match.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For a point `x` of the chart-`α` source, the chart Euclidean image lies in
the Euclidean chart target. -/
lemma toEuclidean_extChartAt_mem_chartTargetEuclid
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartTargetEuclid (I := I) (M := M) α := by
  refine ⟨extChartAt I α x, ?_, rfl⟩
  exact (extChartAt I α).map_source
    (by rw [extChartAt_source (I := I)]; exact hx)

/-- For a point `x` of the chart-`α` source, the inverse pull-back of the chart
Euclidean image of `x` recovers `x`. -/
lemma symm_toEuclidean_symm_toEuclidean_extChartAt
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (extChartAt I α).symm
        ((toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) (extChartAt I α x))) = x := by
  rw [(toEuclidean (E := E)).symm_apply_apply]
  exact (extChartAt I α).left_inv
    (by rw [extChartAt_source (I := I)]; exact hx)

section Unconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- Chart-locality-free twin of `chosenComp`. -/
def chosenComp (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)

/-- Chart-locality-free twin of `chosenComp_contDiffOn`. -/
private lemma chosenComp_contDiffOn
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).1

/-- Chart-locality-free twin of `chosenComp_hasCompactSupport`. -/
private lemma chosenComp_hasCompactSupport
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.1

/-- Chart-locality-free twin of `chosenComp_tsupport`. -/
private lemma chosenComp_tsupport (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.2.1

/-- Chart-locality-free twin of `chosenComp_ae_eq`. -/
lemma chosenComp_ae_eq (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp (I := I) (M := M) g r s i α P
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s i α P)).2.2.2

/-- Chart-locality-free twin of `chosenComp_hu`. -/
private lemma chosenComp_hu (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s i α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_contDiffOn (I := I) (M := M) g r s i α P

/-- Chart-locality-free twin of `chosenComp_hsupp`. -/
private lemma chosenComp_hsupp (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp (I := I) (M := M) g r s i α P) ∧
        tsupport (chosenComp (I := I) (M := M) g r s i α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_hasCompactSupport (I := I) (M := M) g r s i α P,
    chosenComp_tsupport (I := I) (M := M) g r s i α P⟩

/-- Chart-locality-free twin of `eigenvectorSmoothChart`. -/
def eigenvectorSmoothChart (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α)

/-- Chart-locality-free twin of `tensorChartComponentRaw_eigenvectorSmoothChart_self`. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_self
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp (I := I) (M := M) g r s i α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) P hy

/-- Chart-locality-free twin of `eigenvectorSmooth`. -/
noncomputable def eigenvectorSmooth : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    eigenvectorSmoothChart (I := I) (M := M) g r s i α

/-- Chart-locality-free twin of `eigenvectorSmooth_eq`. -/
lemma eigenvectorSmooth_eq :
    eigenvectorSmooth (I := I) (M := M) g r s i =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        eigenvectorSmoothChart (I := I) (M := M) g r s i α := rfl

/-- Chart-locality-free twin of
`eigenvectorSmoothChart_toSection_eq_zero_off_source`. -/
private lemma eigenvectorSmoothChart_toSection_eq_zero_off_source
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x =
      0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s i α)
    (chosenComp_hu (I := I) (M := M) g r s i α)
    (chosenComp_hsupp (I := I) (M := M) g r s i α) hx

/-- Chart-locality-free twin of
`tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source`. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec :
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x = 0 :=
    eigenvectorSmoothChart_toSection_eq_zero_off_source
      (I := I) (M := M) g r s i α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α) β x =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((eigenvectorSmoothChart (I := I) (M := M) g r s i α).toSection x)
      from rfl, hsec, map_zero, map_zero]

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
