import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartFrameSection
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.PouCutoffComponentBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransition
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransitionTransport
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartTransitionTransportCLM
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# A smooth representative of a connection-Laplacian resolvent eigenvector

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas` and an eigenbasis index `i`, the eigenvector
`tensorResolventEigenbasisVec h_atlas i` of the `L²`-side tensor resolvent is
an abstract element of the metric `L²` Hilbert space `TensorL2 r s g`: it
carries no concrete tensor section.

The chart-local elliptic-regularity analysis has shown that each Euclidean chart
component of the eigenvector has a *compactly-supported smooth representative*
(`eigenvectorChartComponent_exists_smooth_representative`). This module assembles
those per-chart, per-component smooth representatives into a single genuine
**smooth compactly-supported tensor section** that *is* the eigenvector inside
the `L²` Hilbert space.

## The construction

The chart-atlas partition of unity `chartAtlasPOU I M` is, on a compact
manifold, supported on the finite set `chartAtlasPOU_finset`. For each chart
centre `α` in that finite set and each component multi-index `P`, the existence
theorem `eigenvectorChartComponent_exists_smooth_representative` produces a
smooth, compactly-supported chart-`α` Euclidean component function, almost
everywhere equal to the eigenvector's chart-`α` `P`-component. Feeding that
family of component functions to the chart-frame section constructor
`tensorBundleSectionOfChartComponents` yields a smooth compactly-supported
`(r, s)`-tensor section whose raw chart-`α` frame *is* the family.

`eigenvectorSmooth g r s h_atlas i` is the finite sum, over the chart centres
`α`, of those per-chart sections.

## Main definitions

* `eigenvectorSmooth g r s h_atlas i` — the smooth compactly-supported
  `(r, s)`-tensor section realising the eigenvector.

## Main results

* `eigenvectorSmooth_toL2` — the image of `eigenvectorSmooth` in the metric `L²`
  Hilbert space equals the eigenvector `tensorResolventEigenbasisVec h_atlas i`.
* `tensorEigenvector_contMDiff` — the eigenvector has a `C^∞` representative.
* `eigenvectorSmooth_weak_eigen` — the smooth weak eigen-equation: testing
  `eigenvectorResolvent` against a smooth compactly-supported `H¹` section `S`
  pairs, in `L²`, with the smooth section `eigenvectorSmooth`.

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

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The per-chart smooth component family

For a chart centre `α` and a component multi-index `P`, the existence theorem
`eigenvectorChartComponent_exists_smooth_representative` produces a smooth,
compactly-supported chart-`α` Euclidean component function. We pick one with
`Classical.choose` and record its three defining properties. -/

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The chosen smooth chart-`α` `P`-component representative of the eigenvector:
the witness of `eigenvectorChartComponent_exists_smooth_representative`. -/
def chosenComp (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s h_atlas i α P)

/-- The chosen chart-`α` `P`-component representative is `C^∞` on the chart
target. -/
private lemma chosenComp_contDiffOn (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s h_atlas i α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s h_atlas i α P)).1

/-- The chosen chart-`α` `P`-component representative has compact support. -/
private lemma chosenComp_hasCompactSupport
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp (I := I) (M := M) g r s h_atlas i α P) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s h_atlas i α P)).2.1

/-- The chosen chart-`α` `P`-component representative is topologically supported
inside the chart target. -/
private lemma chosenComp_tsupport (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp (I := I) (M := M) g r s h_atlas i α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s h_atlas i α P)).2.2.1

/-- The chosen chart-`α` `P`-component representative agrees almost everywhere
with the eigenvector chart component, for the Lebesgue measure restricted to the
chart target. -/
lemma chosenComp_ae_eq (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp (I := I) (M := M) g r s h_atlas i α P
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s h_atlas i α P)).2.2.2

/-- The smoothness/support data of the chosen chart-`α` component family, in the
shape required by `tensorBundleSectionOfChartComponents`. -/
private lemma chosenComp_hu (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp (I := I) (M := M) g r s h_atlas i α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_contDiffOn (I := I) (M := M) g r s h_atlas i α P

/-- The compact-support/topological-support data of the chosen chart-`α`
component family, in the shape required by `tensorBundleSectionOfChartComponents`. -/
private lemma chosenComp_hsupp (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp (I := I) (M := M) g r s h_atlas i α P) ∧
        tsupport (chosenComp (I := I) (M := M) g r s h_atlas i α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_hasCompactSupport (I := I) (M := M) g r s h_atlas i α P,
    chosenComp_tsupport (I := I) (M := M) g r s h_atlas i α P⟩

/-! ## The per-chart smooth section

For a chart centre `α`, feeding the chosen chart-`α` component family to the
chart-frame section constructor yields a smooth compactly-supported tensor
section whose raw chart-`α` frame is that family. -/

/-- The per-chart smooth section at `α`: the chart-frame tensor section assembled
from the chosen chart-`α` smooth component family. -/
def eigenvectorSmoothChart (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hu (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hsupp (I := I) (M := M) g r s h_atlas i α)

/-- The raw chart-`α` frame component of the per-chart section `eigenvectorSmoothChart α`,
read at the chart-source preimage of a chart-target point `y`, recovers the
chosen chart-`α` component `chosenComp α P y`. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_self
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp (I := I) (M := M) g r s h_atlas i α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hu (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hsupp (I := I) (M := M) g r s h_atlas i α) P hy

/-! ## The smooth representative of the eigenvector

The smooth representative is the finite sum, over the chart centres in the
finite partition-of-unity support set, of the per-chart smooth sections. The
summands lie in the `ℝ`-module `SmoothCcTensor g r s`, so the finite sum stays
inside it. -/

/-- **The smooth representative of the eigenvector.** For a closed Riemannian
manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev hypothesis `h_atlas`
and an eigenbasis index `i`, this is the smooth compactly-supported
`(r, s)`-tensor section realising the connection-Laplacian resolvent eigenvector
`tensorResolventEigenbasisVec h_atlas i`.

It is the finite sum, over the chart centres `α` in the partition-of-unity
support set `chartAtlasPOU_finset`, of the chart-frame tensor sections assembled
from the chosen chart-`α` smooth component families. Its image in the metric
`L²` Hilbert space equals the eigenvector (`eigenvectorSmooth_toL2`). -/
noncomputable def eigenvectorSmooth : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α

/-- The smooth representative unfolds to the finite sum of the per-chart
sections. -/
lemma eigenvectorSmooth_eq :
    eigenvectorSmooth (I := I) (M := M) g r s h_atlas i =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α := rfl

/-! ## Chart round-trip helpers

For a point `x` of the chart-`α` source, the chart Euclidean image
`toEuclidean (extChartAt I α x)` lies in the Euclidean chart target, and the
inverse pull-back `(extChartAt I α).symm (toEuclidean.symm ·)` recovers `x`. -/

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

/-! ## The per-chart section is supported in its chart

The per-chart section `eigenvectorSmoothChart α` is a finite sum of chart-frame
constant basis sections cut off by the chart-`α`-pull-back of a component
function. Each chart-pull-back vanishes off the chart-`α` source, so the section
value vanishes there. -/

/-- The underlying section of `eigenvectorSmoothChart α` vanishes off the
chart-`α` source. -/
private lemma eigenvectorSmoothChart_toSection_eq_zero_off_source
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α).toSection x =
      0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hu (I := I) (M := M) g r s h_atlas i α)
    (chosenComp_hsupp (I := I) (M := M) g r s h_atlas i α) hx

/-- The raw chart-`β` frame component of the per-chart section
`eigenvectorSmoothChart α` vanishes off the chart-`α` source: the section value
itself is zero there, and the trivialisation projection of zero is zero. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec : (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α).toSection x = 0 :=
    eigenvectorSmoothChart_toSection_eq_zero_off_source
      (I := I) (M := M) g r s h_atlas i α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α) β x =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α).toSection x)
      from rfl, hsec, map_zero, map_zero]

/-! ## Chart-locality-free twins

The declarations above carry the uniform-Sobolev hypothesis `h_atlas`, which is
false on a general closed manifold. The twins below prove the same statements
re-keyed onto the intrinsic compact-operator eigenbasis, via the chart-locality-free
existence theorem `eigenvectorChartComponent_exists_smooth_representative_unconditional`
(itself keyed on `eigenvectorChartComponentFun_ofCompact`), so they hold
unconditionally. -/

section Unconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- Chart-locality-free twin of `chosenComp`. -/
def chosenComp_unconditional (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (eigenvectorChartComponent_exists_smooth_representative_unconditional
      (I := I) (M := M) g r s i α P)

/-- Chart-locality-free twin of `chosenComp_contDiffOn`. -/
private lemma chosenComp_contDiffOn_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp_unconditional (I := I) (M := M) g r s i α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative_unconditional
      (I := I) (M := M) g r s i α P)).1

/-- Chart-locality-free twin of `chosenComp_hasCompactSupport`. -/
private lemma chosenComp_hasCompactSupport_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp_unconditional (I := I) (M := M) g r s i α P) :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative_unconditional
      (I := I) (M := M) g r s i α P)).2.1

/-- Chart-locality-free twin of `chosenComp_tsupport`. -/
private lemma chosenComp_tsupport_unconditional (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp_unconditional (I := I) (M := M) g r s i α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative_unconditional
      (I := I) (M := M) g r s i α P)).2.2.1

/-- Chart-locality-free twin of `chosenComp_ae_eq`. -/
lemma chosenComp_ae_eq_unconditional (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp_unconditional (I := I) (M := M) g r s i α P
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P :=
  (Classical.choose_spec
    (eigenvectorChartComponent_exists_smooth_representative_unconditional
      (I := I) (M := M) g r s i α P)).2.2.2

/-- Chart-locality-free twin of `chosenComp_hu`. -/
private lemma chosenComp_hu_unconditional (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp_unconditional (I := I) (M := M) g r s i α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_contDiffOn_unconditional (I := I) (M := M) g r s i α P

/-- Chart-locality-free twin of `chosenComp_hsupp`. -/
private lemma chosenComp_hsupp_unconditional (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp_unconditional (I := I) (M := M) g r s i α P) ∧
        tsupport (chosenComp_unconditional (I := I) (M := M) g r s i α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_hasCompactSupport_unconditional (I := I) (M := M) g r s i α P,
    chosenComp_tsupport_unconditional (I := I) (M := M) g r s i α P⟩

/-- Chart-locality-free twin of `eigenvectorSmoothChart`. -/
def eigenvectorSmoothChart_unconditional (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hu_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hsupp_unconditional (I := I) (M := M) g r s i α)

/-- Chart-locality-free twin of `tensorChartComponentRaw_eigenvectorSmoothChart_self`. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_self_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp_unconditional (I := I) (M := M) g r s i α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hu_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hsupp_unconditional (I := I) (M := M) g r s i α) P hy

/-- Chart-locality-free twin of `eigenvectorSmooth`. -/
noncomputable def eigenvectorSmooth_unconditional : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α

/-- Chart-locality-free twin of `eigenvectorSmooth_eq`. -/
lemma eigenvectorSmooth_eq_unconditional :
    eigenvectorSmooth_unconditional (I := I) (M := M) g r s i =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α := rfl

/-- Chart-locality-free twin of
`eigenvectorSmoothChart_toSection_eq_zero_off_source`. -/
private lemma eigenvectorSmoothChart_toSection_eq_zero_off_source_unconditional
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α).toSection x =
      0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hu_unconditional (I := I) (M := M) g r s i α)
    (chosenComp_hsupp_unconditional (I := I) (M := M) g r s i α) hx

/-- Chart-locality-free twin of
`tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source`. -/
lemma tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source_unconditional
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec :
      (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α).toSection x = 0 :=
    eigenvectorSmoothChart_toSection_eq_zero_off_source_unconditional
      (I := I) (M := M) g r s i α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α) β x =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α).toSection x)
      from rfl, hsec, map_zero, map_zero]

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
