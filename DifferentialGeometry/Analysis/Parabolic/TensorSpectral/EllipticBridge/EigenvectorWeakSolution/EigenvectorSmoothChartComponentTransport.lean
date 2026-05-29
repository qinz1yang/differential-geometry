import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothChartComponentSupport
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothChartComponentTerm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartTransitionTransportCLM
import DifferentialGeometry.Analysis.Sobolev.Chart.TransitionQMP
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# Reconciliation of a single transport term of the smooth eigenvector section

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas` and an eigenbasis index `i`, the per-chart smooth section
`eigenvectorSmoothChart g r s h_atlas i γ` is a genuine smooth
compactly-supported `(r, s)`-tensor section realising the chart-`γ` piece of the
connection-Laplacian resolvent eigenvector `tensorResolventEigenbasisVec
h_atlas i`.

The canonical chart-`β` component of the smooth representative is governed,
chart by chart, by the abstract partition-of-unity transport sum of the
eigenvector. This file establishes the **single transport-term
reconciliation**: the per-`γ` term of the smooth-section side — a
transformation-law expression in the smooth transition coefficient
`transitionCoeff` and the raw chart-`γ` frame component of
`eigenvectorSmoothChart γ` — equals, almost everywhere on the chart-`β` `L²`
measure, the per-`γ` term of the eigenvector's transport sum, namely the
chart-transition transport `chartTransitionTransportCLM` applied to the
abstract chart-`γ` component.

## The mechanism

Both sides carry the common pushed partition-of-unity weight of `β`,
`chartPushedRaw I β (chartAtlasPOU I M β)`. The transport side unfolds, by
`chartTransitionTransportCLM_coeFn_aeEq`, into the chart-`β` pushforward of the
transport coefficient `transportCoeffManifold g r s γ β` — the product of the
two chart-kernel cutoffs and `transitionCoeff` — times the chart-transition
precomposition of the abstract chart-`γ` component.

The smooth-section side's second factor is the chart-`β` pushforward of the
`(r, s)`-tensor transformation-law term, in which the raw chart-`γ` frame
component of `eigenvectorSmoothChart γ` is, by
`tensorChartComponentRaw_eigenvectorSmoothChart_self`, the chosen smooth
chart-`γ` representative `chosenComp γ`, itself almost everywhere the
eigenvector's chart-`γ` component (`chosenComp_ae_eq`). That chart-`γ`
almost-everywhere identity is transported into the chart-`β`-precomposed
setting across `chartTransitionEuclid β γ` by
`chartTransitionEuclid_comp_ae_eq_restrict`.

The two chart-kernel cutoffs in the transport coefficient are redundant almost
everywhere. The chart-`γ` cutoff is `1` wherever the eigenvector's chart-`γ`
component is nonzero — the off-kernel vanishing
`eigenvectorChartComponentFun_ae_zero_off_chartPouKernel` — and the chart-`β`
cutoff is `1` wherever the common pushed partition-of-unity weight of `β` is
nonzero. The `if x ∈ (chartAt H γ).source` cutoff on the smooth-section side
matches the chart-overlap domain `chartOverlapEuclid β γ` of the chart
transition.

## Main result

* `eigenvectorSmoothChart_transport_term_aeEq` — the per-`γ`
  transformation-law term of the smooth section equals, almost everywhere on
  the chart-`β` `L²` measure and after the common pushed partition-of-unity
  weight, the per-`γ` term of the eigenvector's chart-transition transport sum.

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

/-! ## A measure-theoretic gluing helper

The two sides of the headline agree everywhere off the chart overlap
`chartOverlapEuclid β γ` and almost everywhere on it; the following helper
combines the two facts into an almost-everywhere identity on the full chart
`L²` measure. -/

/-- If two functions agree almost everywhere with respect to `μ.restrict s` and
agree everywhere off the measurable set `s`, then they agree almost everywhere
with respect to `μ` itself. -/
private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {s : Set X} (hs : MeasurableSet s)
    (h_restrict : f =ᵐ[μ.restrict s] h)
    (h_compl : ∀ x, x ∉ s → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (h_compl x hxs)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ s :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact hs.nullMeasurableSet

/-! ## The chart-overlap membership characterisation

For a point `y` of the Euclidean chart target of `β`, membership in the chart
overlap `chartOverlapEuclid β γ` is equivalent to the chart-`β` inverse image
of `y` lying in the chart-`γ` source. -/

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- A Euclidean chart-target point `y` of `β` lies in the chart overlap
`chartOverlapEuclid β γ` exactly when its chart-`β` inverse image lies in the
chart-`γ` source. -/
lemma mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
    (β γ : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    y ∈ chartOverlapEuclid (I := I) (M := M) β γ ↔
      (extChartAt I β).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H γ).source := by
  classical
  -- `z` is the chart-`β` inverse image of `y`; it lies in the chart-`β` source.
  set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hz_srcβ : z ∈ (chartAt H β).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy
  -- `y` is the chart-`β` Euclidean image of `z`.
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I β).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
    rw [hz_def, (extChartAt I β).right_inv hsymm_target]
    exact (toEuclidean (E := E)).apply_symm_apply y
  constructor
  · -- Overlap membership exhibits `y` as the chart-`β` image of an overlap
    -- point; injectivity of the chart on its source pins that point to `z`.
    rintro ⟨w, ⟨x, hx_in, hxw⟩, hwy⟩
    have hx_eq_z : x = z := by
      have hx_srcβ : x ∈ (extChartAt I β).source := by
        rw [extChartAt_source (I := I)]; exact hx_in.1
      rw [hz_def, ← hwy, ← hxw, (toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I β).left_inv hx_srcβ]
    rw [hx_eq_z] at hx_in
    exact hx_in.2
  · -- Conversely, `z` lies in both sources, and `y` is its chart-`β` image.
    intro hz_srcγ
    exact ⟨extChartAt I β z, ⟨z, ⟨hz_srcβ, hz_srcγ⟩, rfl⟩, hy_eq⟩

/-! ## The chart-kernel cutoff pushed to the Euclidean chart target

The chart-`γ` kernel cutoff `chartKernelCutoff γ`, pushed to the Euclidean
chart target of `γ`. On the partition-of-unity kernel `chartPouKernel γ` it is
identically `1`. -/

/-- The chart-`γ` kernel cutoff `chartKernelCutoff γ`, pushed to the Euclidean
chart target of `γ`. -/
private def chartKernelCutoffPushed (γ : M) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) γ
    (fun x => ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

/-- On the partition-of-unity kernel `chartPouKernel γ` the pushed chart-`γ`
kernel cutoff equals `1`: a kernel point is the chart-`γ` Euclidean image of a
point of the closed support of the partition-of-unity weight, where the
chart-kernel cutoff is `1`. -/
private lemma chartKernelCutoffPushed_eq_one_on_chartPouKernel
    (γ : M) {y : EuclN}
    (hy : y ∈ chartPouKernel (I := I) (M := M) γ) :
    chartKernelCutoffPushed (I := I) (M := M) γ y = 1 := by
  classical
  -- `y` is the chart-`γ` Euclidean image of a point `w` of the closed support
  -- of the partition-of-unity weight.
  rw [chartPouKernel] at hy
  obtain ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩ := hy
  -- The partition of unity is subordinate to the chart sources.
  have hw_srcγ : w ∈ (chartAt H γ).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) γ hw_supp
  have hw_extsrc : w ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]; exact hw_srcγ
  -- `y` lies in the Euclidean chart target of `γ`.
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) γ :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) γ
      ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩
  -- The chart-`γ` inverse image of `y` is `w`.
  have hsymm : (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w := by
    rw [← hvy, ← hwv, (toEuclidean (E := E)).symm_apply_apply,
      (extChartAt I γ).left_inv hw_extsrc]
  -- Evaluate the pushforward and use that the cutoff is `1` on the kernel.
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _ hy_target, hsymm]
  exact chartKernelCutoff_eqOn_one (I := I) (M := M) γ hw_supp

/-- For a point `z` of the chart-`γ` source, the pushed chart-`γ` kernel cutoff
read at the chart-`γ` Euclidean image of `z` recovers `chartKernelCutoff γ z`. -/
private lemma chartKernelCutoffPushed_toEuclidean_extChartAt
    (γ : M) {z : M} (hz : z ∈ (chartAt H γ).source) :
    chartKernelCutoffPushed (I := I) (M := M) γ
        ((toEuclidean (E := E)) (extChartAt I γ z)) =
      ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) γ hz]

/-! ## The chart-`γ` kernel-cutoff factorisation of the eigenvector component

Almost everywhere on the Euclidean chart target of `γ`, the eigenvector
chart-`γ` `Q`-component is unchanged by multiplication with the pushed
chart-`γ` kernel cutoff: where the component is nonzero it sits inside the
partition-of-unity kernel, where the pushed cutoff is `1`. -/

/-- The eigenvector chart-`γ` `Q`-component equals, almost everywhere on the
Lebesgue volume restricted to the Euclidean chart target of `γ`, the pushed
chart-`γ` kernel cutoff times itself. -/
private lemma eigenvectorChartComponentFun_ae_eq_chartKernelCutoffPushed_mul
    (γ : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i γ Q y) := by
  classical
  -- The partition-of-unity kernel is measurable.
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) γ) :=
    chartPouKernel_measurableSet (I := I) (M := M) γ
  -- On the kernel: the pushed cutoff is `1`, so the product is the component.
  have h_on_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∈ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i γ Q y := by
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [chartKernelCutoffPushed_eq_one_on_chartPouKernel (I := I) (M := M) γ hy,
      one_mul]
  -- Off the kernel: the component vanishes almost everywhere, so the product
  -- (the cutoff times zero) agrees with it.
  have h_off_raw :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i γ Q
  have h_off_restrict :
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q
        =ᵐ[((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
            (chartPouKernel (I := I) (M := M) γ)ᶜ]
        (fun _ : EuclN => (0 : ℝ)) := by
    have h_restrict_eq :
        ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
          (chartPouKernel (I := I) (M := M) γ)ᶜ =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ \
            chartPouKernel (I := I) (M := M) γ) := by
      rw [Measure.restrict_restrict hK_meas.compl, Set.inter_comm,
        ← Set.diff_eq]
    rw [h_restrict_eq]
    exact h_off_raw
  have h_off_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∉ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i γ Q y := by
    have h_imp := (ae_restrict_iff' hK_meas.compl).mp h_off_restrict
    filter_upwards [h_imp] with y hy hy_off
    have hy_zero : eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i γ Q y = 0 := hy hy_off
    rw [hy_zero, mul_zero]
  -- Combine the on-kernel and off-kernel facts.
  filter_upwards [h_on_K, h_off_K] with y hy_on hy_off
  by_cases hy_mem : y ∈ chartPouKernel (I := I) (M := M) γ
  · exact hy_on hy_mem
  · exact hy_off hy_mem

/-! ## The transported chart-`γ` almost-everywhere identities

The chart-`γ` almost-everywhere facts — the chosen-representative agreement and
the kernel-cutoff factorisation — are transported across the chart transition
`chartTransitionEuclid β γ` onto the chart overlap `chartOverlapEuclid β γ`. -/

/-- The chosen smooth chart-`γ` representative agrees, almost everywhere on the
chart overlap `chartOverlapEuclid β γ` after precomposition with the chart
transition `chartTransitionEuclid β γ`, with the eigenvector chart-`γ`
component. -/
private lemma chosenComp_comp_chartTransition_ae_eq
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => chosenComp (I := I) (M := M) g r s h_atlas i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  -- The chosen-representative agreement holds on the Euclidean chart target of
  -- `γ`; restrict it to the chart overlap and transport across the transition.
  have h_target := chosenComp_ae_eq (I := I) (M := M) g r s h_atlas i γ Q
  have h_overlap :
      chosenComp (I := I) (M := M) g r s h_atlas i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

/-- The eigenvector chart-`γ` component, precomposed with the chart transition
`chartTransitionEuclid β γ`, equals almost everywhere on the chart overlap
`chartOverlapEuclid β γ` the pushed chart-`γ` kernel cutoff (also precomposed)
times itself. -/
private lemma eigenvectorChartComponentFun_comp_chartTransition_ae_eq_cutoff_mul
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ
          (chartTransitionEuclid (I := I) (M := M) β γ y) *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i γ Q
          (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  -- The kernel-cutoff factorisation holds on the Euclidean chart target of `γ`;
  -- restrict it to the chart overlap and transport across the transition.
  have h_target :=
    eigenvectorChartComponentFun_ae_eq_chartKernelCutoffPushed_mul
      (I := I) (M := M) g r s h_atlas i γ Q
  have h_overlap :
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i γ Q y) :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

/-! ## The single transport-term reconciliation -/

open Classical in
/-- **Single transport-term reconciliation of the smooth eigenvector section.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, chart base points `β` and `γ`,
and component multi-indices `(P₀, Q)`, the per-`γ` term of the smooth-section
side — the chart-`β` pushforward of the `(r, s)`-tensor transformation-law
expression `transitionCoeff r s γ β P₀ Q · (raw chart-γ component of
eigenvectorSmoothChart γ)`, cut off to the chart-`γ` source — equals, almost
everywhere on the chart-`β` `L²` measure and after the common pushed
partition-of-unity weight of `β`, the per-`γ` term of the eigenvector's
chart-transition transport sum, namely `chartTransitionTransportCLM g r s γ β
P₀ Q` applied to the abstract chart-`γ` `Q`-component of the resolvent
eigenvector.

The transport operator unfolds via `chartTransitionTransportCLM_coeFn_aeEq`
into the chart-`β` pushforward of the transport coefficient
`transportCoeffManifold g r s γ β` times the chart-transition precomposition of
the abstract component; the two chart-kernel cutoffs in the transport
coefficient are redundant almost everywhere, against the common pushed
partition-of-unity weight (chart-`β` cutoff) and the off-kernel vanishing of
the eigenvector component (chart-`γ` cutoff). -/
theorem eigenvectorSmoothChart_transport_term_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      chartPushedRaw I β
        (fun x => if x ∈ (chartAt H γ).source then
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i γ)
              γ Q.1 Q.2 x
          else 0) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) γ Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
  classical
  -- Abbreviations: the common pushed partition-of-unity weight `W`, the
  -- smooth-section transformation-law factor `A`, the transport operator
  -- output `B`, and the explicit underlying-function form `RHS` of `B`.
  set W : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y with hW_def
  set A : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => if x ∈ (chartAt H γ).source then
      transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i γ)
          γ Q.1 Q.2 x
      else 0) y with hA_def
  set B : EuclN → ℝ := fun y =>
    ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) γ Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y with hB_def
  set RHS : EuclN → ℝ := fun y =>
    chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y *
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y) with hRHS_def
  -- Step 1: `B` unfolds, almost everywhere, into the explicit form `RHS`.
  have hB_eq : B =ᵐ[chartL2Measure (I := I) (M := M) β] RHS := by
    have h := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) g r s γ β
      P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) γ Q)
    -- The abstract-component coercion is, by definition, the eigenvector
    -- chart-`γ` component function.
    exact h.trans (Filter.EventuallyEq.of_eq rfl)
  -- Step 2: the headline goal reduces to `W · A =ᵐ W · RHS`.
  have h_goal : (fun y => W y * A y)
      =ᵐ[chartL2Measure (I := I) (M := M) β] (fun y => W y * RHS y) := by
    -- The chart overlap of `β` and `γ` is open, hence measurable.
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β γ) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β γ
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β γ) :=
      hΩ_open.measurableSet
    -- The chart `L²` measure restricted to the chart overlap is the plain
    -- Lebesgue volume restricted to the overlap (the overlap sits inside the
    -- chart target).
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ)]
    -- The on-overlap almost-everywhere identity.
    have h_on_overlap : (fun y => W y * A y)
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β γ)]
        (fun y => W y * RHS y) := by
      rw [h_restrict_eq]
      -- Almost-everywhere membership in the overlap, and the two transported
      -- chart-`γ` identities.
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β γ :=
        ae_restrict_mem hΩ_meas
      have h_cc := chosenComp_comp_chartTransition_ae_eq
        (I := I) (M := M) g r s h_atlas i β γ Q
      have h_kc :=
        eigenvectorChartComponentFun_comp_chartTransition_ae_eq_cutoff_mul
          (I := I) (M := M) g r s h_atlas i β γ Q
      filter_upwards [h_mem, h_cc, h_kc] with y hy_mem hy_cc hy_kc
      -- The chart-`β` inverse image `z` of `y` lies in both chart sources.
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcγ : z ∈ (chartAt H γ).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β γ hy_target).mp hy_mem
      -- The chart-`γ` Euclidean image of `z`.
      set zγ : EuclN := (toEuclidean (E := E)) (extChartAt I γ z) with hzγ_def
      -- `y` is the chart-`β` Euclidean image of `z`.
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      -- The chart transition carries `y` to the chart-`γ` image of `z`.
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β γ y = zγ := by
        rw [← hy_eq, hzγ_def]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β γ hz_srcβ
      -- Unfold `A y` on the chart target: the transformation-law term, in
      -- which the raw chart-`γ` component is the chosen smooth representative.
      have hA_y : A y =
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
            chosenComp (I := I) (M := M) g r s h_atlas i γ Q zγ := by
        rw [hA_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, if_pos hz_srcγ]
        congr 1
        have h_raw := tensorChartComponentRaw_eigenvectorSmoothChart_self
          (I := I) (M := M) g r s h_atlas i γ Q
          (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ
            hz_srcγ)
        rw [symm_toEuclidean_symm_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ] at h_raw
        rw [h_raw, hzγ_def]
      -- Unfold `RHS y` on the chart target: the transport coefficient at `z`
      -- times the eigenvector chart-`γ` component at `zγ`.
      have hRHS_y : RHS y =
          (((chartKernelCutoff (I := I) (M := M) β :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            ((chartKernelCutoff (I := I) (M := M) γ :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z) *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i γ Q zγ := by
        rw [hRHS_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hT_eq]
      -- The pushed chart-`γ` kernel cutoff at `zγ` is `chartKernelCutoff γ z`.
      have h_cutγ : chartKernelCutoffPushed (I := I) (M := M) γ zγ =
          ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
        rw [hzγ_def]
        exact chartKernelCutoffPushed_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ
      -- Rewrite the two transported chart-`γ` identities at the point `y`.
      rw [hT_eq] at hy_cc hy_kc
      rw [h_cutγ] at hy_kc
      -- `E` is the eigenvector chart-`γ` component at `zγ`.
      set Eγ : ℝ := eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i γ Q zγ with hEγ_def
      -- Replace the chosen representative by the eigenvector component.
      rw [hA_y, hy_cc, hRHS_y]
      -- The kernel-cutoff factorisation: `Eγ = chartKernelCutoff γ z · Eγ`.
      -- Case split on whether the common pushed weight `W y` vanishes.
      by_cases hWy : W y = 0
      · rw [hWy, zero_mul, zero_mul]
      · -- `W y ≠ 0` forces `z ∈ tsupport (chartAtlasPOU β)`, where the
        -- chart-`β` kernel cutoff is `1`.
        have hWy_val : W y =
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
          rw [hW_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def]
        have hz_pou : z ∈ tsupport
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          rw [hWy_val] at hWy
          exact hWy
        have h_cutβ : ((chartKernelCutoff (I := I) (M := M) β :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 1 :=
          chartKernelCutoff_eqOn_one (I := I) (M := M) β hz_pou
        rw [h_cutβ, one_mul]
        -- `hy_kc : Eγ = chartKernelCutoff γ z · Eγ`. Substitute one occurrence.
        rw [show transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z * Eγ =
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
              (((chartKernelCutoff (I := I) (M := M) γ :
                  C^∞⟮I, M; ℝ⟯) : M → ℝ) z * Eγ) from by rw [← hy_kc]]
        ring
    -- The off-overlap everywhere identity: both sides vanish.
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β γ →
        W y * A y = W y * RHS y := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · -- Inside the chart target: the chart-`β` inverse image avoids the
        -- chart-`γ` source, so both transformation-law factors vanish.
        set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcγ : z ∉ (chartAt H γ).source := by
          intro hz_srcγ
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β γ hy_target).mpr hz_srcγ)
        have hA_y : A y = 0 := by
          rw [hA_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, if_neg hz_notin_srcγ]
        have hRHS_y : RHS y = 0 := by
          rw [hRHS_def]
          simp only
          -- Off the chart-`γ` source the chart-`γ` kernel cutoff vanishes, so
          -- the transport coefficient — hence its pushforward — is zero.
          have h_cutγ_zero : ((chartKernelCutoff (I := I) (M := M) γ :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hz_notin_srcγ
                (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) γ h))
          have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
              (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y = 0 := by
            rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
              ← hz_def, transportCoeffManifold_apply, h_cutγ_zero]
            ring
          rw [h_coeff_zero, zero_mul]
        rw [hA_y, hRHS_y]
      · -- Outside the chart target the common pushed weight `W` vanishes.
        have hWy : W y = 0 := by
          rw [hW_def]
          simp only
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target
        rw [hWy, zero_mul, zero_mul]
    -- Glue the on-overlap and off-overlap facts.
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap
      h_off_overlap
  -- Assemble: the headline goal equals `W · A`, and `W · RHS =ᵐ W · B`.
  refine h_goal.trans ?_
  exact (Filter.EventuallyEq.refl _ W).mul hB_eq.symm

/-! ## Chart-locality-free twins

The declarations above are keyed on the chart-selection witness
`HasLocallyConstantChartAt`. We now build the chart-locality-free twins,
re-keying the eigenvector chart component onto the intrinsic-compactness
eigenvector `tensorResolventEigenbasisVec_ofCompact
(tensorResolventL2_isCompactOperator_intrinsic g r s) i` and consuming the
`_unconditional` / `_ofCompact` sibling objects. The originals above are kept
intact. The chart-geometry helpers `mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid`
and `chartKernelCutoffPushed*` carry no chart-selection witness and are reused
directly. -/

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_eq_chartKernelCutoffPushed_mul`. -/
private lemma eigenvectorChartComponentFun_ofCompact_ae_eq_chartKernelCutoffPushed_mul_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (γ : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i γ Q y) := by
  classical
  -- The partition-of-unity kernel is measurable.
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) γ) :=
    chartPouKernel_measurableSet (I := I) (M := M) γ
  -- On the kernel: the pushed cutoff is `1`, so the product is the component.
  have h_on_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∈ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i γ Q y := by
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [chartKernelCutoffPushed_eq_one_on_chartPouKernel (I := I) (M := M) γ hy,
      one_mul]
  -- Off the kernel: the component vanishes almost everywhere, so the product
  -- (the cutoff times zero) agrees with it.
  have h_off_raw :=
    eigenvectorChartComponentFun_ofCompact_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i γ Q
  have h_off_restrict :
      eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q
        =ᵐ[((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
            (chartPouKernel (I := I) (M := M) γ)ᶜ]
        (fun _ : EuclN => (0 : ℝ)) := by
    have h_restrict_eq :
        ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
          (chartPouKernel (I := I) (M := M) γ)ᶜ =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ \
            chartPouKernel (I := I) (M := M) γ) := by
      rw [Measure.restrict_restrict hK_meas.compl, Set.inter_comm,
        ← Set.diff_eq]
    rw [h_restrict_eq]
    exact h_off_raw
  have h_off_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∉ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i γ Q y := by
    have h_imp := (ae_restrict_iff' hK_meas.compl).mp h_off_restrict
    filter_upwards [h_imp] with y hy hy_off
    have hy_zero : eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i γ Q y = 0 := hy hy_off
    rw [hy_zero, mul_zero]
  -- Combine the on-kernel and off-kernel facts.
  filter_upwards [h_on_K, h_off_K] with y hy_on hy_off
  by_cases hy_mem : y ∈ chartPouKernel (I := I) (M := M) γ
  · exact hy_on hy_mem
  · exact hy_off hy_mem

/-- Chart-locality-free twin of `chosenComp_comp_chartTransition_ae_eq`. -/
private lemma chosenComp_comp_chartTransition_ae_eq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => chosenComp_unconditional (I := I) (M := M) g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  -- The chosen-representative agreement holds on the Euclidean chart target of
  -- `γ`; restrict it to the chart overlap and transport across the transition.
  have h_target := chosenComp_ae_eq_unconditional (I := I) (M := M) g r s i γ Q
  have h_overlap :
      chosenComp_unconditional (I := I) (M := M) g r s i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_comp_chartTransition_ae_eq_cutoff_mul`. -/
private lemma eigenvectorChartComponentFun_ofCompact_comp_chartTransition_ae_eq_cutoff_mul_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ
          (chartTransitionEuclid (I := I) (M := M) β γ y) *
        eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
          g r s i γ Q
          (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  -- The kernel-cutoff factorisation holds on the Euclidean chart target of `γ`;
  -- restrict it to the chart overlap and transport across the transition.
  have h_target :=
    eigenvectorChartComponentFun_ofCompact_ae_eq_chartKernelCutoffPushed_mul_unconditional
      (I := I) (M := M) g r s i γ Q
  have h_overlap :
      eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
          eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i γ Q y) :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

open Classical in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorSmoothChart_transport_term_aeEq`. -/
theorem eigenvectorSmoothChart_transport_term_aeEq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      chartPushedRaw I β
        (fun x => if x ∈ (chartAt H γ).source then
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i γ)
              γ Q.1 Q.2 x
          else 0) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) γ Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
  classical
  -- Abbreviations: the common pushed partition-of-unity weight `W`, the
  -- smooth-section transformation-law factor `A`, the transport operator
  -- output `B`, and the explicit underlying-function form `RHS` of `B`.
  set W : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y with hW_def
  set A : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => if x ∈ (chartAt H γ).source then
      transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i γ)
          γ Q.1 Q.2 x
      else 0) y with hA_def
  set B : EuclN → ℝ := fun y =>
    ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) γ Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y with hB_def
  set RHS : EuclN → ℝ := fun y =>
    chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y *
      eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y) with hRHS_def
  -- Step 1: `B` unfolds, almost everywhere, into the explicit form `RHS`.
  have hB_eq : B =ᵐ[chartL2Measure (I := I) (M := M) β] RHS := by
    have h := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) g r s γ β
      P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i) γ Q)
    -- The abstract-component coercion is, by definition, the eigenvector
    -- chart-`γ` component function.
    exact h.trans (Filter.EventuallyEq.of_eq rfl)
  -- Step 2: the headline goal reduces to `W · A =ᵐ W · RHS`.
  have h_goal : (fun y => W y * A y)
      =ᵐ[chartL2Measure (I := I) (M := M) β] (fun y => W y * RHS y) := by
    -- The chart overlap of `β` and `γ` is open, hence measurable.
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β γ) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β γ
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β γ) :=
      hΩ_open.measurableSet
    -- The chart `L²` measure restricted to the chart overlap is the plain
    -- Lebesgue volume restricted to the overlap (the overlap sits inside the
    -- chart target).
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ)]
    -- The on-overlap almost-everywhere identity.
    have h_on_overlap : (fun y => W y * A y)
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β γ)]
        (fun y => W y * RHS y) := by
      rw [h_restrict_eq]
      -- Almost-everywhere membership in the overlap, and the two transported
      -- chart-`γ` identities.
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β γ :=
        ae_restrict_mem hΩ_meas
      have h_cc := chosenComp_comp_chartTransition_ae_eq_unconditional
        (I := I) (M := M) g r s i β γ Q
      have h_kc :=
        eigenvectorChartComponentFun_ofCompact_comp_chartTransition_ae_eq_cutoff_mul_unconditional
          (I := I) (M := M) g r s i β γ Q
      filter_upwards [h_mem, h_cc, h_kc] with y hy_mem hy_cc hy_kc
      -- The chart-`β` inverse image `z` of `y` lies in both chart sources.
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcγ : z ∈ (chartAt H γ).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β γ hy_target).mp hy_mem
      -- The chart-`γ` Euclidean image of `z`.
      set zγ : EuclN := (toEuclidean (E := E)) (extChartAt I γ z) with hzγ_def
      -- `y` is the chart-`β` Euclidean image of `z`.
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      -- The chart transition carries `y` to the chart-`γ` image of `z`.
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β γ y = zγ := by
        rw [← hy_eq, hzγ_def]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β γ hz_srcβ
      -- Unfold `A y` on the chart target: the transformation-law term, in
      -- which the raw chart-`γ` component is the chosen smooth representative.
      have hA_y : A y =
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
            chosenComp_unconditional (I := I) (M := M) g r s i γ Q zγ := by
        rw [hA_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, if_pos hz_srcγ]
        congr 1
        have h_raw := tensorChartComponentRaw_eigenvectorSmoothChart_self_unconditional
          (I := I) (M := M) g r s i γ Q
          (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ
            hz_srcγ)
        rw [symm_toEuclidean_symm_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ] at h_raw
        rw [h_raw, hzγ_def]
      -- Unfold `RHS y` on the chart target: the transport coefficient at `z`
      -- times the eigenvector chart-`γ` component at `zγ`.
      have hRHS_y : RHS y =
          (((chartKernelCutoff (I := I) (M := M) β :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            ((chartKernelCutoff (I := I) (M := M) γ :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z) *
          eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i γ Q zγ := by
        rw [hRHS_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hT_eq]
      -- The pushed chart-`γ` kernel cutoff at `zγ` is `chartKernelCutoff γ z`.
      have h_cutγ : chartKernelCutoffPushed (I := I) (M := M) γ zγ =
          ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
        rw [hzγ_def]
        exact chartKernelCutoffPushed_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ
      -- Rewrite the two transported chart-`γ` identities at the point `y`.
      rw [hT_eq] at hy_cc hy_kc
      rw [h_cutγ] at hy_kc
      -- `Eγ` is the eigenvector chart-`γ` component at `zγ`.
      set Eγ : ℝ := eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i γ Q zγ with hEγ_def
      -- Replace the chosen representative by the eigenvector component.
      rw [hA_y, hy_cc, hRHS_y]
      -- The kernel-cutoff factorisation: `Eγ = chartKernelCutoff γ z · Eγ`.
      -- Case split on whether the common pushed weight `W y` vanishes.
      by_cases hWy : W y = 0
      · rw [hWy, zero_mul, zero_mul]
      · -- `W y ≠ 0` forces `z ∈ tsupport (chartAtlasPOU β)`, where the
        -- chart-`β` kernel cutoff is `1`.
        have hWy_val : W y =
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
          rw [hW_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def]
        have hz_pou : z ∈ tsupport
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          rw [hWy_val] at hWy
          exact hWy
        have h_cutβ : ((chartKernelCutoff (I := I) (M := M) β :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 1 :=
          chartKernelCutoff_eqOn_one (I := I) (M := M) β hz_pou
        rw [h_cutβ, one_mul]
        -- `hy_kc : Eγ = chartKernelCutoff γ z · Eγ`. Substitute one occurrence.
        rw [show transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z * Eγ =
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
              (((chartKernelCutoff (I := I) (M := M) γ :
                  C^∞⟮I, M; ℝ⟯) : M → ℝ) z * Eγ) from by rw [← hy_kc]]
        ring
    -- The off-overlap everywhere identity: both sides vanish.
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β γ →
        W y * A y = W y * RHS y := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · -- Inside the chart target: the chart-`β` inverse image avoids the
        -- chart-`γ` source, so both transformation-law factors vanish.
        set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcγ : z ∉ (chartAt H γ).source := by
          intro hz_srcγ
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β γ hy_target).mpr hz_srcγ)
        have hA_y : A y = 0 := by
          rw [hA_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, if_neg hz_notin_srcγ]
        have hRHS_y : RHS y = 0 := by
          rw [hRHS_def]
          simp only
          -- Off the chart-`γ` source the chart-`γ` kernel cutoff vanishes, so
          -- the transport coefficient — hence its pushforward — is zero.
          have h_cutγ_zero : ((chartKernelCutoff (I := I) (M := M) γ :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hz_notin_srcγ
                (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) γ h))
          have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
              (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y = 0 := by
            rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
              ← hz_def, transportCoeffManifold_apply, h_cutγ_zero]
            ring
          rw [h_coeff_zero, zero_mul]
        rw [hA_y, hRHS_y]
      · -- Outside the chart target the common pushed weight `W` vanishes.
        have hWy : W y = 0 := by
          rw [hW_def]
          simp only
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target
        rw [hWy, zero_mul, zero_mul]
    -- Glue the on-overlap and off-overlap facts.
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap
      h_off_overlap
  -- Assemble: the headline goal equals `W · A`, and `W · RHS =ᵐ W · B`.
  refine h_goal.trans ?_
  exact (Filter.EventuallyEq.refl _ W).mul hB_eq.symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
