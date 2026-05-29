import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothChartComponentTransport
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.PouCutoffComponentBridge
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# The chart component of the smooth eigenvector representative

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas` and an eigenbasis index `i`, the smooth representative
`eigenvectorSmooth g r s h_atlas i` is the finite partition-of-unity sum, over
the chart centres in `chartAtlasPOU_finset`, of the per-chart smooth sections
`eigenvectorSmoothChart g r s h_atlas i α`.

This file proves the **chart-component equality**: the canonical Euclidean
chart-`β` `P₀`-component of `eigenvectorSmooth` equals — as an element of the
chart `L²` space — the canonical chart-`β` `P₀`-component of the
connection-Laplacian resolvent eigenvector `tensorResolventEigenbasisVec
h_atlas i`.

## The argument

**Left side.** `eigenvectorSmooth` is the finite sum `∑_α eigenvectorSmoothChart
α`; the canonical chart component is continuous-linear in its abstract `L²`
argument (it factors through the smooth-section embedding and
`tensorL2ChartComponentCLM`), so additivity turns its chart-`β` `P₀`-component
into the finite sum, over `α`, of the chart-`β` `P₀`-components of the
summands. Each summand component is rewritten, as a function, by the per-chart
component formula `eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq`.

**Right side.** The eigenvector's canonical chart-`β` `P₀`-component is
rewritten by the abstract partition-of-unity transport law
`tensorL2ChartComponent_ae_eq_pou_transport_sum`: the chart-pushed
partition-of-unity weight of `β` times a finite double sum, over the transport
chart centres `γ` and component multi-indices `Q`, of the chart-transition
transport of the eigenvector's chart-`γ` `Q`-components.

**Matching.** Each per-chart summand of the left side, after pushing the chart
pushforward through the inner component sum, is reconciled per `(α, Q)` by the
single transport-term identity `eigenvectorSmoothChart_transport_term_aeEq`
with the chart-transition transport term of the right side. The index sets
differ — the left sum ranges over `chartAtlasPOU_finset`, the right over
`transportChartCenters β` — but the transport chart centres are a subset of the
partition-of-unity support set, and for a chart centre outside the transport
set the corresponding transport term vanishes almost everywhere: where the
chart-`β` cutoff is nonzero the partition-of-unity weight of that centre
vanishes, hence so does the eigenvector chart component there (the off-support
vanishing), and elsewhere the transport coefficient itself carries the
vanishing chart-`β` cutoff factor.

## Main result

* `eigenvectorSmooth_tensorL2ChartComponent_eq` — the chart-`β` `P₀`-component
  of the smooth representative equals the chart-`β` `P₀`-component of the
  resolvent eigenvector, as elements of the chart `L²` space.

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

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## A measure-theoretic gluing helper

The two sides of an a.e. identity that agree everywhere off a measurable set and
almost everywhere on it agree almost everywhere on the full measure. -/

/-- If two functions agree almost everywhere with respect to `μ.restrict s` and
agree everywhere off the measurable set `s`, then they agree almost everywhere
with respect to `μ` itself. -/
private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {t : Set X} (ht : MeasurableSet t)
    (h_restrict : f =ᵐ[μ.restrict t] h)
    (h_compl : ∀ x, x ∉ t → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ t := by
    intro x hx
    by_contra hxt
    exact hx (h_compl x hxt)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ t :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact ht.nullMeasurableSet

/-! ## The transport chart centres lie in the partition-of-unity support set

A transport chart centre `γ ∈ transportChartCenters β` has, by definition, a
partition-of-unity weight whose support meets the chart-`β` cutoff support; in
particular that support is nonempty, so `γ` belongs to the partition-of-unity
support set `chartAtlasPOU_finset`. -/

/-- Every transport chart centre of `β` belongs to the partition-of-unity
support set. -/
private lemma transportChartCenters_subset_chartAtlasPOU_finset (β : M) :
    transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) := by
  intro γ hγ
  rw [mem_transportChartCenters] at hγ
  rw [chartAtlasPOU_finset_mem]
  exact hγ.mono (Set.inter_subset_left)

/-! ## The chart pushforward of the per-chart component formula

The per-chart component formula `eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq`
presents the chart-`β` component of `eigenvectorSmoothChart α` as the chart-`β`
pushforward of the partition-of-unity weight times the chart-`β` pushforward of
an `if`-gated component sum. This subsection moves the chart pushforward through
the inner finite sum, so the single-term transport reconciliation
`eigenvectorSmoothChart_transport_term_aeEq` applies per component
multi-index. -/

/-- An `if`-gated finite sum equals the finite sum of the `if`-gated summands:
both sides are the sum when the condition holds and `0` otherwise. -/
private lemma ite_finsetSum_eq_finsetSum_ite
    {ι : Type*} (t : Finset ι) (p : Prop) [Decidable p] (f : ι → ℝ) :
    (if p then ∑ a ∈ t, f a else 0) = ∑ a ∈ t, (if p then f a else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp, Finset.sum_const_zero]

open Classical in
/-- The chart-`β` pushforward of the `if`-gated chart-`α` transformation-law
component sum, evaluated at a Euclidean point `y`, equals the finite sum, over
component multi-indices `Q`, of the chart-`β` pushforwards of the single
`if`-gated transformation-law terms. -/
private lemma chartPushedRaw_ite_transitionSum_eq_finsetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    chartPushedRaw I β
        (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                α Q.1 Q.2 x
          else 0) y =
      ∑ Q : TensorCompIdx (E := E) r s,
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                α Q.1 Q.2 x
          else 0) y := by
  classical
  -- Move the `if` inside the finite sum, then push the chart pushforward
  -- through the resulting finite sum.
  have h_ite :
      (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                α Q.1 Q.2 x
          else 0) =
        fun x => ∑ Q : TensorCompIdx (E := E) r s,
          (if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                α Q.1 Q.2 x
          else 0) := by
    funext x
    exact ite_finsetSum_eq_finsetSum_ite (Finset.univ) _ _
  rw [h_ite]
  exact chartPushedRaw_finsetSum (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => if x ∈ (chartAt H α).source then
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
          α Q.1 Q.2 x
    else 0) y

/-! ## The per-chart summand as a transport sum

Each per-chart summand of the smooth representative's chart-`β` component — the
canonical chart-`β` component of `eigenvectorSmoothChart α` — equals, almost
everywhere, the chart-pushed partition-of-unity weight of `β` times the finite
sum, over component multi-indices `Q`, of the chart-transition transport of the
eigenvector's chart-`α` `Q`-components. -/

/-- The canonical chart-`β` `P₀`-component of the per-chart smooth section
`eigenvectorSmoothChart α` equals, almost everywhere on the chart-`β` `L²`
measure, the chart-pushed partition-of-unity weight of `β` times the finite sum,
over component multi-indices `Q`, of the chart-transition transport of the
resolvent eigenvector's chart-`α` `Q`-components. -/
private lemma eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
  classical
  -- Start from the per-chart component formula ("D-i").
  refine (eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq
    (I := I) (M := M) g r s h_atlas i α β P₀).trans ?_
  -- Push the chart pushforward through the inner component sum, so the per-`Q`
  -- transport reconciliation applies.
  have h_push : ∀ y : EuclN,
      chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                  α Q.1 Q.2 x
            else 0) y =
        ∑ Q : TensorCompIdx (E := E) r s,
          (chartPushedRaw I β
              (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
            chartPushedRaw I β
              (fun x => if x ∈ (chartAt H α).source then
                transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                  tensorChartComponentRaw (I := I) (M := M) g r s
                    (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                    α Q.1 Q.2 x
              else 0) y) := by
    intro y
    rw [chartPushedRaw_ite_transitionSum_eq_finsetSum
      (I := I) (M := M) g r s h_atlas i α β P₀ y, Finset.mul_sum]
  -- The right side of "D-i" therefore becomes a finite sum of single transport
  -- terms; reconcile each by the single transport-term identity ("File 2").
  have h_terms : ∀ Q : TensorCompIdx (E := E) r s,
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                α Q.1 Q.2 x
          else 0) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) :=
    fun Q => eigenvectorSmoothChart_transport_term_aeEq
      (I := I) (M := M) g r s h_atlas i β α P₀ Q
  -- Assemble: rewrite the product as a finite sum, then sum the per-`Q`
  -- reconciliations, then pull the partition-of-unity weight back out.
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_terms Q)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq (funext h_push)) ?_
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.mul_sum]

/-! ## The off-transport per-chart summand vanishes

For a chart centre `α` outside the transport set of `β`, the per-chart transport
sum vanishes almost everywhere. The transport coefficient confines each transport
term to the overlap of the chart-`α` and chart-`β` cutoff supports; where the
chart-`β` cutoff is nonzero the chart-`α` partition-of-unity weight is zero —
since `α` is not a transport chart centre — and there the off-support vanishing
of the eigenvector chart component kills the transported component. -/

/-- The chart-pushed partition-of-unity weight of `α`, read at the chart-`α`
Euclidean image of a chart-`α` source point `z`, recovers the partition-of-unity
weight `chartAtlasPOU α` at `z`. -/
private lemma chartPushedPouWeight_toEuclidean_extChartAt
    (α : M) {z : M} (hz : z ∈ (chartAt H α).source) :
    chartPushedPouWeight (I := I) (M := M) α
        ((toEuclidean (E := E)) (extChartAt I α z)) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartPushedPouWeight
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α hz]

/-- The eigenvector chart-`α` `Q`-component, gated to the zero locus of the
chart-pushed partition-of-unity weight of `α`, vanishes almost everywhere on the
chart-`α` `L²` measure: where the weight is nonzero the `if` evaluates to `0`,
and where it is zero the off-support vanishing kills the component. -/
private lemma eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q y
      else 0)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  filter_upwards [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s h_atlas i α Q] with y hy
  by_cases hw : chartPushedPouWeight (I := I) (M := M) α y = 0
  · rw [if_pos hw]
    exact hy hw
  · rw [if_neg hw]

/-- The single transport term `chartTransitionTransportCLM g r s α β P₀ Q
(eigenvector chart-`α` `Q`-component)` vanishes almost everywhere on the
chart-`β` `L²` measure whenever `α` is not a transport chart centre of `β`.

The transported function is the chart-`β` pushforward of the transport
coefficient `transportCoeffManifold g r s α β P₀ Q` times the chart-transition
precomposition of the eigenvector chart-`α` `Q`-component. Off the chart overlap
of `β` and `α` the transport coefficient — which carries the chart-`α` cutoff
factor — vanishes. On the overlap, at each point the chart-`β` cutoff is either
zero — and then the transport coefficient, carrying that factor, vanishes — or
nonzero; in the latter case the chart-`α` partition-of-unity weight is zero
there, because `α` is not a transport chart centre, so the off-support vanishing
of the eigenvector chart component (transported across the chart transition)
kills the precomposed component. -/
private lemma chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ Q : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- The transported function: chart-`β` pushforward of the transport
  -- coefficient times the chart-transition precomposition of the chart-`α`
  -- component.
  have h_coeFn := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M)
    g r s α β P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α Q)
  refine h_coeFn.trans ?_
  -- The transport coefficient is supported in the overlap of the two chart
  -- sources; the chart overlap `chartOverlapEuclid β α` is open, hence
  -- measurable.
  have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) β α
  have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
    hΩ_open.measurableSet
  -- The chart-`β` `L²` measure restricted to the chart overlap is the plain
  -- volume restricted to the overlap.
  have h_restrict_eq :
      (chartL2Measure (I := I) (M := M) β).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) =
      (volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) := by
    rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
      Set.inter_eq_left.mpr
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]
  -- On the overlap: the gated off-support vanishing of the eigenvector chart
  -- component, transported across the chart transition.
  have h_on_overlap :
      (fun y => chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y))
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_restrict_eq]
    -- The gated chart-`α` component vanishes a.e. on the chart-`α` `L²`
    -- measure; restrict it to the chart overlap of `α` with `β`, then transport
    -- across the chart transition `chartTransitionEuclid β α`.
    have h_gate_target :=
      eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero
        (I := I) (M := M) g r s h_atlas i α Q
    have h_gate_overlap :
        (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α Q y
          else 0)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartOverlapEuclid (I := I) (M := M) α β)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [chartL2Measure] at h_gate_target
      exact ae_mono (Measure.restrict_mono_set _
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β))
        h_gate_target
    have h_gate_transport := chartTransitionEuclid_comp_ae_eq_restrict
      (I := I) (M := M) β α h_gate_overlap
    -- Almost-everywhere membership in the overlap.
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α)),
        y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
      ae_restrict_mem hΩ_meas
    filter_upwards [h_mem, h_gate_transport] with y hy_mem hy_gate
    -- The chart-`β` inverse image `z` of `y` lies in both chart sources.
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
    set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
      with hz_def
    have hz_srcβ : z ∈ (chartAt H β).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
    have hz_srcα : z ∈ (chartAt H α).source :=
      (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
        (I := I) (M := M) β α hy_target).mp hy_mem
    -- The chart transition carries `y` to the chart-`α` Euclidean image of `z`.
    have hsymm_target : (toEuclidean (E := E)).symm y ∈
        (extChartAt I β).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
      rw [hz_def, (extChartAt I β).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y =
        (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hy_eq]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_srcβ
    -- The transport coefficient at the chart-`β` Euclidean image of `z`.
    have h_coeff : chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y =
        transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target, ← hz_def]
    -- Split on whether the chart-`β` cutoff vanishes at `z`.
    by_cases hχβ : ((chartKernelCutoff (I := I) (M := M) β :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0
    · -- The chart-`β` cutoff vanishes: the transport coefficient — which
      -- carries that factor — vanishes too.
      rw [h_coeff, transportCoeffManifold_apply, hχβ]
      ring
    · -- The chart-`β` cutoff is nonzero at `z`.  Then `α` not being a transport
      -- chart centre of `β` forces the chart-`α` partition-of-unity weight to
      -- vanish at `z`.
      have hχβ_supp : z ∈ tsupport
          ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ hχβ
      have hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 := by
        by_contra hρα_ne
        exact hα (mem_transportChartCenters_of_pou_cutoff_ne
          (I := I) (M := M) β α hρα_ne hχβ)
      -- Hence the chart-pushed partition-of-unity weight of `α` vanishes at the
      -- chart-`α` Euclidean image of `z` — which is `chartTransitionEuclid β α
      -- y` — so the transported gated component identifies the eigenvector
      -- chart component there, which the gating fact pins to `0`.
      have hw_zero : chartPushedPouWeight (I := I) (M := M) α
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
        rw [hT_eq, chartPushedPouWeight_toEuclidean_extChartAt
          (I := I) (M := M) α hz_srcα, hρα]
      -- The transported gating fact at `y`.
      have hy_gate' : (if chartPushedPouWeight (I := I) (M := M) α
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 then
          eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q
            (chartTransitionEuclid (I := I) (M := M) β α y)
        else 0) = 0 := hy_gate
      rw [if_pos hw_zero] at hy_gate'
      rw [hy_gate', mul_zero]
  -- Off the overlap: the transport coefficient vanishes, since its chart-`α`
  -- cutoff factor vanishes off the chart-`α` source.
  have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
      chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
    intro y hy_notin
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
    · -- Inside the chart-`β` target: the chart-`β` inverse image avoids the
      -- chart-`α` source, so the chart-`α` cutoff — hence the transport
      -- coefficient — vanishes there.
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_notin_srcα : z ∉ (chartAt H α).source := by
        intro hz_srcα
        exact hy_notin
          ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
            (I := I) (M := M) β α hy_target).mpr hz_srcα)
      have hχα_zero : ((chartKernelCutoff (I := I) (M := M) α :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hz_notin_srcα
            (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
      have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y = 0 := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hχα_zero]
        ring
      rw [h_coeff_zero, zero_mul]
    · -- Outside the chart-`β` target the chart pushforward vanishes.
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target,
        zero_mul]
  -- Glue the on-overlap and off-overlap facts.
  exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap h_off_overlap

/-! ## The off-transport per-chart summand transport sum vanishes

Summing the single-term vanishing over the component multi-indices: for a chart
centre `α` outside the transport set of `β`, the finite transport sum over `Q`
vanishes almost everywhere. -/

/-- For a chart centre `α` outside the transport set of `β`, the finite sum, over
component multi-indices `Q`, of the chart-transition transport of the eigenvector
chart-`α` `Q`-components vanishes almost everywhere on the chart-`β` `L²`
measure. -/
private lemma transportSum_eigenvector_ae_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_each : ∀ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
            α Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) :=
    fun Q => chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem
      (I := I) (M := M) g r s h_atlas i α β P₀ Q hα
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_each Q)
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.sum_const_zero]

/-! ## The chart-component equality

Both the smooth representative's chart-`β` `P₀`-component and the eigenvector's
chart-`β` `P₀`-component reduce, almost everywhere, to the chart-pushed
partition-of-unity weight of `β` times a finite double sum of chart-transition
transports of chart-`γ` `Q`-components of the resolvent eigenvector. The index
sets are reconciled by the subset relation `transportChartCenters β ⊆
chartAtlasPOU_finset` and the off-transport vanishing. -/

/-- **The chart-component equality of the smooth eigenvector representative.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart base point `β` and a
component multi-index `P₀`, the canonical Euclidean chart-`β` `P₀`-component of
the smooth representative `eigenvectorSmooth g r s h_atlas i` equals — as an
element of the chart `L²` space `Lp ℝ 2 (chartL2Measure β)` — the canonical
chart-`β` `P₀`-component of the connection-Laplacian resolvent eigenvector
`tensorResolventEigenbasisVec h_atlas i`.

The smooth representative is the finite partition-of-unity sum of the per-chart
smooth sections; the canonical chart component is continuous-linear in the
abstract `L²` argument, so its chart-`β` `P₀`-component is the finite sum of the
per-chart components, each reconciled — via the per-chart component formula and
the single transport-term identity — with a finite sum of chart-transition
transport terms. The eigenvector's chart-`β` `P₀`-component is governed by the
abstract partition-of-unity transport law. The two finite double sums match: the
transport chart centres are a subset of the partition-of-unity support set, and
for a chart centre outside the transport set the corresponding transport term
vanishes almost everywhere. -/
theorem eigenvectorSmooth_tensorL2ChartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent g r s
        (eigenvectorSmooth g r s h_atlas i : TensorL2 r s g) β P₀ =
      tensorL2ChartComponent g r s
        (tensorResolventEigenbasisVec h_atlas i : TensorL2 r s g) β P₀ := by
  classical
  -- Reduce to the a.e. equality of the underlying functions.
  apply Lp.ext
  -- The smooth representative is the finite sum of the per-chart sections; its
  -- `L²`-coercion distributes through the finite sum (the smooth-section
  -- embedding is linear).
  have h_coe_sum :
      (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i : TensorL2 r s g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
            TensorL2 r s g) := by
    rw [← smoothToTensorL2_apply (I := I) (M := M) g r s,
      eigenvectorSmooth_eq (I := I) (M := M) g r s h_atlas i,
      map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [smoothToTensorL2_apply]
  -- The canonical chart component is continuous-linear in the abstract `L²`
  -- argument, so it distributes through the finite sum.
  have h_lhs_sum :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i :
            TensorL2 r s g) β P₀ =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
              TensorL2 r s g) β P₀ := by
    rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s β P₀,
      h_coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [tensorL2ChartComponentCLM_apply]
  rw [h_lhs_sum]
  -- Coerce the finite sum of `L²` classes to the finite sum of functions.
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) β
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun α => tensorL2ChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
        TensorL2 r s g) β P₀)).trans ?_
  -- Each per-chart summand becomes a chart-pushed-weight-times-transport-sum.
  have h_lhs_terms :
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
              TensorL2 r s g) β P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartPushedRaw I β
            (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                  α Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)) :=
    finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M))
      (fun α _ => eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum
        (I := I) (M := M) g r s h_atlas i α β P₀)
  refine h_lhs_terms.trans ?_
  -- The eigenvector's chart-`β` `P₀`-component, by the abstract transport law.
  refine Filter.EventuallyEq.symm
    ((tensorL2ChartComponent_ae_eq_pou_transport_sum (I := I) (M := M)
      g r s (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
      β P₀).trans ?_)
  -- Match the two finite double sums: reindex the left sum over the
  -- partition-of-unity support set down to the transport chart centres, the
  -- off-transport terms vanishing almost everywhere.
  have h_subset : transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) :=
    transportChartCenters_subset_chartAtlasPOU_finset (I := I) (M := M) β
  -- Abbreviate the per-chart summand of the left sum.
  set F : M → EuclN → ℝ := fun α y =>
    chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y
    with hF_def
  -- The right side of the transport law is the same per-chart summand `F`
  -- (with the partition-of-unity weight pulled inside) summed over the
  -- transport chart centres.
  have h_rhs_eq :
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ γ ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                  γ Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y) =
        fun y => ∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y := by
    funext y
    rw [Finset.mul_sum]
  rw [h_rhs_eq]
  -- Split the left sum: the transport chart centres plus the remaining
  -- partition-of-unity centres.
  have h_union : chartAtlasPOU_finset (I := I) (M := M) =
      transportChartCenters (I := I) (M := M) β ∪
        (chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β) :=
    (Finset.union_sdiff_of_subset h_subset).symm
  have h_disjoint : Disjoint (transportChartCenters (I := I) (M := M) β)
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β) :=
    Finset.disjoint_sdiff
  have h_split : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        F α y) =
      fun y => (∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y) +
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
            transportChartCenters (I := I) (M := M) β, F α y := by
    funext y
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disjoint]
  rw [h_split]
  -- The extra partition-of-unity centres contribute an almost-everywhere zero
  -- finite sum.
  have h_extra : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β, F α y)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    have h_each : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β,
        F α =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
      intro α hα
      have hα_notin : α ∉ transportChartCenters (I := I) (M := M) β :=
        (Finset.mem_sdiff.mp hα).2
      have h_zero := transportSum_eigenvector_ae_zero_of_notMem
        (I := I) (M := M) g r s h_atlas i α β P₀ hα_notin
      filter_upwards [h_zero] with y hy
      rw [hF_def]
      change chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
                α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y =
        (0 : ℝ)
      rw [hy, mul_zero]
    have h_sum := finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β)
      (fun α hα => h_each α hα)
    refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
    funext y
    rw [Finset.sum_const_zero]
  -- The left sum therefore agrees almost everywhere with the transport-chart
  -- sum, which is the right side.
  filter_upwards [h_extra] with y hy
  rw [show (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β, F α y) = 0 from hy,
    add_zero]

/-! ## Chart-locality-free twins

The following twins reprove the chart-component equality without the
uniform-Sobolev chart-locality hypothesis `h_atlas`, re-keyed onto the intrinsic
compact-operator eigenbasis `tensorResolventEigenbasisVec_ofCompact …`. -/

open Classical in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`chartPushedRaw_ite_transitionSum_eq_finsetSum`. -/
private lemma chartPushedRaw_ite_transitionSum_eq_finsetSum_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    chartPushedRaw I β
        (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y =
      ∑ Q : TensorCompIdx (E := E) r s,
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y := by
  classical
  -- Move the `if` inside the finite sum, then push the chart pushforward
  -- through the resulting finite sum.
  have h_ite :
      (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) =
        fun x => ∑ Q : TensorCompIdx (E := E) r s,
          (if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) := by
    funext x
    exact ite_finsetSum_eq_finsetSum_ite (Finset.univ) _ _
  rw [h_ite]
  exact chartPushedRaw_finsetSum (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => if x ∈ (chartAt H α).source then
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
          α Q.1 Q.2 x
    else 0) y

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum`. -/
private lemma eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i)
                α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
  classical
  -- Start from the per-chart component formula ("D-i").
  refine (eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq_unconditional
    (I := I) (M := M) g r s i α β P₀).trans ?_
  -- Push the chart pushforward through the inner component sum, so the per-`Q`
  -- transport reconciliation applies.
  have h_push : ∀ y : EuclN,
      chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                  α Q.1 Q.2 x
            else 0) y =
        ∑ Q : TensorCompIdx (E := E) r s,
          (chartPushedRaw I β
              (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
            chartPushedRaw I β
              (fun x => if x ∈ (chartAt H α).source then
                transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                  tensorChartComponentRaw (I := I) (M := M) g r s
                    (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                    α Q.1 Q.2 x
              else 0) y) := by
    intro y
    rw [chartPushedRaw_ite_transitionSum_eq_finsetSum_unconditional
      (I := I) (M := M) g r s i α β P₀ y, Finset.mul_sum]
  -- The right side of "D-i" therefore becomes a finite sum of single transport
  -- terms; reconcile each by the single transport-term identity ("File 2").
  have h_terms : ∀ Q : TensorCompIdx (E := E) r s,
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                α Q.1 Q.2 x
          else 0) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) :=
    fun Q => eigenvectorSmoothChart_transport_term_aeEq_unconditional
      (I := I) (M := M) g r s i β α P₀ Q
  -- Assemble: rewrite the product as a finite sum, then sum the per-`Q`
  -- reconciliations, then pull the partition-of-unity weight back out.
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_terms Q)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq (funext h_push)) ?_
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.mul_sum]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero`. -/
private lemma eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y
      else 0)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  filter_upwards [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero_unconditional
    (I := I) (M := M) g r s i α Q] with y hy
  by_cases hw : chartPushedPouWeight (I := I) (M := M) α y = 0
  · rw [if_pos hw]
    exact hy hw
  · rw [if_neg hw]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem`. -/
private lemma chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ Q : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- The transported function: chart-`β` pushforward of the transport
  -- coefficient times the chart-transition precomposition of the chart-`α`
  -- component.
  have h_coeFn := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M)
    g r s α β P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i) α Q)
  refine h_coeFn.trans ?_
  -- The transport coefficient is supported in the overlap of the two chart
  -- sources; the chart overlap `chartOverlapEuclid β α` is open, hence
  -- measurable.
  have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) β α
  have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
    hΩ_open.measurableSet
  -- The chart-`β` `L²` measure restricted to the chart overlap is the plain
  -- volume restricted to the overlap.
  have h_restrict_eq :
      (chartL2Measure (I := I) (M := M) β).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) =
      (volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) := by
    rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
      Set.inter_eq_left.mpr
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]
  -- On the overlap: the gated off-support vanishing of the eigenvector chart
  -- component, transported across the chart transition.
  have h_on_overlap :
      (fun y => chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y))
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_restrict_eq]
    -- The gated chart-`α` component vanishes a.e. on the chart-`α` `L²`
    -- measure; restrict it to the chart overlap of `α` with `β`, then transport
    -- across the chart transition `chartTransitionEuclid β α`.
    have h_gate_target :=
      eigenvectorChartComponentFun_ite_chartPushedPouWeight_zero_ae_zero_unconditional
        (I := I) (M := M) g r s i α Q
    have h_gate_overlap :
        (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
            eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α Q y
          else 0)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartOverlapEuclid (I := I) (M := M) α β)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [chartL2Measure] at h_gate_target
      exact ae_mono (Measure.restrict_mono_set _
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β))
        h_gate_target
    have h_gate_transport := chartTransitionEuclid_comp_ae_eq_restrict
      (I := I) (M := M) β α h_gate_overlap
    -- Almost-everywhere membership in the overlap.
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α)),
        y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
      ae_restrict_mem hΩ_meas
    filter_upwards [h_mem, h_gate_transport] with y hy_mem hy_gate
    -- The chart-`β` inverse image `z` of `y` lies in both chart sources.
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
    set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
      with hz_def
    have hz_srcβ : z ∈ (chartAt H β).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
    have hz_srcα : z ∈ (chartAt H α).source :=
      (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
        (I := I) (M := M) β α hy_target).mp hy_mem
    -- The chart transition carries `y` to the chart-`α` Euclidean image of `z`.
    have hsymm_target : (toEuclidean (E := E)).symm y ∈
        (extChartAt I β).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
      rw [hz_def, (extChartAt I β).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y =
        (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hy_eq]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_srcβ
    -- The transport coefficient at the chart-`β` Euclidean image of `z`.
    have h_coeff : chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y =
        transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target, ← hz_def]
    -- Split on whether the chart-`β` cutoff vanishes at `z`.
    by_cases hχβ : ((chartKernelCutoff (I := I) (M := M) β :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0
    · -- The chart-`β` cutoff vanishes: the transport coefficient — which
      -- carries that factor — vanishes too.
      rw [h_coeff, transportCoeffManifold_apply, hχβ]
      ring
    · -- The chart-`β` cutoff is nonzero at `z`.  Then `α` not being a transport
      -- chart centre of `β` forces the chart-`α` partition-of-unity weight to
      -- vanish at `z`.
      have hχβ_supp : z ∈ tsupport
          ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ hχβ
      have hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 := by
        by_contra hρα_ne
        exact hα (mem_transportChartCenters_of_pou_cutoff_ne
          (I := I) (M := M) β α hρα_ne hχβ)
      -- Hence the chart-pushed partition-of-unity weight of `α` vanishes at the
      -- chart-`α` Euclidean image of `z` — which is `chartTransitionEuclid β α
      -- y` — so the transported gated component identifies the eigenvector
      -- chart component there, which the gating fact pins to `0`.
      have hw_zero : chartPushedPouWeight (I := I) (M := M) α
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
        rw [hT_eq, chartPushedPouWeight_toEuclidean_extChartAt
          (I := I) (M := M) α hz_srcα, hρα]
      -- The transported gating fact at `y`.
      have hy_gate' : (if chartPushedPouWeight (I := I) (M := M) α
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 then
          eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
            (chartTransitionEuclid (I := I) (M := M) β α y)
        else 0) = 0 := hy_gate
      rw [if_pos hw_zero] at hy_gate'
      rw [hy_gate', mul_zero]
  -- Off the overlap: the transport coefficient vanishes, since its chart-`α`
  -- cutoff factor vanishes off the chart-`α` source.
  have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
      chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
    intro y hy_notin
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
    · -- Inside the chart-`β` target: the chart-`β` inverse image avoids the
      -- chart-`α` source, so the chart-`α` cutoff — hence the transport
      -- coefficient — vanishes there.
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_notin_srcα : z ∉ (chartAt H α).source := by
        intro hz_srcα
        exact hy_notin
          ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
            (I := I) (M := M) β α hy_target).mpr hz_srcα)
      have hχα_zero : ((chartKernelCutoff (I := I) (M := M) α :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hz_notin_srcα
            (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
      have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y = 0 := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hχα_zero]
        ring
      rw [h_coeff_zero, zero_mul]
    · -- Outside the chart-`β` target the chart pushforward vanishes.
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target,
        zero_mul]
  -- Glue the on-overlap and off-overlap facts.
  exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap h_off_overlap

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`transportSum_eigenvector_ae_zero_of_notMem`. -/
private lemma transportSum_eigenvector_ae_zero_of_notMem_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_each : ∀ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i)
            α Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) :=
    fun Q => chartTransitionTransportCLM_eigenvector_ae_zero_of_notMem_unconditional
      (I := I) (M := M) g r s i α β P₀ Q hα
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_each Q)
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.sum_const_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorSmooth_tensorL2ChartComponent_eq`. -/
theorem eigenvectorSmooth_tensorL2ChartComponent_eq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent g r s
        (eigenvectorSmooth_unconditional g r s i : TensorL2 r s g) β P₀ =
      tensorL2ChartComponent g r s
        (tensorResolventEigenbasisVec_ofCompact
          (tensorResolventL2_isCompactOperator_intrinsic g r s) i :
          TensorL2 r s g) β P₀ := by
  classical
  -- Reduce to the a.e. equality of the underlying functions.
  apply Lp.ext
  -- The smooth representative is the finite sum of the per-chart sections; its
  -- `L²`-coercion distributes through the finite sum (the smooth-section
  -- embedding is linear).
  have h_coe_sum :
      (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i : TensorL2 r s g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
            TensorL2 r s g) := by
    rw [← smoothToTensorL2_apply (I := I) (M := M) g r s,
      eigenvectorSmooth_eq_unconditional (I := I) (M := M) g r s i,
      map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [smoothToTensorL2_apply]
  -- The canonical chart component is continuous-linear in the abstract `L²`
  -- argument, so it distributes through the finite sum.
  have h_lhs_sum :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i :
            TensorL2 r s g) β P₀ =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
              TensorL2 r s g) β P₀ := by
    rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s β P₀,
      h_coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [tensorL2ChartComponentCLM_apply]
  rw [h_lhs_sum]
  -- Coerce the finite sum of `L²` classes to the finite sum of functions.
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) β
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun α => tensorL2ChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
        TensorL2 r s g) β P₀)).trans ?_
  -- Each per-chart summand becomes a chart-pushed-weight-times-transport-sum.
  have h_lhs_terms :
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
              TensorL2 r s g) β P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartPushedRaw I β
            (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                      g r s) i)
                  α Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)) :=
    finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M))
      (fun α _ => eigenvectorSmoothChart_tensorL2ChartComponent_eq_transport_sum_unconditional
        (I := I) (M := M) g r s i α β P₀)
  refine h_lhs_terms.trans ?_
  -- The eigenvector's chart-`β` `P₀`-component, by the abstract transport law.
  refine Filter.EventuallyEq.symm
    ((tensorL2ChartComponent_ae_eq_pou_transport_sum (I := I) (M := M)
      g r s (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)
      β P₀).trans ?_)
  -- Match the two finite double sums: reindex the left sum over the
  -- partition-of-unity support set down to the transport chart centres, the
  -- off-transport terms vanishing almost everywhere.
  have h_subset : transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) :=
    transportChartCenters_subset_chartAtlasPOU_finset (I := I) (M := M) β
  -- Abbreviate the per-chart summand of the left sum.
  set F : M → EuclN → ℝ := fun α y =>
    chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i)
              α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y
    with hF_def
  -- The right side of the transport law is the same per-chart summand `F`
  -- (with the partition-of-unity weight pulled inside) summed over the
  -- transport chart centres.
  have h_rhs_eq :
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ γ ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                      g r s) i)
                  γ Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y) =
        fun y => ∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y := by
    funext y
    rw [Finset.mul_sum]
  rw [h_rhs_eq]
  -- Split the left sum: the transport chart centres plus the remaining
  -- partition-of-unity centres.
  have h_union : chartAtlasPOU_finset (I := I) (M := M) =
      transportChartCenters (I := I) (M := M) β ∪
        (chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β) :=
    (Finset.union_sdiff_of_subset h_subset).symm
  have h_disjoint : Disjoint (transportChartCenters (I := I) (M := M) β)
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β) :=
    Finset.disjoint_sdiff
  have h_split : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        F α y) =
      fun y => (∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y) +
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
            transportChartCenters (I := I) (M := M) β, F α y := by
    funext y
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disjoint]
  rw [h_split]
  -- The extra partition-of-unity centres contribute an almost-everywhere zero
  -- finite sum.
  have h_extra : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β, F α y)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    have h_each : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β,
        F α =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
      intro α hα
      have hα_notin : α ∉ transportChartCenters (I := I) (M := M) β :=
        (Finset.mem_sdiff.mp hα).2
      have h_zero := transportSum_eigenvector_ae_zero_of_notMem_unconditional
        (I := I) (M := M) g r s i α β P₀ hα_notin
      filter_upwards [h_zero] with y hy
      rw [hF_def]
      change chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i)
                α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y =
        (0 : ℝ)
      rw [hy, mul_zero]
    have h_sum := finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β)
      (fun α hα => h_each α hα)
    refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
    funext y
    rw [Finset.sum_const_zero]
  -- The left sum therefore agrees almost everywhere with the transport-chart
  -- sum, which is the right side.
  filter_upwards [h_extra] with y hy
  rw [show (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β, F α y) = 0 from hy,
    add_zero]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
