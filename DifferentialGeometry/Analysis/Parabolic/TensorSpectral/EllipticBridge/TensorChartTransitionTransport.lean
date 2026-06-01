import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.ChartTransitionTransportCLM

/-!
# The abstract a.e. decomposition of the cutoff-weighted chart component

For a closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)` and a chart base
point `α`, this file proves that the cutoff-weighted chart `P₀`-component of an
arbitrary abstract `L²` tensor element `u : TensorL2 r s g` equals, almost
everywhere on the Euclidean chart target, a finite sum — over the chart centres
`β` whose partition-of-unity weight meets the chart-`α` cutoff support, and over
the component multi-indices `Q` — of the chart-transition transport of the
partition-of-unity `Q`-components of `u`.

## The finite index set

`transportChartCenters α` is the finite set of chart centres `β : M` such that
the support of the chart-atlas partition-of-unity weight `chartAtlasPOU β` meets
the topological support of the chart-kernel cutoff `chartKernelCutoff α`. It is
finite because the partition-of-unity weight family is locally finite and the
cutoff's topological support is compact.

## The decomposition

The headline `tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum` states the
a.e.-identity

`(tensorL2ChartComponentCutoff g r s u α P₀)
   =ᵐ[chartL2Measure α]
   fun y => ∑ β ∈ transportChartCenters α, ∑ Q,
     (chartTransitionTransportCLM g r s β α P₀ Q
        (tensorL2ChartComponent g r s u β Q)) y`.

Both sides are continuous-linear in `u`. They agree on smooth compactly-supported
sections: there the transport operator's smooth-section compatibility
(`chartTransitionTransportCLM_coeFn_smooth`) turns the right side into a finite
sum of chart-pushed transport-coefficient-weighted partition-of-unity
components, and the `(r, s)`-tensor transformation law
(`tensorChartComponentRaw_chartTransition_decomp`) together with the
partition-of-unity identity `∑ β, chartAtlasPOU β = 1` recovers the cutoff
component. Smooth sections are dense in the abstract `L²` completion, so the
identity extends to every `u`.

## Main definitions

* `transportChartCenters α` — the finite set of relevant chart centres.

## Main results

* `tensorL2ChartComponentCutoff_eq_pou_transport_sum` — the underlying equality
  of `L²` classes.
* `tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum` — the headline
  a.e.-identity on the Euclidean chart target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

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

/-- The function underlying a finite sum of `L²` classes agrees almost
everywhere with the finite sum of the underlying functions. -/
lemma coeFn_finsetSum_chartL2
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

/-- The set of chart centres `β` whose partition-of-unity weight has support
meeting the topological support of the chart-`α` kernel cutoff is finite: the
weight family is locally finite, and the cutoff support is compact. -/
private lemma transportChartCenters_finite (α : M) :
    {β : M |
        (Function.support
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport
            ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
              M → ℝ)).Nonempty}.Finite := by
  classical
  have hlf : LocallyFinite
      (fun β : M =>
        Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (chartAtlasPOU I M).locallyFinite
  have hcompact : IsCompact
      (tsupport
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    chartKernelCutoff_hasCompactSupport (I := I) (M := M) α
  exact hlf.finite_nonempty_inter_compact hcompact

/-- **The transport chart centres.** For a chart base point `α : M`, the finite
set of chart centres `β : M` such that the support of the chart-atlas
partition-of-unity weight at `β` meets the topological support of the
chart-kernel cutoff at `α`.

This is the index set over which the cutoff-weighted chart component of an
abstract `L²` tensor decomposes as a finite sum of transported
partition-of-unity components: outside this finite set the partition-of-unity
weight misses the cutoff support, so its contribution vanishes. -/
def transportChartCenters (α : M) : Finset M :=
  (transportChartCenters_finite (I := I) (M := M) α).toFinset

/-- Membership in `transportChartCenters α`: a chart centre `β` belongs to it
exactly when its partition-of-unity weight has support meeting the chart-`α`
cutoff support. -/
lemma mem_transportChartCenters (α β : M) :
    β ∈ transportChartCenters (I := I) (M := M) α ↔
      (Function.support
          (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
            M → ℝ)).Nonempty := by
  unfold transportChartCenters
  rw [Set.Finite.mem_toFinset]
  rfl

/-- If the partition-of-unity weight at `β` and the chart-kernel cutoff at `α`
are both nonzero at a common point `x`, then `β` is a transport chart centre. -/
lemma mem_transportChartCenters_of_pou_cutoff_ne
    (α β : M) {x : M}
    (hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0)
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    β ∈ transportChartCenters (I := I) (M := M) α := by
  rw [mem_transportChartCenters]
  exact ⟨x, hβ, subset_tsupport _ hα⟩

/-- At a point where the chart-`α` cutoff is nonzero, the partition-of-unity
weights summed over the transport chart centres equal `1`. The finite support of
the partition-of-unity at that point is contained in `transportChartCenters α`,
so the partition-of-unity sum identity applies. -/
private lemma sum_chartAtlasPOU_transportChartCenters_eq_one
    (α : M) {x : M}
    (hα : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0) :
    ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1 := by
  classical
  have hsubset :
      (chartAtlasPOU I M).finsupport x ⊆
        transportChartCenters (I := I) (M := M) α := by
    intro β hβ
    rw [SmoothPartitionOfUnity.mem_finsupport] at hβ
    exact mem_transportChartCenters_of_pou_cutoff_ne
      (I := I) (M := M) α β hβ hα
  exact (chartAtlasPOU I M).sum_finsupport' x (Set.mem_univ x) hsubset

/-- For any chart centre `β`, any point `x` of the chart-`α` source, and any
component multi-index `P₀`, the partition-of-unity weight at `β` times the raw
chart-`α` component equals the sum, over component multi-indices `Q`, of the
chart-kernel cutoff at `β` times the transition coefficient times the
partition-of-unity-weighted raw chart-`β` component.

When the partition-of-unity weight at `β` vanishes both sides vanish; otherwise
the point lies in the chart-`β` source too — so the `(r, s)`-tensor
transformation law expands the raw chart-`α` component in the raw chart-`β`
components — and lies in the closed support of the partition-of-unity weight, so
the chart-`β` cutoff equals `1` there. -/
private lemma pou_smul_raw_eq_transition_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (β α : M)
    (P₀ : TensorCompIdx (E := E) r s) {x : M}
    (hx_α : x ∈ (chartAt H α).source) :
    ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  by_cases hβ : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hβ, zero_mul]
    refine (Finset.sum_eq_zero (fun Q _ => ?_)).symm
    unfold tensorChartComponentPou
    rw [hβ]
    ring
  · have hx_supp : x ∈
        tsupport
          (fun y : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hβ
    have hx_β : x ∈ (chartAt H β).source :=
      chartAtlasPOU_isSubordinate I M β hx_supp
    have hχβ : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) β hx_supp
    have hdecomp :=
      tensorChartComponentRaw_eq_transitionCoeff_sum
        (E := E) (I := I) (M := M) g r s S β α P₀ ⟨hx_β, hx_α⟩
    rw [hdecomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    unfold tensorChartComponentPou
    rw [hχβ]
    ring

/-- **The manifold-side cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff-weighted raw
chart-frame scalar component centred at `α` equals, pointwise on `M`, the finite
sum over the transport chart centres `β` and the component multi-indices `Q` of
the transport-coefficient-weighted partition-of-unity `Q`-components centred at
`β`.

The proof splits on whether the chart-`α` kernel cutoff vanishes. Where it
vanishes both sides vanish — the transport coefficient carries the chart-`α`
cutoff factor. Where it is nonzero the point lies in the chart-`α` source; the
per-centre transformation-law identity `pou_smul_raw_eq_transition_sum` and the
partition-of-unity sum `sum_chartAtlasPOU_transportChartCenters_eq_one` over the
transport chart centres recover the raw chart-`α` component. -/
private lemma cutoffComponentScalar_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (x : M) :
    cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
            tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
  classical
  unfold cutoffComponentScalar
  set χα : ℝ := ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
    M → ℝ) x with hχα_def
  by_cases hχα : χα = 0
  · rw [hχα, zero_mul]
    refine (Finset.sum_eq_zero (fun β _ => Finset.sum_eq_zero (fun Q _ => ?_))).symm
    rw [transportCoeffManifold_apply]
    rw [show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl, hχα]
    ring
  · have hx_supp : x ∈
        tsupport
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ hχα
    have hx_α : x ∈ (chartAt H α).source :=
      chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_supp
    have h_rhs :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        χα *
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                  M → ℝ) x *
                transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [transportCoeffManifold_apply,
        show ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
          = χα from rfl]
      ring
    rw [h_rhs]
    have h_inner :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
                M → ℝ) x *
              transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x *
              tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) =
        ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
      refine Finset.sum_congr rfl (fun β _ => ?_)
      exact (pou_smul_raw_eq_transition_sum
        (I := I) (M := M) g r s S β α P₀ hx_α).symm
    rw [h_inner, ← Finset.sum_mul,
      sum_chartAtlasPOU_transportChartCenters_eq_one (I := I) (M := M) α hχα,
      one_mul]

/-- The chart-`α` pushforward of a finite sum of manifold functions equals,
pointwise on the Euclidean model space, the finite sum of the chart-`α`
pushforwards of the summands. -/
lemma chartPushedRaw_finsetSum
    (α : M) {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) (y : EuclN) :
    chartPushedRaw I α (fun x : M => ∑ a ∈ s, F a x) y =
      ∑ a ∈ s, chartPushedRaw I α (F a) y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

/-- **The Euclidean cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff Euclidean chart
component centred at `α` equals, pointwise on the Euclidean model space, the
finite sum over the transport chart centres `β` and the component multi-indices
`Q` of the chart-`α` pushforwards of the transport-coefficient-weighted
partition-of-unity `Q`-components centred at `β`. -/
private lemma cutoffComponentEuclid_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartPushedRaw I α
            (fun x : M =>
              transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
            y := by
  classical
  rw [cutoffComponentEuclid_eq_chartPushedRaw (I := I) (M := M) g r s S α
    P₀.1 P₀.2]
  have h_scalar :
      cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun x : M =>
          ∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x := by
    funext x
    exact cutoffComponentScalar_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ x
  rw [h_scalar]
  rw [chartPushedRaw_finsetSum (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β x => ∑ Q : TensorCompIdx (E := E) r s,
      transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
        tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  exact chartPushedRaw_finsetSum (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
      tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y

/-- If finitely many summands agree almost everywhere, then so do their finite
sums. -/
lemma finsetSum_ae_eq
    (α : M) {ι : Type*} (s : Finset ι) {f h : ι → EuclN → ℝ}
    (hfh : ∀ a ∈ s,
      f a =ᵐ[chartL2Measure (I := I) (M := M) α] h a) :
    (fun y => ∑ a ∈ s, f a y) =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, h a y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hfh_a : f a =ᵐ[chartL2Measure (I := I) (M := M) α] h a :=
        hfh a (Finset.mem_insert_self a t)
      have hfh_t : ∀ b ∈ t,
          f b =ᵐ[chartL2Measure (I := I) (M := M) α] h b :=
        fun b hb => hfh b (Finset.mem_insert_of_mem hb)
      filter_upwards [hfh_a, ih hfh_t] with y hya hyt
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hyt]

/-- **The smooth-section cutoff-component decomposition.** For a smooth
compactly-supported `(r, s)`-tensor section `S`, the cutoff chart component of
its image in the `L²` Hilbert space equals the finite sum over the transport
chart centres `β` and the component multi-indices `Q` of the transported
partition-of-unity `Q`-components centred at `β`. -/
private lemma tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (S : TensorL2 r s g) β Q) := by
  classical
  apply Lp.ext
  refine (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀).trans ?_
  have h_rhs_coeFn :
      ((∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (S : TensorL2 r s g) β Q)) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) =ᵐ[
          chartL2Measure (I := I) (M := M) α]
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (S : TensorL2 r s g) β Q))).trans ?_
    refine finsetSum_ae_eq (I := I) (M := M) α
      (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
    refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q => chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (S : TensorL2 r s g) β Q))).trans ?_
    refine finsetSum_ae_eq (I := I) (M := M) α
      (Finset.univ : Finset (TensorCompIdx (E := E) r s)) (fun Q _ => ?_)
    exact chartTransitionTransportCLM_coeFn_smooth
      (I := I) (M := M) g r s β α S P₀ Q
  have h_pointwise :
      cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            chartPushedRaw I α
              (fun x : M =>
                transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
                  tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x)
              y := by
    funext y
    exact cutoffComponentEuclid_eq_pou_transport_sum
      (I := I) (M := M) g r s S α P₀ y
  rw [h_pointwise]
  exact h_rhs_coeFn.symm

/-- The transport sum is a continuous function of the abstract `L²` element: a
finite sum over the transport chart centres and component multi-indices of
compositions of the transport operator with the canonical chart component, each
continuous. -/
private lemma continuous_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q)) := by
  classical
  refine continuous_finset_sum _ (fun β _ => ?_)
  refine continuous_finset_sum _ (fun Q _ => ?_)
  exact (chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q).continuous.comp
    (continuous_tensorL2ChartComponent (I := I) (M := M) g r s β Q)

/-- **The abstract cutoff-component decomposition.** For an arbitrary abstract
`L²` tensor element `u : TensorL2 r s g`, the cutoff chart `P₀`-component of `u`
equals — as an element of `Lp ℝ 2 (chartL2Measure α)` — the finite sum over the
transport chart centres `β` and the component multi-indices `Q` of the
chart-transition transport of the partition-of-unity `Q`-components of `u`.

Both sides are continuous-linear in `u`; they agree on the dense subspace of
smooth compactly-supported sections by
`tensorL2ChartComponentCutoff_smooth_eq_transport_sum`, so the dense-range
equaliser principle extends the identity to every `u`. -/
theorem tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) := by
  classical
  set lhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀
    with hlhs_def
  set rhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
      ∑ Q : TensorCompIdx (E := E) r s,
        chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s v β Q)
    with hrhs_def
  suffices h_eq : lhs = rhs by
    exact congrFun h_eq u
  have h_lhs_cont : Continuous lhs := by
    rw [hlhs_def]
    have h_fun : (fun v : TensorL2 r s g =>
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀) =
        (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀) := by
      funext v
      rw [tensorL2ChartComponentCutoffCLM_apply]
    rw [h_fun]
    exact (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀).continuous
  have h_rhs_cont : Continuous rhs := by
    rw [hrhs_def]
    exact continuous_transport_sum (I := I) (M := M) g r s α P₀
  have h_denseRange :
      DenseRange ((↑) : SmoothCcTensor g r s → TensorL2 r s g) :=
    UniformSpace.Completion.denseRange_coe
  refine h_denseRange.equalizer h_lhs_cont h_rhs_cont ?_
  funext S
  rw [Function.comp_apply, Function.comp_apply, hlhs_def, hrhs_def]
  exact tensorL2ChartComponentCutoff_smooth_eq_transport_sum
    (I := I) (M := M) g r s S α P₀

/-- **The abstract cutoff-component a.e. decomposition.** For an arbitrary
abstract `L²` tensor element `u : TensorL2 r s g`, the cutoff chart
`P₀`-component of `u` equals, almost everywhere on the Euclidean chart target,
the finite sum over the transport chart centres `β` and the component
multi-indices `Q` of the chart-transition transport of the partition-of-unity
`Q`-components of `u`.

This is the a.e.-identity form of `tensorL2ChartComponentCutoff_eq_pou_transport_sum`,
obtained by passing to representatives via the `L²` coercion lemmas. -/
theorem tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  rw [tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀]
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α)
    (fun β => ∑ Q : TensorCompIdx (E := E) r s,
      chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))).trans ?_
  refine finsetSum_ae_eq (I := I) (M := M) α
    (transportChartCenters (I := I) (M := M) α) (fun β _ => ?_)
  exact coeFn_finsetSum_chartL2 (I := I) (M := M) α
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q => chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
      (tensorL2ChartComponent (I := I) (M := M) g r s u β Q))

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) : Finset M := transportChartCenters (I := I) (M := M) α

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ =
      ∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :=
  tensorL2ChartComponentCutoff_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
