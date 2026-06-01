import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransitionTransport

/-!
# The partition-of-unity ↔ cutoff chart-component bridge

For a closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)` and a chart base
point `α`, an abstract `L²` tensor element `u : TensorL2 r s g` carries two
chart-`P₀`-component-extraction maps:

* `tensorL2ChartComponent g r s u α P₀` — the **partition-of-unity-weighted**
  chart component: on a smooth section it is the chart-`α` pushforward of the
  partition-of-unity weight `chartAtlasPOU α` times the raw chart-frame scalar
  component.
* `tensorL2ChartComponentCutoff g r s u α P₀` — the **cutoff-weighted** chart
  component: on a smooth section it is the chart-`α` pushforward of the
  chart-kernel cutoff `chartKernelCutoff α` times the raw chart-frame scalar
  component.

The chart-kernel cutoff `chartKernelCutoff α` is a `C^∞`, `[0, 1]`-valued
function equal to `1` on the topological support of `chartAtlasPOU α`.

## The bridge

The headline `tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` states the
a.e.-identity

`tensorL2ChartComponent g r s u α P₀
   =ᵐ[chartL2Measure α]
   fun y => chartPushedRaw α (chartAtlasPOU α) y *
     tensorL2ChartComponentCutoff g r s u α P₀ y`.

Both sides are continuous-`ℝ`-linear in `u`: the right side is the bounded
`L²`-multiplier by the `[0, 1]`-valued bounded measurable function
`chartPushedRaw α (chartAtlasPOU α)` composed with the cutoff chart component.
They agree on smooth sections, because where the partition-of-unity weight is
nonzero the point lies in its topological support, so the chart-kernel cutoff
equals `1` there, and where the partition-of-unity weight vanishes both sides
vanish. Smooth sections are dense in the abstract `L²` completion, so the
identity extends to every `u` by the dense-range equaliser principle.

## The abstract partition-of-unity transport law

Rewriting the cutoff factor by the committed
`tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum` gives, as a corollary,
the abstract partition-of-unity-weighted transport law
`tensorL2ChartComponent_ae_eq_pou_transport_sum`: the partition-of-unity-weighted
chart component equals, almost everywhere, the pushed partition-of-unity weight
times the finite transport sum over the transport chart centres.

## Main definitions

* `chartPushedPouWeight α` — the chart-`α` pushforward of the partition-of-unity
  weight `chartAtlasPOU α`; a `[0, 1]`-valued bounded measurable function.
* `boundedPouMulLpCLM α` — the bounded `L²`-multiplier by `chartPushedPouWeight α`.

## Main results

* `tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` — the partition-of-unity
  ↔ cutoff chart-component bridge.
* `tensorL2ChartComponent_ae_eq_pou_transport_sum` — the abstract
  partition-of-unity-weighted transport law.
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

/-- The chart-`α` pushforward of the canonical partition-of-unity weight
`chartAtlasPOU α`. On the Euclidean chart target it reads the partition-of-unity
weight at the chart preimage; off the chart target it is `0`. -/
def chartPushedPouWeight (α : M) : EuclN → ℝ :=
  chartPushedRaw I α (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

/-- The chart-pushed partition-of-unity weight is bounded by `1` everywhere: on
the chart target it equals a `[0, 1]`-valued partition-of-unity value, and off
the chart target it is `0`. -/
private lemma chartPushedPouWeight_abs_le_one (α : M) (y : EuclN) :
    |chartPushedPouWeight (I := I) (M := M) α y| ≤ 1 := by
  classical
  unfold chartPushedPouWeight
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    set x : M := (extChartAt I α).symm (toEuclidean.symm y) with hx_def
    have h_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (chartAtlasPOU I M).nonneg α x
    have h_le : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (chartAtlasPOU I M).le_one α x
    rw [abs_of_nonneg h_nn]
    exact h_le
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, abs_zero]
    exact zero_le_one

/-- The chart-pushed partition-of-unity weight has norm bounded by `1`
everywhere. -/
private lemma chartPushedPouWeight_norm_le_one (α : M) (y : EuclN) :
    ‖chartPushedPouWeight (I := I) (M := M) α y‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact chartPushedPouWeight_abs_le_one (I := I) (M := M) α y

/-- The chart-pushed partition-of-unity weight is Borel measurable: the
partition-of-unity weight is `C^∞` hence measurable, and the chart pushforward
of a measurable function is measurable. -/
lemma chartPushedPouWeight_measurable (α : M) :
    Measurable (chartPushedPouWeight (I := I) (M := M) α) := by
  classical
  unfold chartPushedPouWeight
  exact chartPushedRaw_measurable (I := I) (M := M) α
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable

/-- The chart-pushed partition-of-unity weight is `AEStronglyMeasurable` with
respect to the chart `L²` measure. -/
private lemma chartPushedPouWeight_aestronglyMeasurable (α : M) :
    AEStronglyMeasurable (chartPushedPouWeight (I := I) (M := M) α)
      (chartL2Measure (I := I) (M := M) α) :=
  (chartPushedPouWeight_measurable (I := I) (M := M) α).aestronglyMeasurable

/-- The product of the chart-pushed partition-of-unity weight with an `L²`
function is `L²`: the weight is bounded by `1`, so the product is dominated by
the input in `L²` norm. -/
private lemma chartPushedPouWeight_mul_memLp
    (α : M) {f : EuclN → ℝ}
    (hf : MemLp f 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine ⟨(chartPushedPouWeight_aestronglyMeasurable
    (I := I) (M := M) α).mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN,
      ‖chartPushedPouWeight (I := I) (M := M) α y * f y‖ ≤ ‖f y‖ := by
    intro y
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right
      (chartPushedPouWeight_norm_le_one (I := I) (M := M) α y)
      (norm_nonneg _)).trans ?_
    rw [one_mul]
  calc eLpNorm (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
        (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_mono hpt
    _ < ⊤ := hf.2

/-- The `L²` norm of the product of the chart-pushed partition-of-unity weight
with an `L²` function is bounded by the `L²` norm of the function: the weight is
bounded by `1`. -/
private lemma eLpNorm_chartPushedPouWeight_mul_le
    (α : M) (f : EuclN → ℝ) :
    eLpNorm (fun y => chartPushedPouWeight (I := I) (M := M) α y * f y) 2
        (chartL2Measure (I := I) (M := M) α) ≤
      eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN,
      ‖chartPushedPouWeight (I := I) (M := M) α y * f y‖ ≤ ‖f y‖ := by
    intro y
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right
      (chartPushedPouWeight_norm_le_one (I := I) (M := M) α y)
      (norm_nonneg _)).trans ?_
    rw [one_mul]
  exact eLpNorm_mono hpt

/-- The `L²` class of the chart-pushed partition-of-unity weight times an `L²`
class. -/
private def boundedPouMulLp
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chartPushedPouWeight_mul_memLp (I := I) (M := M) α (Lp.memLp f)).toLp
    (fun y => chartPushedPouWeight (I := I) (M := M) α y *
      (f : EuclN → ℝ) y)

/-- The representative of `boundedPouMulLp α f` agrees almost everywhere with
the chart-pushed partition-of-unity weight times the representative of `f`. -/
private lemma boundedPouMulLp_coeFn
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    ((boundedPouMulLp (I := I) (M := M) α f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => chartPushedPouWeight (I := I) (M := M) α y *
        (f : EuclN → ℝ) y := by
  unfold boundedPouMulLp
  exact MemLp.coeFn_toLp _

/-- The bounded partition-of-unity `L²`-multiplier is additive. -/
private lemma boundedPouMulLp_add
    (α : M) (f₁ f₂ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    boundedPouMulLp (I := I) (M := M) α (f₁ + f₂) =
      boundedPouMulLp (I := I) (M := M) α f₁ +
        boundedPouMulLp (I := I) (M := M) α f₂ := by
  classical
  apply Lp.ext
  refine (boundedPouMulLp_coeFn (I := I) (M := M) α (f₁ + f₂)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  filter_upwards [Lp.coeFn_add f₁ f₂,
    boundedPouMulLp_coeFn (I := I) (M := M) α f₁,
    boundedPouMulLp_coeFn (I := I) (M := M) α f₂] with y hy_add hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂, hy_add, Pi.add_apply, mul_add]

/-- The bounded partition-of-unity `L²`-multiplier is `ℝ`-homogeneous. -/
private lemma boundedPouMulLp_smul
    (α : M) (c : ℝ) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    boundedPouMulLp (I := I) (M := M) α (c • f) =
      c • boundedPouMulLp (I := I) (M := M) α f := by
  classical
  apply Lp.ext
  refine (boundedPouMulLp_coeFn (I := I) (M := M) α (c • f)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul c _).symm
  filter_upwards [Lp.coeFn_smul c f,
    boundedPouMulLp_coeFn (I := I) (M := M) α f] with y hy_smul hy
  rw [Pi.smul_apply, hy, hy_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_left_comm]

/-- The bounded partition-of-unity `L²`-multiplier as an `ℝ`-linear map. -/
private def boundedPouMulLpLin (α : M) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →ₗ[ℝ]
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun f := boundedPouMulLp (I := I) (M := M) α f
  map_add' f₁ f₂ := boundedPouMulLp_add (I := I) (M := M) α f₁ f₂
  map_smul' c f := boundedPouMulLp_smul (I := I) (M := M) α c f

@[simp] private lemma boundedPouMulLpLin_apply
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    boundedPouMulLpLin (I := I) (M := M) α f =
      boundedPouMulLp (I := I) (M := M) α f := rfl

/-- The operator-norm bound for the bounded partition-of-unity `L²`-multiplier:
the `L²` norm of the product is bounded by `1 · ‖f‖`. -/
private lemma boundedPouMulLpLin_norm_le
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    ‖boundedPouMulLpLin (I := I) (M := M) α f‖ ≤ 1 * ‖f‖ := by
  classical
  rw [one_mul, boundedPouMulLpLin_apply]
  unfold boundedPouMulLp
  rw [MeasureTheory.Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  exact eLpNorm_chartPushedPouWeight_mul_le (I := I) (M := M) α _

/-- **The bounded partition-of-unity `L²`-multiplier.** The continuous linear
self-map of `Lp ℝ 2 (chartL2Measure α)` given by multiplication by the
`[0, 1]`-valued bounded measurable function `chartPushedPouWeight α`. -/
def boundedPouMulLpCLM (α : M) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →L[ℝ]
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (boundedPouMulLpLin (I := I) (M := M) α).mkContinuous 1
    (boundedPouMulLpLin_norm_le (I := I) (M := M) α)

@[simp] private lemma boundedPouMulLpCLM_apply
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    boundedPouMulLpCLM (I := I) (M := M) α f =
      boundedPouMulLp (I := I) (M := M) α f := rfl

/-- The representative of `boundedPouMulLpCLM α` applied to `f` agrees almost
everywhere with the chart-pushed partition-of-unity weight times the
representative of `f`. -/
private lemma boundedPouMulLpCLM_coeFn
    (α : M) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    ((boundedPouMulLpCLM (I := I) (M := M) α f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => chartPushedPouWeight (I := I) (M := M) α y *
        (f : EuclN → ℝ) y := by
  rw [boundedPouMulLpCLM_apply]
  exact boundedPouMulLp_coeFn (I := I) (M := M) α f

/-- For every point `x` of the manifold, the partition-of-unity weight at `α`
times any real value `v` equals the partition-of-unity weight at `α` times the
chart-kernel cutoff at `α` times `v`.

Where the partition-of-unity weight is nonzero the point lies in its
topological support, where the chart-kernel cutoff equals `1`; where the weight
vanishes both sides vanish. -/
private lemma pou_smul_eq_pou_smul_cutoff_smul
    (α : M) (x : M) (v : ℝ) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v) := by
  classical
  by_cases hρ : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0
  · rw [hρ, zero_mul, zero_mul]
  · have hx_supp : x ∈
        tsupport
          (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      subset_tsupport _ hρ
    have hχ : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ) x = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) α hx_supp
    rw [hχ, one_mul]

/-- For a smooth compactly-supported `(r, s)`-tensor section `S`, the
partition-of-unity-weighted raw chart-frame scalar component equals, pointwise
on `M`, the partition-of-unity weight times the cutoff-weighted raw chart-frame
scalar component. -/
private lemma tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (x : M) :
    tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
  classical
  unfold tensorChartComponentPou cutoffComponentScalar
  exact pou_smul_eq_pou_smul_cutoff_smul (I := I) (M := M) α x
    (tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x)

/-- The chart-`α` pushforward of a pointwise product where the first factor is
`chartAtlasPOU α` is, pointwise on Euclidean space, the chart-pushed
partition-of-unity weight times the chart-`α` pushforward of the second
factor. -/
private lemma chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul
    (α : M) (F : M → ℝ) (y : EuclN) :
    chartPushedRaw I α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * F x)
        y =
      chartPushedPouWeight (I := I) (M := M) α y *
        chartPushedRaw I α F y := by
  classical
  unfold chartPushedPouWeight
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, zero_mul]

/-- For a smooth compactly-supported `(r, s)`-tensor section `S`, the Euclidean
chart component equals, pointwise on Euclidean space, the chart-pushed
partition-of-unity weight times the cutoff Euclidean chart component. -/
private lemma tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 y =
      chartPushedPouWeight (I := I) (M := M) α y *
        cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y := by
  classical
  rw [tensorChartComponent_def, cutoffComponentEuclid_eq_chartPushedRaw]
  have h_scalar :
      tensorChartComponentPou (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2 x := by
    funext x
    exact tensorChartComponentPou_eq_pou_mul_cutoffComponentScalar
      (I := I) (M := M) g r s S α P₀ x
  rw [h_scalar]
  exact chartPushedRaw_pou_mul_eq_chartPushedPouWeight_mul (I := I) (M := M) α
    (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) y

/-- **The smooth-section bridge identity.** For a smooth compactly-supported
`(r, s)`-tensor section `S`, the partition-of-unity chart component of its image
in the `L²` Hilbert space equals the bounded partition-of-unity `L²`-multiplier
applied to the cutoff chart component. -/
private lemma tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (S : TensorL2 r s g) α P₀) := by
  classical
  apply Lp.ext
  refine (tensorL2ChartComponent_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀).trans ?_
  refine Filter.EventuallyEq.symm (Filter.EventuallyEq.trans
    (boundedPouMulLpCLM_coeFn (I := I) (M := M) α
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀)) ?_)
  filter_upwards [tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s S α P₀] with y hy
  rw [hy]
  exact (tensorChartComponent_eq_chartPushedPouWeight_mul_cutoffComponentEuclid
    (I := I) (M := M) g r s S α P₀ y).symm

/-- The bounded-multiplier image of the cutoff chart component is a continuous
function of the abstract `L²` element: it is the composition of the bounded
partition-of-unity `L²`-multiplier with the cutoff chart component. -/
private lemma continuous_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Continuous (fun u : TensorL2 r s g =>
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) := by
  classical
  have h_fun :
      (fun u : TensorL2 r s g =>
        boundedPouMulLpCLM (I := I) (M := M) α
          (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) =
        (fun u : TensorL2 r s g =>
          boundedPouMulLpCLM (I := I) (M := M) α
            (tensorL2ChartComponentCutoffCLM (I := I) (M := M)
              g r s α P₀ u)) := by
    funext u
    rw [tensorL2ChartComponentCutoffCLM_apply]
  rw [h_fun]
  exact (boundedPouMulLpCLM (I := I) (M := M) α).continuous.comp
    (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀).continuous

/-- **The abstract partition-of-unity ↔ cutoff bridge (as `L²` classes).** For an
arbitrary abstract `L²` tensor element `u : TensorL2 r s g`, the
partition-of-unity chart `P₀`-component of `u` equals — as an element of
`Lp ℝ 2 (chartL2Measure α)` — the bounded partition-of-unity `L²`-multiplier
applied to the cutoff chart `P₀`-component of `u`.

Both sides are continuous-linear in `u`; they agree on the dense subspace of
smooth compactly-supported sections by
`tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff`, so the dense-range
equaliser principle extends the identity to every `u`. -/
private lemma tensorL2ChartComponent_eq_boundedPouMul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      boundedPouMulLpCLM (I := I) (M := M) α
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀) := by
  classical
  set lhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => tensorL2ChartComponent (I := I) (M := M) g r s v α P₀
    with hlhs_def
  set rhs : TensorL2 r s g → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun v => boundedPouMulLpCLM (I := I) (M := M) α
      (tensorL2ChartComponentCutoff (I := I) (M := M) g r s v α P₀)
    with hrhs_def
  suffices h_eq : lhs = rhs by
    exact congrFun h_eq u
  have h_lhs_cont : Continuous lhs := by
    rw [hlhs_def]
    exact continuous_tensorL2ChartComponent (I := I) (M := M) g r s α P₀
  have h_rhs_cont : Continuous rhs := by
    rw [hrhs_def]
    exact continuous_boundedPouMul_cutoff (I := I) (M := M) g r s α P₀
  have h_denseRange :
      DenseRange ((↑) : SmoothCcTensor g r s → TensorL2 r s g) :=
    UniformSpace.Completion.denseRange_coe
  refine h_denseRange.equalizer h_lhs_cont h_rhs_cont ?_
  funext S
  rw [Function.comp_apply, Function.comp_apply, hlhs_def, hrhs_def]
  exact tensorL2ChartComponent_smooth_eq_boundedPouMul_cutoff
    (I := I) (M := M) g r s S α P₀

/-- **The partition-of-unity ↔ cutoff chart-component bridge.** For an arbitrary
abstract `L²` tensor element `u : TensorL2 r s g`, a chart base point `α` and a
component multi-index `P₀`, the partition-of-unity-weighted chart `P₀`-component
of `u` equals, almost everywhere on the Euclidean chart target, the chart-pushed
partition-of-unity weight times the cutoff-weighted chart `P₀`-component of `u`.

Both sides are continuous-`ℝ`-linear in `u`: the right side is the bounded
`L²`-multiplier by the `[0, 1]`-valued bounded measurable function
`chartPushedRaw α (chartAtlasPOU α)` composed with the cutoff chart component.
They agree on smooth compactly-supported sections — there the chart-kernel
cutoff equals `1` wherever the partition-of-unity weight is nonzero — and smooth
sections are dense in the abstract `L²` completion. -/
theorem tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  rw [tensorL2ChartComponent_eq_boundedPouMul_cutoff (I := I) (M := M)
    g r s u α P₀]
  exact boundedPouMulLpCLM_coeFn (I := I) (M := M) α
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)

/-- **The abstract partition-of-unity-weighted transport law.** For an arbitrary
abstract `L²` tensor element `u : TensorL2 r s g`, a chart base point `α` and a
component multi-index `P₀`, the partition-of-unity-weighted chart `P₀`-component
of `u` equals, almost everywhere on the Euclidean chart target, the chart-pushed
partition-of-unity weight times the finite sum — over the transport chart centres
`β` and the component multi-indices `Q` — of the chart-transition transport of
the partition-of-unity `Q`-components of `u`.

This is the partition-of-unity ↔ cutoff bridge
`tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` with the cutoff factor
rewritten by the cutoff-component transport decomposition
`tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum`. -/
theorem tensorL2ChartComponent_ae_eq_pou_transport_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y) := by
  classical
  refine (tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s u α P₀).trans ?_
  filter_upwards [tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
    (I := I) (M := M) g r s u α P₀] with y hy
  rw [hy]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →L[ℝ]
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  boundedPouMulLpCLM (I := I) (M := M) α

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) :=
  tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s u α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
