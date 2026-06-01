import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.AbstractChartPull

/-!
# An `L²` tensor element is determined by its chart components

For a smooth Riemannian metric `g` on a closed (compact, boundaryless) smooth
manifold `M` and fixed ranks `(r, s)`, the metric `L²` Hilbert space
`TensorL2 r s g` of `(r, s)`-tensor fields is the Hausdorff completion of the
seminormed space `SmoothCcTensor g r s` of smooth compactly-supported tensor
sections. A general element of `TensorL2 r s g` carries no concrete tensor
section.

The canonical Euclidean chart component `tensorL2ChartComponent g r s u α P₀`
(`CanonicalTensorRepr.lean`) reads off, from an abstract element
`u : TensorL2 r s g`, the partition-of-unity-weighted chart-frame scalar
component at a chart center `α : M` and a component multi-index `P₀`, as a
genuine `L²` function class on the Euclidean chart target.

This file proves that this family of chart components is **complete**: an `L²`
tensor element is fully determined by the whole family of its chart components.

## The argument

The chart-component map `tensorL2ChartComponent g r s · α P₀` is continuous and
`ℝ`-linear, so the statement reduces, on the difference `w := u - v`, to: the
only `w` with all chart components zero is `w = 0`.

The chart-pull headline `tensorL2Inner_pouSmul_tensorL2ChartComponent_pull`
expresses the global `L²` inner product of a partition-of-unity-weighted
concrete section `pouSmul g r s α Sg` against an abstract element as a
chart-Euclidean integral whose integrand is linear in the canonical chart
components `tensorL2ChartComponent`. If all chart components of `w` vanish, this
integral is zero, so `w` is orthogonal to every section of the form
`pouSmul g r s α (pouSmul g r s α S)` — the chart-`α`-supported section
`pouSmul g r s α S` substituted for the headline's `Sg`.

The chart-atlas partition of unity `chartAtlasPOU I M` sums to `1`, so on a
compact manifold the smooth function `Φ := ∑_α (chartAtlasPOU I M α)²` is
strictly positive (hence has a smooth reciprocal). For every smooth section `T`,

```
T = ∑_α pouSmul g r s α (pouSmul g r s α (Φ⁻¹ • T)),
```

because the pointwise weight `∑_α (chartAtlasPOU I M α x)² · Φ(x)⁻¹` is `1`.
Hence `⟪(T : TensorL2), w⟫ = 0` for every smooth section `T`; smooth sections
are dense, so `⟪·, w⟫` vanishes identically and `w = 0`.

## Main result

* `tensorL2_eq_of_chartComponent_eq` — two `L²` tensor elements with identical
  families of canonical Euclidean chart components are equal.
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

/-- The pointwise scalar product of a globally `C^∞` real-valued function `φ`
and a smooth compactly-supported `(r, s)`-tensor section `S`, packaged as a
smooth compactly-supported tensor section. -/
private def smoothFnSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : M → ℝ) (hφ : ContMDiff I (𝓘(ℝ, ℝ)) ∞ φ)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => φ x • S.toSection x
      contMDiff_toFun := ContMDiff.smul_section hφ S.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport S.toFun ?_
    rw [Function.mem_support]
    intro hS_zero
    apply hx
    change TensorRSSpace.toModel (φ x • S.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (S.toSection x) = S.toFun x from rfl, hS_zero,
      smul_zero]

/-- The underlying section of `smoothFnSmul g r s φ hφ S` is the pointwise
scalar product of `φ` and the underlying section of `S`. -/
private lemma smoothFnSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : M → ℝ) (hφ : ContMDiff I (𝓘(ℝ, ℝ)) ∞ φ)
    (S : SmoothCcTensor g r s) (x : M) :
    (smoothFnSmul (I := I) (M := M) g r s φ hφ S).toSection x =
      φ x • S.toSection x := rfl

/-- The chart-atlas partition-of-unity weights sum to `1` over the finite
support `Finset` at every point of a compact manifold. -/
private lemma chartAtlasPOU_finset_sum_eq_one (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) α x) = 1 := by
  classical
  have h_finsum : ∑ᶠ α : M, ((chartAtlasPOU I M) α x) = 1 :=
    (chartAtlasPOU I M).sum_eq_one (Set.mem_univ x)
  have h_supp : Function.support (fun α : M => ((chartAtlasPOU I M) α x)) ⊆
      (chartAtlasPOU_finset (I := I) (M := M) : Set M) := by
    intro α hα
    rw [Function.mem_support] at hα
    rw [Finset.mem_coe, chartAtlasPOU_finset_mem]
    exact ⟨x, hα⟩
  rw [← h_finsum, finsum_eq_sum_of_support_subset _ h_supp]

/-- The sum of squares of the chart-atlas partition-of-unity weights over the
finite support `Finset`. -/
private def pouSq (x : M) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x)

/-- The partition-of-unity square `pouSq` is globally `C^∞`. -/
private lemma contMDiff_pouSq :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞ (pouSq (I := I) (M := M)) := by
  classical
  refine contMDiff_finset_sum (fun α _ => ?_)
  exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).mul
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff)

/-- The partition-of-unity square `pouSq` is everywhere strictly positive: the
weights sum to `1`, so some weight is strictly positive, and squaring it gives a
strictly positive summand of the non-negative sum. -/
private lemma pouSq_pos (x : M) : 0 < pouSq (I := I) (M := M) x := by
  classical
  have h_sum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have h_nonneg : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 ≤ ((chartAtlasPOU I M) α x) := fun α _ => (chartAtlasPOU I M).nonneg α x
  have h_sum_lt :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), (0 : ℝ) <
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), ((chartAtlasPOU I M) α x) := by
    rw [Finset.sum_const_zero, h_sum]
    exact zero_lt_one
  obtain ⟨α₀, hα₀_mem, hα₀_pos⟩ :=
    Finset.exists_lt_of_sum_lt h_sum_lt
  refine lt_of_lt_of_le (mul_pos hα₀_pos hα₀_pos) ?_
  refine Finset.single_le_sum (f := fun α : M =>
    ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x))
    (fun α hα => mul_nonneg (h_nonneg α hα) (h_nonneg α hα)) hα₀_mem

/-- The partition-of-unity square `pouSq` is nowhere zero. -/
private lemma pouSq_ne_zero (x : M) : pouSq (I := I) (M := M) x ≠ 0 :=
  (pouSq_pos (I := I) (M := M) x).ne'

/-- The reciprocal of the partition-of-unity square. -/
private def pouSqRecip (x : M) : ℝ := (pouSq (I := I) (M := M) x)⁻¹

/-- The reciprocal of the partition-of-unity square is globally `C^∞`: the
reciprocal of a nowhere-zero `C^∞` function is `C^∞`. -/
private lemma contMDiff_pouSqRecip :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞ (pouSqRecip (I := I) (M := M)) :=
  (contMDiff_pouSq (I := I) (M := M)).inv₀ (pouSq_ne_zero (I := I) (M := M))

/-- The smooth compactly-supported `(r, s)`-tensor section `Φ⁻¹ • T`, the
reciprocal of the partition-of-unity square scaling `T`. -/
private def reconSeed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  smoothFnSmul (I := I) (M := M) g r s
    (pouSqRecip (I := I) (M := M)) (contMDiff_pouSqRecip (I := I) (M := M)) T

/-- **The doubly-weighted reconstruction.** For every smooth compactly-supported
`(r, s)`-tensor section `T`, the sum, over the finite partition-of-unity support
`Finset`, of the doubly partition-of-unity-weighted, `Φ⁻¹`-scaled sections
`pouSmul g r s α (pouSmul g r s α (Φ⁻¹ • T))` equals `T`. -/
private lemma sum_pouSmul_pouSmul_reconSeed_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T)) = T := by
  classical
  refine SmoothCcTensor.ext (ContMDiffSection.ext (fun x => ?_))
  have h_eval :
      (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection x =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection x := by
    have h_sum_section :
        (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))).toSection =
          ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            (pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))).toSection :=
      map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g)
        (r := r) (s := s)) _ _
    rw [h_sum_section]
    have h_coe : ⇑(∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ⇑(pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection :=
      map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
        (fun x : M => TensorRSSpace r s I x)) _ _
    have h_eval' := congrFun h_coe x
    rw [Finset.sum_apply] at h_eval'
    exact h_eval'
  rw [h_eval]
  have h_summand : ∀ α : M,
      (pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T))).toSection x =
        (((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x) *
            pouSqRecip (I := I) (M := M) x) • T.toSection x := by
    intro α
    rw [pouSmul_toSection_apply, pouSmul_toSection_apply]
    rw [show (reconSeed (I := I) (M := M) g r s T) =
        smoothFnSmul (I := I) (M := M) g r s
          (pouSqRecip (I := I) (M := M)) (contMDiff_pouSqRecip (I := I) (M := M))
          T from rfl,
      smoothFnSmul_toSection_apply, smul_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun α _ => h_summand α), ← Finset.sum_smul]
  have h_weight :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x) *
            pouSqRecip (I := I) (M := M) x = 1 := by
    rw [← Finset.sum_mul]
    change pouSq (I := I) (M := M) x * (pouSq (I := I) (M := M) x)⁻¹ = 1
    exact mul_inv_cancel₀ (pouSq_ne_zero (I := I) (M := M) x)
  rw [h_weight, one_smul]

/-- If every canonical Euclidean chart component of `w` is the zero `L²` class,
then the global `L²` inner product of any partition-of-unity-weighted concrete
section `pouSmul g r s α Sg` (with `Sg` supported inside the chart-`α` source)
against `w` is zero. -/
private lemma inner_pouSmul_eq_zero_of_chartComponent_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (w : TensorL2 r s g)
    (hw : ∀ Q : CompIdx E r s,
      tensorL2ChartComponent (I := I) (M := M) g r s w α Q = 0) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), w⟫_ℝ : ℝ) = 0 := by
  classical
  rw [tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (I := I) (M := M) g r s α w Sg hSg]
  have h_each : ∀ Q : CompIdx E r s,
      ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] 0 := by
    intro Q
    have h0 : ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α] 0 := by
      rw [hw Q]
      exact Lp.coeFn_zero (E := ℝ) (p := 2)
        (μ := chartL2Measure (I := I) (M := M) α)
    exact h0
  have h_integrand_ae :
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] 0 := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        ∀ Q : CompIdx E r s,
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro Q
      filter_upwards [h_each Q] with y hy using hy
    filter_upwards [h_all] with y hy
    change densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y) = 0
    have h_sum_zero :
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y) = 0 := by
      refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ => ?_))
      rw [hy Q, mul_zero]
    rw [h_sum_zero, mul_zero]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [setIntegral_congr_ae hctE_meas
    ((ae_restrict_iff' hctE_meas).mp h_integrand_ae)]
  exact integral_zero EuclN ℝ

/-- An abstract `L²` tensor element all of whose canonical Euclidean chart
components vanish is zero. -/
private lemma tensorL2_eq_zero_of_chartComponent_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (w : TensorL2 r s g)
    (hw : ∀ (α : M) (Q : CompIdx E r s),
      tensorL2ChartComponent (I := I) (M := M) g r s w α Q = 0) :
    w = 0 := by
  classical
  refine inner_self_eq_zero (𝕜 := ℝ) |>.mp ?_
  have h_dense : DenseRange ((↑) :
      SmoothCcTensor g r s → UniformSpace.Completion (SmoothCcTensor g r s)) :=
    UniformSpace.Completion.denseRange_coe
  have h_on_smooth : ∀ T : SmoothCcTensor g r s,
      (⟪w, (T : TensorL2 r s g)⟫_ℝ : ℝ) = 0 := by
    intro T
    have h_recon :
        (T : TensorL2 r s g) =
          ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            ((pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))) : TensorL2 r s g) := by
      have h_map := map_sum
        (UniformSpace.Completion.toComplL :
          SmoothCcTensor g r s →L[ℝ] TensorL2 r s g)
        (fun α : M => pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T)))
        (chartAtlasPOU_finset (I := I) (M := M))
      rw [sum_pouSmul_pouSmul_reconSeed_eq (I := I) (M := M) g r s T] at h_map
      rw [show ((T : TensorL2 r s g)) =
          (UniformSpace.Completion.toComplL :
            SmoothCcTensor g r s →L[ℝ] TensorL2 r s g) T from rfl, h_map]
      rfl
    rw [h_recon, inner_sum]
    refine Finset.sum_eq_zero (fun α _ => ?_)
    have hSg : tsupport
        (pouSmul (I := I) (M := M) g r s α
          (reconSeed (I := I) (M := M) g r s T)).toFun ⊆ (chartAt H α).source :=
      pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α
        (reconSeed (I := I) (M := M) g r s T)
    rw [real_inner_comm]
    exact inner_pouSmul_eq_zero_of_chartComponent_eq_zero
      (I := I) (M := M) g r s α
      (pouSmul (I := I) (M := M) g r s α (reconSeed (I := I) (M := M) g r s T))
      hSg w (fun Q => hw α Q)
  have h_zero : (fun x : TensorL2 r s g => (⟪w, x⟫_ℝ : ℝ)) =
      (fun _ : TensorL2 r s g => (0 : ℝ)) := by
    refine h_dense.equalizer ?_ continuous_const ?_
    · exact (innerSL ℝ w).continuous
    · funext T
      exact h_on_smooth T
  exact congrFun h_zero w

/-- **An `L²` tensor element is determined by its chart components.**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless) smooth
manifold `M`, and fix tensor ranks `(r, s)`. Two abstract elements
`u v : TensorL2 r s g` of the metric `L²` Hilbert space of `(r, s)`-tensor
fields with identical families of canonical Euclidean chart components — i.e.
`tensorL2ChartComponent g r s u α P₀ = tensorL2ChartComponent g r s v α P₀` for
every chart center `α : M` and component multi-index `P₀` — are equal.

Equivalently, the family of canonical Euclidean chart components
`tensorL2ChartComponent` jointly separates points of `TensorL2 r s g`: an `L²`
tensor element is fully determined by the partition-of-unity-weighted
chart-coordinate scalar fields read off in every chart and every component
direction. -/
theorem tensorL2_eq_of_chartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u v : TensorL2 r s g)
    (h : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s v α P₀) :
    u = v := by
  classical
  rw [← sub_eq_zero]
  refine tensorL2_eq_zero_of_chartComponent_eq_zero (I := I) (M := M)
    g r s (u - v) (fun α P₀ => ?_)
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    map_sub, tensorL2ChartComponentCLM_apply, tensorL2ChartComponentCLM_apply,
    h α P₀, sub_self]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (u v : TensorL2 r s g)
    (h : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s v α P₀) :
    u = v :=
  tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s u v h

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
