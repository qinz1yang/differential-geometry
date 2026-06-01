import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGradCrossBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGradL2

/-!
# The covariant-Leibniz cross terms of an eigenvector approximant as `n → ∞`
# `L²`-limits

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix an eigenbasis
index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center
`α : M`, and a fixed smooth compactly-supported `(r, s)`-tensor *test section*
`S`. Write `ζ_α := chartAtlasPOU I M α` for the chart-atlas partition-of-unity
weight and `wₙ := eigenvectorSmoothApprox g r s i n` for the
canonical smooth `H¹`-approximating sequence of the eigenvector resolvent.

The variational-identity assembly that promotes the abstract eigenvector to a
chart-local weak elliptic solution applies a per-approximant chart identity to
`Tₙ := scalarSmul ζ_α wₙ`. Its Dirichlet term `∫⟨∇Tₙ, ∇S⟩` splits, via the
covariant Leibniz rule `tensorCovDerivPointwiseInner_scalarSmul_left`, into the
genuine-gradient term `∫⟨∇wₙ, ∇(scalarSmul ζ_α S)⟩` corrected by the two cross
terms `∫ tensorCovDerivCrossLeft g r s ζ_α wₙ S` and
`∫ tensorCovDerivCrossRight g r s ζ_α wₙ S`. This file analyses the `n → ∞`
behaviour of those two cross integrals.

## The cross-left term

`tensorCovDerivCrossLeft g r s ζ_α wₙ S` rewrites — via the cross-left
metric-isometry bridge `tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad`
pointwise plus the smooth-case pairing formula `tensorCovGradL2_inner_smooth` —
as the abstract `L²` pairing
`⟪tensorCovGradL2 g r s wₙ, prependCovGradSlot g r s ζ_α S⟫`, where the
covector-prepend section `prependCovGradSlot g r s ζ_α S` is a fixed concrete
chart-supported `(r, s + 1)`-tensor section. The chart-pull
`tensorL2Inner_cutoff_chartKernelSupported_pull` at rank `(r, s + 1)` then
expresses the pairing as a single-chart Euclidean integral against the cutoff
chart component `tensorL2ChartComponentCutoff` of the abstract `L²` element
`tensorCovGradL2 g r s wₙ`.

As `n → ∞`, `tensorCovGradL2 g r s wₙ =
tensorCovGradL2Compl g r s (smoothToTensorH1Compl g r s wₙ)` converges, by
`eigenvectorSmoothApprox_tendsto` and continuity of
`tensorCovGradL2Compl`, to
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s i)`. Since
`tensorL2ChartComponentCutoff` is the coercion of a continuous linear map, the
chart integrand converges in `Lp ℝ 2 (chartL2Measure α)`, and the cross-left
integral converges to the chart-Euclidean integral built from that abstract
limit.

## The cross-right term

`tensorCovDerivCrossRight g r s ζ_α wₙ S` carries `wₙ` *undifferentiated*. The
pointwise symmetry `tensorCovDerivCrossRight g r s ζ w S =
tensorCovDerivCrossLeft g r s ζ S w` (`tensorCovDerivCrossRight_eq_crossLeft`)
re-expresses it through the cross-left term with the two tensor sections
swapped. Composing with the cross-left metric-isometry bridge and the
smooth-case pairing formula yields the per-approximant rewrite of the
cross-right integral as the genuine `(r, s + 1)`-tensor `L²` pairing
`⟪covGrad g r s S, prependCovGradSlot g r s ζ_α wₙ⟫`.

## Main definitions

* `crossLeftLimitComponent g r s i α P` — the `n → ∞` limit of the
  cutoff chart component of `tensorCovGradL2 g r s wₙ`: the cutoff chart
  component of the abstract `L²` limit `tensorCovGradL2Compl g r s
  (eigenvectorResolvent g r s i)`.

## Main results

* `tensorCovDerivCrossLeft_integral_eq_inner` — the per-approximant rewrite of
  the cross-left integral as the abstract `L²` pairing.
* `tensorCovDerivCrossLeft_integral_eq_chartPull` — the per-approximant rewrite
  of the cross-left integral as the single-chart Euclidean integral.
* `crossLeftComponent_tendsto` — the cutoff chart components of the
  cross-left approximants converge, in `Lp ℝ 2 (chartL2Measure α)`, to
  `crossLeftLimitComponent`.
* `tensorCovDerivCrossLeft_integral_tendsto` — the cross-left
  integral converges, as `n → ∞`, to the abstract `L²` pairing of the fixed
  limit.
* `tensorCovDerivCrossRight_eq_crossLeft` — the pointwise cross-right/cross-left
  symmetry.
* `tensorCovDerivCrossRight_integral_eq_inner` — the per-approximant rewrite of
  the cross-right integral as the genuine `(r, s + 1)`-tensor `L²` pairing.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The covariant gradient `covGrad g r s w` vanishes — as an `(r, s + 1)`-tensor
field — at every point outside `tsupport w.toFun`. The directional covariant
derivative `tensorCovDerivAt g r s w x` is the zero continuous linear map there
(`tensorCovDerivAt_eq_zero_off_tsupport`), and the covariant-gradient bundle
equivalence sends the zero fibre to the zero `(r, s + 1)`-tensor. -/
private lemma covGrad_toFun_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport w.toFun) :
    (covGrad (I := I) (M := M) g r s w).toFun x = 0 := by
  have hcov_zero :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => w.toSection y) x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.zero_apply]
    exact tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s w hx v
  rw [SmoothCcTensor.toFun_apply, covGrad_toSection_apply, hcov_zero, map_zero,
    TensorRSSpace.toModel_zero]

/-- The smooth-scalar-weighted section `scalarSmul g r s ζ w` has topological
support inside the closed support of the scalar `ζ`: the underlying tensor field
`ζ x • w.toFun x` vanishes wherever `ζ` vanishes. -/
private lemma scalarSmul_toFun_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) {x : M}
    (hx : x ∉ tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toFun x = 0 := by
  have hζx : ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  rw [scalarSmul_toFun_apply, hζx, zero_smul]

private lemma scalarSmul_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) :
    tsupport (scalarSmul (I := I) (M := M) g r s ζ w).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  exact hx (scalarSmul_toFun_eq_zero_off_tsupport (I := I) (M := M) g r s ζ w
    hx_notin)

/-- **Support of the covector-prepend section.** For a smooth scalar `ζ` and a
smooth compactly-supported `(r, s)`-tensor section `S`, the covector-prepend
section `prependCovGradSlot g r s ζ S` has topological support inside the closed
support of `ζ`.

The covector-prepend section is the difference `covGrad g r s (scalarSmul ζ S) -
scalarSmul ζ (covGrad g r s S)`; both summands vanish off the closed support of
`ζ`, the first because `scalarSmul ζ S` does (`scalarSmul_tsupport_subset`,
`covGrad_toFun_eq_zero_off_tsupport`), the second because the smooth-scalar
weight `ζ` does. -/
private lemma prependCovGradSlot_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) :
    tsupport (prependCovGradSlot (I := I) (M := M) g r s ζ S).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  refine hx ?_
  have hsub : (prependCovGradSlot (I := I) (M := M) g r s ζ S).toFun x =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toFun x -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toFun x := by
    rw [prependCovGradSlot, SmoothCcTensor.toFun_sub]
    rfl
  rw [hsub]
  have hfst : (covGrad (I := I) (M := M) g r s
      (scalarSmul (I := I) (M := M) g r s ζ S)).toFun x = 0 :=
    covGrad_toFun_eq_zero_off_tsupport (I := I) (M := M) g r s
      (scalarSmul (I := I) (M := M) g r s ζ S)
      (fun hx_mem => hx_notin
        (scalarSmul_tsupport_subset (I := I) (M := M) g r s ζ S hx_mem))
  have hsnd : (scalarSmul (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S)).toFun x = 0 :=
    scalarSmul_toFun_eq_zero_off_tsupport (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S) hx_notin
  rw [hfst, hsnd, sub_zero]

/-- **The cross-left integral as an abstract `L²` pairing.** For a smooth scalar
`ζ`, a smooth compactly-supported `H¹` tensor section `w`, and a fixed smooth
compactly-supported `(r, s)`-tensor section `S`, the integral of the cross-left
term `tensorCovDerivCrossLeft g r s ζ w.toCcTensor S` against the Riemannian
volume measure equals the metric `L²` inner product of the covariant-gradient
operator value `tensorCovGradL2 g r s w` against the `L²`-coercion of the
covector-prepend section `prependCovGradSlot g r s ζ S`. -/
theorem tensorCovDerivCrossLeft_integral_eq_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensorH1 g r s)
    (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪tensorCovGradL2 (I := I) (M := M) g r s w,
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ := by
  rw [tensorCovGradL2_inner_smooth (I := I) (M := M) g r s w
    (prependCovGradSlot (I := I) (M := M) g r s ζ S)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  rw [tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w.toCcTensor S x]
  rfl

/-- **The cross-left integral as a single-chart Euclidean integral.** For a chart
center `α : M`, a smooth compactly-supported `H¹` tensor section `w`, and a fixed
smooth compactly-supported `(r, s)`-tensor section `S`, the integral of the
cross-left term `tensorCovDerivCrossLeft g r s (chartAtlasPOU I M α) w.toCcTensor
S` equals the single-chart Euclidean integral coupling the cutoff Euclidean chart
components `tensorL2ChartComponentCutoff` of `tensorCovGradL2 g r s w` to the raw
Euclidean chart components of the covector-prepend section
`prependCovGradSlot g r s (chartAtlasPOU I M α) S`. -/
theorem tensorCovDerivCrossLeft_integral_eq_chartPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (w : SmoothCcTensorH1 g r s) (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α) w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r (s + 1), ∑ Q : CompIdx E r (s + 1),
            covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s w) α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                (prependCovGradSlot (I := I) (M := M) g r s
                  (chartAtlasPOU I M α) S) α Q y)
        ∂(volume : Measure EuclN) := by
  rw [tensorCovDerivCrossLeft_integral_eq_inner (I := I) (M := M) g r s
    (chartAtlasPOU I M α) w S]
  exact tensorL2Inner_cutoff_chartKernelSupported_pull (I := I) (M := M)
    g r (s + 1) α (tensorCovGradL2 (I := I) (M := M) g r s w)
    (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S)
    (prependCovGradSlot_tsupport_subset (I := I) (M := M) g r s
      (chartAtlasPOU I M α) S)

/-- The inverse Gram matrix of `g(x)` on the fixed model-space basis is symmetric:
swapping its two component indices leaves it unchanged. This is the real-case
specialisation of `gramMatrixAt_inv_isHermitian`. -/
private lemma gramMatrixAt_inv_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (k l : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ k l =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ l k := by
  have hHerm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
  have h := hHerm.apply l k
  rwa [star_trivial] at h

/-- **The cross-right / cross-left symmetry.** For a smooth scalar `ζ` and smooth
compactly-supported `(r, s)`-tensor sections `w` and `S`, the cross-right term
`tensorCovDerivCrossRight g r s ζ w S` coincides, at every point, with the
cross-left term `tensorCovDerivCrossLeft g r s ζ S w` — the same cross term with
the two tensor sections swapped.

Unfolding both sides to the explicit inverse-Gram-weighted double sums, the
identity is the symmetry of the pointwise tensor inner product
`tensorInnerPointwise_symm` together with the symmetry of the inverse Gram matrix
`gramMatrixAt_inv_symm`, after exchanging the two summation indices. -/
theorem tensorCovDerivCrossRight_eq_crossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ S w x := by
  classical
  rw [tensorCovDerivCrossRight_def, tensorCovDerivCrossLeft_def]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [gramMatrixAt_inv_symm (I := I) (M := M) g x i j,
    tensorInnerPointwise_symm (I := I) (M := M) g r s x
      (w.toFun x)
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j)))]

/-- **The cross-right integral as a genuine `(r, s + 1)`-tensor `L²` pairing.**
For a smooth scalar `ζ`, a smooth compactly-supported `H¹` tensor section `w`,
and a fixed smooth compactly-supported `(r, s)`-tensor section `S`, the integral
of the cross-right term `tensorCovDerivCrossRight g r s ζ w.toCcTensor S` against
the Riemannian volume measure equals the metric `L²` inner product of the
`L²`-coercion of the covariant gradient `covGrad g r s S` of the fixed test
section against the `L²`-coercion of the covector-prepend section
`prependCovGradSlot g r s ζ w.toCcTensor` carrying the approximant in its
undifferentiated covariant block.

The proof feeds the cross-right / cross-left symmetry into the cross-left
metric-isometry bridge with `S` and `w.toCcTensor` swapped, then reads the
integral of a pointwise tensor inner product of two smooth sections as their
`L²` inner product. -/
theorem tensorCovDerivCrossRight_integral_eq_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensorH1 g r s)
    (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪((covGrad (I := I) (M := M) g r s S : SmoothCcTensor g r (s + 1)) :
          TensorL2 r (s + 1) g),
        ((prependCovGradSlot (I := I) (M := M) g r s ζ w.toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ := by
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def
      (covGrad (I := I) (M := M) g r s S)
      (prependCovGradSlot (I := I) (M := M) g r s ζ w.toCcTensor),
    tensorL2Inner]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  rw [tensorCovDerivCrossRight_eq_crossLeft (I := I) (M := M) g r s ζ
      w.toCcTensor S x,
    tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M)
      g r s ζ S w.toCcTensor x]
  rfl

/-- **The `n → ∞` abstract `L²` limit of the cross-left operator value.** For an
eigenbasis index `i`, the covariant-gradient operator values
`tensorCovGradL2 g r s (eigenvectorSmoothApprox g r s i n)`
converge, as `n → ∞` and in `TensorL2 r (s + 1) g`, to the completion-extended
covariant gradient `tensorCovGradL2Compl g r s` applied to the eigenvector
resolvent `eigenvectorResolvent g r s i`. -/
theorem tensorCovGradL2_eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => tensorCovGradL2 (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
      atTop
      (𝓝 (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))) := by
  have h_clm :=
    ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  refine h_clm.congr ?_
  intro n
  rw [Function.comp_apply,
    tensorCovGradL2Compl_smoothToTensorH1Compl (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

/-- **The `n → ∞` limit object of the cross-left chart component.** For an
eigenbasis index `i`, a chart center `α : M`, and a component multi-index
`P : CompIdx E r (s + 1)`, this is the cutoff Euclidean chart component, at
`(α, P)`, of the completion-extended covariant gradient
`tensorCovGradL2Compl g r s` applied to the eigenvector resolvent
`eigenvectorResolvent g r s i`. -/
def crossLeftLimitComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r (s + 1)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

/-- **The `n → ∞` `L²`-convergence of the cross-left chart component.** For an
eigenbasis index `i`, a chart center `α : M`, and a component multi-index `P`,
the cutoff Euclidean chart components of the cross-left operator values
`tensorCovGradL2 g r s (eigenvectorSmoothApprox g r s i n)`
converge, as `n → ∞` and in `Lp ℝ 2 (chartL2Measure α)`, to the limit object
`crossLeftLimitComponent g r s i α P`. -/
theorem crossLeftComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r (s + 1)) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
        α P)
      atTop
      (𝓝 (crossLeftLimitComponent (I := I) (M := M) g r s i α P)) := by
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r (s + 1)
        α P).continuous.tendsto _).comp
      (tensorCovGradL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

/-- **The `n → ∞` limit of the cross-left integral.** For a chart center
`α : M`, an eigenbasis index `i`, and a fixed smooth compactly-supported
`(r, s)`-tensor test section `S`, the cross-left integrals
`∫ tensorCovDerivCrossLeft g r s (chartAtlasPOU I M α)
(eigenvectorSmoothApprox g r s i n).toCcTensor S` converge, as
`n → ∞`, to the metric `L²` inner product of the fixed abstract limit
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s i)`
against the `L²`-coercion of the covector-prepend section
`prependCovGradSlot g r s (chartAtlasPOU I M α) S`. -/
theorem tensorCovDerivCrossLeft_integral_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (S : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          ((prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ)) := by
  have h_clm :=
    ((innerSL ℝ
        ((prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S :
          SmoothCcTensor g r (s + 1)) :
          TensorL2 r (s + 1) g)).continuous.tendsto _).comp
      (tensorCovGradL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, innerSL_apply_apply] at h_clm
  rw [real_inner_comm]
  refine h_clm.congr ?_
  intro n
  rw [tensorCovDerivCrossLeft_integral_eq_inner (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) S,
    real_inner_comm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
