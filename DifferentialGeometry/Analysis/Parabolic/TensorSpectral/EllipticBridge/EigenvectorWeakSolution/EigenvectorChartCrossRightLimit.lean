import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossLimits
import DifferentialGeometry.Geometry.Gradient

/-!
# The cross-right covariant-Leibniz term as an `n → ∞` `L²`-limit, recast at rank `(r, s)`

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix an eigenbasis
index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center
`α : M`, and a fixed smooth compactly-supported `(r, s)`-tensor *test section*
`S`. Write `ζ_α := chartAtlasPOU I M α` for the chart-atlas partition-of-unity
weight and `wₙ := eigenvectorSmoothApprox g r s i n` for the
canonical smooth `H¹`-approximating sequence of the eigenvector resolvent.

The sibling file `EigenvectorChartCrossLimits` analysed the cross-right term
`tensorCovDerivCrossRight g r s ζ_α wₙ S` only up to the genuine
`(r, s + 1)`-tensor `L²` pairing
`⟪covGrad g r s S, prependCovGradSlot g r s ζ_α wₙ⟫`
(`tensorCovDerivCrossRight_integral_eq_inner`). That `(r, s + 1)` form cannot be
chart-pulled directly: the abstract chart-pull
`tensorL2Inner_cutoff_chartKernelSupported_pull` needs the *concrete* section to
sit inside `tsupport ζ_α`, whereas `covGrad g r s S` is supported throughout the
chart. This file *recasts* the cross-right integral at rank `(r, s)`.

## The recast

The cross-right term carries the approximant `w` undifferentiated; its explicit
form `tensorCovDerivCrossRight_def` is an inverse-Gram-weighted double sum of
`∂ₖζ` against the `(r, s)`-tensor pointwise inner product `⟨w, ∇S⟩`. Pushing the
inverse-Gram weight and the covector factor `dζ` into the second argument of the
pointwise inner product, the double sum collapses to a single `(r, s)`-tensor
pointwise inner product

  `tensorCovDerivCrossRight g r s ζ w S x =
     tensorInnerPointwise g r s x (w.toFun x) (covDerivAlongGrad g r s S ζ).toFun x`,

where `covDerivAlongGrad g r s S ζ` is the covariant derivative of `S` taken
along the gradient vector field of the scalar `ζ`. The collapse is the
metric-sharp identity `gradFun g ζ x = ∑ⱼ (∑ᵢ (G⁻¹)ᵢⱼ ∂ᵢζ) eⱼ`, which feeds the
inverse-Gram-weighted sum of directional covariant derivatives into a single
directional covariant derivative along `gradFun g ζ x`.

The covariant derivative along the gradient field is a *concrete*
`(r, s)`-tensor section supported inside `tsupport ζ` — the gradient field
vanishes wherever `ζ` is locally constant — so the rank-`(r, s)` chart-pull
applies.

## The covariant derivative along a vector field

`covDerivAlong g r s S V` — the covariant derivative of a smooth
compactly-supported `(r, s)`-tensor section `S` along a smooth tangent-vector
section `V` — is the smooth `(r, s)`-tensor section
`x ↦ tensorCovDerivAt g r s S x (V x)`. Smoothness is `clm_bundle_apply`: the
covariant-gradient-bundle section of `S` is a smooth `Hom(TM, T^{(r,s)})`
section, applied to the smooth vector section `V`. `covDerivAlongGrad g r s S ζ`
is the special case `V := gradFun g ζ`.

## Main definitions

* `covDerivAlong g r s S V` — the covariant derivative of `S` along the smooth
  vector field `V`, a smooth compactly-supported `(r, s)`-tensor section.
* `covDerivAlongGrad g r s S ζ` — the covariant derivative of `S` along the
  gradient vector field of the smooth scalar `ζ`.
* `crossRightLimitComponent g r s i α P` — the `n → ∞` limit
  object of the cutoff chart component of the cross-right approximants: the
  cutoff chart component of the abstract `L²` limit `TensorH1ComplToTensorL2 g r
  s (eigenvectorResolvent g r s i)`.

## Main results

* `tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad` — the pointwise recast
  of the cross-right term as a rank-`(r, s)` tensor pointwise inner product.
* `tensorCovDerivCrossRight_integral_eq_innerLow` — the per-approximant rewrite
  of the cross-right integral as the rank-`(r, s)` abstract `L²` pairing
  `⟪w, covDerivAlongGrad g r s S ζ⟫`.
* `tensorCovDerivCrossRight_integral_eq_chartPull` — the per-approximant rewrite
  of the cross-right integral as a single-chart Euclidean integral.
* `tensorCovDerivCrossRight_integral_tendsto` — the cross-right
  integral converges, as `n → ∞`, to the rank-`(r, s)` abstract `L²` pairing of
  the fixed abstract limit.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
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
open DifferentialGeometry.Integral.DivergenceTheorem
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

/-- Scalar form of `extDerivFun`: applied to an `ℝ`-valued function and a
tangent vector, it is exactly the manifold-Fréchet derivative — the cast
`NormedSpace.fromTangentSpace` on the `ℝ` value side is the identity. -/
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl

/-- The directional covariant derivative of an `(r, s)`-tensor section along the
zero direction is the zero `(r, s)`-tensor: it is the bundled covariant
derivative — a continuous linear map in the direction — applied to `0`. -/
private lemma tensorCovDerivAt_zero_dir
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivAt (I := I) (M := M) g r s S x (0 : E) = 0 := by
  rw [tensorCovDerivAt_def]
  exact ContinuousLinearMap.map_zero _

/-- **The metric-sharp basis decomposition of the gradient.** For a smooth
scalar `ζ` and a point `x`, the gradient vector field `gradFun g ζ x` equals the
inverse-Gram-weighted combination of the fixed model-fibre basis
`∑ⱼ (∑ᵢ (G(x)⁻¹)ᵢⱼ · ∂ᵢζ) • eⱼ`, where `∂ᵢζ = extDerivFun ζ x eᵢ`.

The proof checks, by the basis-extensionality of linear functionals and the
injectivity of the metric flat map, that the metric inner product of the
right-hand side against each basis vector `eₖ` recovers `∂ₖζ`: the
inverse-Gram-weighted sum telescopes through the Gram identity
`G(x)⁻¹ · G(x) = 1`. -/
private lemma gradFun_eq_gramInv_sum
    (g : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    gradFun (I := I) g (ζ : M → ℝ) x =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
          (chartModelBasis E) j := by
  classical
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  set rhs : TangentSpace I x :=
    ∑ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        Ginv i j * extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
        (chartModelBasis E) j with hrhs
  refine (metricFlatLinear_injective (I := I) g x ?_).symm
  refine (chartModelBasis E).ext ?_
  intro k
  have hgrad_k : metricFlatLinear (I := I) g x
      (gradFun (I := I) g (ζ : M → ℝ) x) ((chartModelBasis E) k) =
        extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) k) := by
    rw [metricFlatLinear_apply, extDerivFun_apply_scalar]
    exact inner_gradFun (I := I) g (ζ : M → ℝ) x ((chartModelBasis E) k)
  have hrhs_k : metricFlatLinear (I := I) g x rhs ((chartModelBasis E) k) =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          Ginv i j * extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) *
          gramMatrixAt (I := I) (M := M) g x j k := by
    rw [metricFlatLinear_apply, hrhs]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, gramMatrixAt_apply]
  have hgram : ∀ i : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i k := by
    intro i
    have hmul := gramMatrixAt_inv_mul_self (I := I) (M := M) g x
    have hentry := congrFun (congrFun hmul i) k
    rw [Matrix.mul_apply] at hentry
    rw [hGinv]
    exact hentry
  calc metricFlatLinear (I := I) g x rhs ((chartModelBasis E) k)
      = ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            Ginv i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) *
            gramMatrixAt (I := I) (M := M) g x j k := hrhs_k
    _ = ∑ j : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
              (Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = ∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            (∑ j : Fin (Module.finrank ℝ E),
              Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
              i k := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hgram i]
    _ = extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) k) := by
        rw [Finset.sum_eq_single k]
        · rw [Matrix.one_apply_eq, mul_one]
        · intro i _ hik
          rw [Matrix.one_apply_ne hik, mul_zero]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
    _ = metricFlatLinear (I := I) g x
          (gradFun (I := I) g (ζ : M → ℝ) x) ((chartModelBasis E) k) :=
        hgrad_k.symm

/-- The covariant-gradient-bundle section of a smooth compactly-supported
`(r, s)`-tensor section `S`: the continuous-linear-map–valued function sending a
base point `x` to the directional covariant derivative
`v ↦ tensorCovDerivAt g r s S x v`. -/
private noncomputable def covDerivHomSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x

/-- The covariant-gradient-bundle section, evaluated bilinearly at a base point
`x` and a direction `v`, equals the directional covariant derivative
`tensorCovDerivAt g r s S x v`. -/
private lemma covDerivHomSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    covDerivHomSection (I := I) (M := M) g r s S x v =
      tensorCovDerivAt (I := I) (M := M) g r s S x v := rfl

/-- The covariant-gradient-bundle section is a `C^∞` section of the
covariant-gradient bundle `Hom(TM, T^{(r,s)})`.

This is the `contMDiff` field of the `ContMDiffCovariantDerivative` instance
carried by the bundled `(r, s)`-tensor covariant derivative, applied to the
smooth section `S.toSection`. -/
private lemma covDerivHomSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covDerivHomSection (I := I) (M := M) g r s S x⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    with hcovLC
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => S.toSection y) x⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

/-- The smoothness of the directional-covariant-derivative section
`x ↦ tensorCovDerivAt g r s S x (V x)`, as a `C^∞` section of the
`(r, s)`-tensor bundle in total-space form.

It is `ContMDiff.clm_bundle_apply` applied to the smooth covariant-gradient-bundle
section `covDerivHomSection g r s S` of `S` and the smooth vector section `V`. -/
private lemma covDerivAlong_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, tensorCovDerivAt (I := I) (M := M) g r s S x (V x)⟩ :
          TotalSpace (TensorRSModel r s ℝ E)
            fun y : M => TensorRSSpace r s I y)) := by
  have hϕ := covDerivHomSection_contMDiff (I := I) (M := M) g r s S
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, V x⟩ :
        TotalSpace E (TangentSpace I : M → Type _))) :=
    V.contMDiff
  exact ContMDiff.clm_bundle_apply hϕ hv

/-- The underlying section value of the covariant derivative along `V`, as a
`C^∞` section of the `(r, s)`-tensor bundle: the function sending a base point
`x` to the directional covariant derivative `tensorCovDerivAt g r s S x (V x)`.
Smoothness is `clm_bundle_apply` applied to the smooth covariant-gradient-bundle
section of `S` and the smooth vector section `V`. -/
private noncomputable def covDerivAlongSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I :=
    tensorRSBundle_smooth ∞ r s
  (ContMDiffSection.mk
      (fun x : M => tensorCovDerivAt (I := I) (M := M) g r s S x (V x))
      (covDerivAlong_section_contMDiff (I := I) (M := M) g r s S V) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)

/-- The section value of `covDerivAlongSection g r s S V` at `x` is the
directional covariant derivative `tensorCovDerivAt g r s S x (V x)`. -/
private lemma covDerivAlongSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivAlongSection (I := I) (M := M) g r s S V x =
      tensorCovDerivAt (I := I) (M := M) g r s S x (V x) := rfl

/-- The underlying model-valued map of `covDerivAlongSection g r s S V` vanishes
at every point outside `tsupport S.toFun`.

The directional covariant derivative `tensorCovDerivAt g r s S x` is the zero
continuous linear map there (by `tensorCovDerivAt_eq_zero_off_tsupport`); applied
to `V x` it is the zero `(r, s)`-tensor. -/
private lemma covDerivAlongSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∉ tsupport S.toFun) :
    TensorRSSpace.toModel
      (covDerivAlongSection (I := I) (M := M) g r s S V x) = 0 := by
  rw [covDerivAlongSection_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hx (V x),
    TensorRSSpace.toModel_zero]

/-- The underlying model-valued map of `covDerivAlongSection g r s S V` has
compact support: it vanishes outside `tsupport S.toFun`, which is compact. -/
private lemma covDerivAlongSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covDerivAlongSection (I := I) (M := M) g r s S V x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covDerivAlongSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s S V hxnot)

/-- **The covariant derivative along a smooth vector field.** The covariant
derivative of a smooth compactly-supported `(r, s)`-tensor section `S` along a
smooth tangent-vector section `V`, as a smooth compactly-supported
`(r, s)`-tensor section.

Pointwise, its underlying section value at a base point `x` is the directional
covariant derivative `tensorCovDerivAt g r s S x (V x)` of `S` along the tangent
vector `V x`. -/
noncomputable def covDerivAlong
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    SmoothCcTensor g r s where
  toSection := covDerivAlongSection (I := I) (M := M) g r s S V
  hasCompactSupport :=
    covDerivAlongSection_hasCompactSupport (I := I) (M := M) g r s S V

/-- The underlying section value of `covDerivAlong g r s S V` at `x` is the
directional covariant derivative `tensorCovDerivAt g r s S x (V x)`. -/
lemma covDerivAlong_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x (V x) := rfl

/-- The underlying model-valued map of `covDerivAlong g r s S V` at `x` is the
model coercion of the directional covariant derivative
`tensorCovDerivAt g r s S x (V x)`. -/
lemma covDerivAlong_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x (V x)) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlong_toSection_apply]

/-- The underlying tensor field of `covDerivAlong g r s S V` has topological
support inside the closed support of `S`: the directional covariant derivative
vanishes wherever `S` does. -/
lemma covDerivAlong_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    tsupport (covDerivAlong (I := I) (M := M) g r s S V).toFun ⊆
      tsupport S.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  rw [covDerivAlong_toFun_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hxnot (V x),
    TensorRSSpace.toModel_zero]

/-- **The covariant derivative along the gradient of a scalar.** The covariant
derivative of a smooth compactly-supported `(r, s)`-tensor section `S` along the
gradient vector field of the smooth scalar `ζ`, as a smooth compactly-supported
`(r, s)`-tensor section.

It is `covDerivAlong g r s S` applied to the smooth gradient vector field
`grad_g g ζ.contMDiff` of `ζ`. -/
noncomputable def covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    SmoothCcTensor g r s :=
  covDerivAlong (I := I) (M := M) g r s S
    (grad_g (I := I) g ζ.contMDiff)

/-- The underlying section value of `covDerivAlongGrad g r s S ζ` at `x` is the
directional covariant derivative `tensorCovDerivAt g r s S x (gradFun g ζ x)` of
`S` along the gradient of `ζ`. -/
lemma covDerivAlongGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (gradFun (I := I) g (ζ : M → ℝ) x) := by
  rw [covDerivAlongGrad, covDerivAlong_toSection_apply, grad_g_apply]

/-- The underlying tensor field of `covDerivAlongGrad g r s S ζ` at `x` is the
model coercion of `tensorCovDerivAt g r s S x (gradFun g ζ x)`. -/
lemma covDerivAlongGrad_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x
          (gradFun (I := I) g (ζ : M → ℝ) x)) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlongGrad_toSection_apply]

/-- **Support of the covariant derivative along the gradient.** For a smooth
scalar `ζ` and a smooth compactly-supported `(r, s)`-tensor section `S`, the
covariant derivative `covDerivAlongGrad g r s S ζ` of `S` along the gradient of
`ζ` has topological support inside the closed support of `ζ`.

The underlying tensor field is `x ↦ toModel (∇_{gradζ x} S)`; off the closed
support of `ζ` the gradient field `gradFun g ζ x` vanishes
(`support_gradFun_subset`), so the directional covariant derivative — being
linear in the direction — is the zero tensor there.

This is the support hypothesis required by the chart-pull
`tensorL2Inner_cutoff_chartKernelSupported_pull` (instantiated at `ζ :=
chartAtlasPOU I M α`). -/
lemma covDerivAlongGrad_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    tsupport (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  have hgrad_zero : gradFun (I := I) g (ζ : M → ℝ) x = (0 : TangentSpace I x) := by
    by_contra hne
    exact hxnot (support_gradFun_subset (I := I) g (ζ : M → ℝ)
      (by rw [Function.mem_support]; exact hne))
  rw [covDerivAlongGrad_toFun_apply, hgrad_zero,
    tensorCovDerivAt_zero_dir (I := I) (M := M) g r s S x,
    TensorRSSpace.toModel_zero]

/-- The rank-`(r, s)` pointwise tensor inner product against a fixed first
argument `A`, packaged as an additive group homomorphism in the second
argument. Additivity is `tensorInnerPointwise_add_right` and the zero is
`tensorInnerPointwise_zero_right`. -/
private noncomputable def tensorInnerPointwiseRightHom
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E →+ ℝ where
  toFun := fun T => tensorInnerPointwise (I := I) (M := M) g r s x A T
  map_zero' := tensorInnerPointwise_zero_right (I := I) (M := M) g r s x A
  map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g r s x A

/-- Right-distributivity of the rank-`(r, s)` pointwise tensor inner product
over a double sum: for a fixed first argument `A` and a doubly-indexed family
`T`, the pointwise inner product of `A` against the double sum `∑ᵢ ∑ⱼ T i j` is
the double sum of the pointwise inner products. This is `map_sum` of the
additive hom `tensorInnerPointwiseRightHom`, applied to the two summations. -/
private lemma tensorInnerPointwise_sum_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E)
    (T : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x A (T i j) := by
  classical
  have h := map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun i => ∑ j : Fin (Module.finrank ℝ E), T i j) Finset.univ
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) from rfl]
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun j => T i j) Finset.univ

/-- The inverse-Gram-weighted combination of the basis-directional covariant
derivatives of `S` is the directional covariant derivative of `S` along the
gradient of `ζ`: pushing the model coercion and the directional linearity of
`tensorCovDerivAt` through, the metric-sharp basis decomposition
`gradFun_eq_gramInv_sum` collapses the double sum to a single direction. -/
private lemma gramInv_sum_covDeriv_eq_covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
            TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((chartModelBasis E) j)) =
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x := by
  classical
  set D : TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun y : M => S.toSection y) x with hD
  set toM : TensorRSSpace r s I x ≃L[ℝ] TensorRSModel r s ℝ E :=
    tensorRSSpace_continuousLinearEquiv (I := I) r s x with htoM
  have hcov : ∀ v : E,
      tensorCovDerivAt (I := I) (M := M) g r s S x v = D v := fun v => rfl
  have hgoal_rhs :
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
        toM (D (gradFun (I := I) g (ζ : M → ℝ) x)) := by
    rw [covDerivAlongGrad_toFun_apply, hcov]
    rfl
  rw [hgoal_rhs]
  have htoModel_cov : ∀ j : Fin (Module.finrank ℝ E),
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j)) =
        toM (D ((chartModelBasis E) j)) := by
    intro j
    rw [hcov]
    rfl
  have hlhs :
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)) =
        toM (D (∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
            (chartModelBasis E) j)) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j))
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
                toM (D ((chartModelBasis E) j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [htoModel_cov j]
      _ = ∑ j : Fin (Module.finrank ℝ E),
            toM (D ((∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              (chartModelBasis E) j)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul D, map_smul toM, Finset.sum_smul]
      _ = toM (D (∑ j : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              (chartModelBasis E) j)) := by
          rw [map_sum D, map_sum toM]
  rw [hlhs]
  rw [← gradFun_eq_gramInv_sum (I := I) g ζ x]

/-- **The pointwise recast of the cross-right term at rank `(r, s)`.** For a
closed Riemannian manifold `(M, g)`, a smooth scalar `ζ`, and smooth
compactly-supported `(r, s)`-tensor sections `w`, `S`, the cross-right term
`tensorCovDerivCrossRight g r s ζ w S` of the covariant Leibniz rule equals, at
every point `x`, the rank-`(r, s)` tensor pointwise inner product
`tensorInnerPointwise g r s x` of the section value `w.toFun x` against the
underlying tensor field of the covariant derivative `covDerivAlongGrad g r s S ζ`
of `S` along the gradient of `ζ`.

The cross-right term carries `w` undifferentiated; its explicit
inverse-Gram-weighted double sum, with the inverse-Gram weight and the
differentiation factor `∂ᵢζ` pushed into the second argument of the
`ℝ`-bilinear pointwise inner product `⟨w, ·⟩`, collapses to the single inner
product against the directional covariant derivative along the metric sharp
`gradFun g ζ x` of `dζ`. -/
theorem tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (w.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x) := by
  classical
  rw [tensorCovDerivCrossRight_def]
  rw [← gramInv_sum_covDeriv_eq_covDerivAlongGrad (I := I) (M := M) g r s ζ S x]
  rw [tensorInnerPointwise_sum_sum_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tensorInnerPointwise_smul_right]
  ring

/-- **The cross-right integral as a rank-`(r, s)` abstract `L²` pairing.** For a
smooth scalar `ζ`, a smooth compactly-supported `(r, s)`-tensor section `w`, and
a fixed smooth compactly-supported `(r, s)`-tensor section `S`, the integral of
the cross-right term `tensorCovDerivCrossRight g r s ζ w S` against the
Riemannian volume measure equals the metric `L²` inner product of the
`L²`-coercion of `w` against the `L²`-coercion of the covariant derivative
`covDerivAlongGrad g r s S ζ` of `S` along the gradient of `ζ`.

The proof integrates the pointwise recast
`tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad`, then reads the integral
of a pointwise tensor inner product of two smooth sections as their `L²` inner
product. -/
theorem tensorCovDerivCrossRight_integral_eq_innerLow
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪(w : TensorL2 r s g),
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ :
          SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ := by
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def w
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ),
    tensorL2Inner]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w S x

/-- **The cross-right integral as a single-chart Euclidean integral.** For a
chart center `α : M`, a smooth compactly-supported `(r, s)`-tensor section `w`,
and a fixed smooth compactly-supported `(r, s)`-tensor section `S`, the integral
of the cross-right term `tensorCovDerivCrossRight g r s (chartAtlasPOU I M α) w S`
equals the single-chart Euclidean integral coupling the cutoff Euclidean chart
components `tensorL2ChartComponentCutoff` of `(w : TensorL2 r s g)` to the raw
Euclidean chart components of the covariant derivative
`covDerivAlongGrad g r s S (chartAtlasPOU I M α)` along the gradient of the
chart-atlas partition-of-unity weight.

The covariant derivative along the gradient is supported inside the closed
support of the partition-of-unity weight (`covDerivAlongGrad_tsupport_subset`),
so the rank-`(r, s)` chart-pull applies. -/
theorem tensorCovDerivCrossRight_integral_eq_chartPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α) w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (w : TensorL2 r s g) α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s
                (covDerivAlongGrad (I := I) (M := M) g r s S
                  (chartAtlasPOU I M α)) α Q y)
        ∂(volume : Measure EuclN) := by
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α) w S]
  exact tensorL2Inner_cutoff_chartKernelSupported_pull (I := I) (M := M)
    g r s α (w : TensorL2 r s g)
    (covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α))
    (covDerivAlongGrad_tsupport_subset (I := I) (M := M) g r s S
      (chartAtlasPOU I M α))

/-- **The `n → ∞` abstract `L²` limit of the approximant `L²`-coercion
(chart-locality-free).** For an eigenbasis index `i`, the `L²`-coercions
`((eigenvectorSmoothApprox g r s i n).toCcTensor : TensorL2 r s g)`
converge, as `n → ∞` and in `TensorL2 r s g`, to the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s i)` of
the eigenvector resolvent. -/
theorem tensorL2_eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))) := by
  have h_clm :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  refine h_clm.congr ?_
  intro n
  rw [Function.comp_apply,
    TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

/-- **The `n → ∞` limit object of the cross-right chart component
(chart-locality-free).** For an eigenbasis index `i`, a chart center `α : M`,
and a component multi-index `P : CompIdx E r s`, the cutoff Euclidean chart
component, at `(α, P)`, of the `L²`-coercion `TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent g r s i)` of the eigenvector resolvent. -/
def crossRightLimitComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

/-- **The `n → ∞` `L²`-convergence of the cross-right chart component
(chart-locality-free).** For an eigenbasis index `i`, a chart center `α : M`,
and a component multi-index `P`, the cutoff Euclidean chart components of the
cross-right approximant `L²`-coercions
`((eigenvectorSmoothApprox g r s i n).toCcTensor : TensorL2 r s g)`
converge, as `n → ∞` and in `Lp ℝ 2 (chartL2Measure α)`, to the limit object
`crossRightLimitComponent g r s i α P`. -/
theorem crossRightComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)
        α P)
      atTop
      (𝓝 (crossRightLimitComponent (I := I) (M := M)
        g r s i α P)) := by
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s
        α P).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

/-- **The `n → ∞` limit of the cross-right integral (chart-locality-free).** For
a chart center `α : M`, an eigenbasis index `i`, and a fixed smooth
compactly-supported `(r, s)`-tensor test section `S`, the cross-right integrals
`∫ tensorCovDerivCrossRight g r s (chartAtlasPOU I M α)
(eigenvectorSmoothApprox g r s i n).toCcTensor S` converge, as
`n → ∞`, to the metric `L²` inner product of the fixed abstract limit
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s i)`
against the `L²`-coercion of the covariant derivative
`covDerivAlongGrad g r s S (chartAtlasPOU I M α)` of `S` along the gradient of
the chart-atlas partition-of-unity weight. -/
theorem tensorCovDerivCrossRight_integral_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (S : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
            SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ)) := by
  have h_clm :=
    ((innerSL ℝ
        ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
          SmoothCcTensor g r s) :
          TensorL2 r s g)).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, innerSL_apply_apply] at h_clm
  rw [real_inner_comm]
  refine h_clm.congr ?_
  intro n
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor S,
    real_inner_comm]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    SmoothCcTensor g r s :=
  covDerivAlong (I := I) (M := M) g r s S V

example (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    SmoothCcTensor g r s :=
  covDerivAlongGrad (I := I) (M := M) g r s S ζ

example (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (w.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x) :=
  tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w S x

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
