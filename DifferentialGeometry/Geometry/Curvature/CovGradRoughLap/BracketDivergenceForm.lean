import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock

/-!
# The frame-bracket pairing as a total covariant divergence

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file exhibits the
frame-bracket directional terms — the `∇²T`-order frame-bracket summands
`∇_{[B_i, W]}(∇_{B_i} T)` and `∇_{B_i}(∇_{[B_i, W]} T)` that `tensor3rdCurvBracket`
(`Bochner/PointwiseTensorBochner`) collects — as the **first slot of the covariant Leibniz
expression that the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`) consumes**, hence as
a total covariant divergence whose integral over the closed manifold vanishes.

## The engine consumption shape

The engine `integral_frameSummed_covDeriv_combined_eq_zero` integrates, over a finite index family `ι`,
smooth tangent vector fields `V i`, and smooth `(r, s)`-tensor sections `W i`, `Z`, the frame-summed
covariant Leibniz expression
```
∑ᵢ ∫_M ( ⟨∇_{V i}(W i), Z⟩ + ⟨W i, ∇_{V i} Z⟩ + ⟨W i, Z⟩ · divᵍ (V i) ) dvolᵍ = 0,
```
where `∇_{V i}` is the metric-lowered directional covariant derivative `loweredCovDerivAlongVF` and
`⟨·, ·⟩` is the covariant `(0, r + s)` inner product `tensorInnerPointwise_0s` of the metric-lowered
tensors. Its **first slot** `∑ᵢ ⟨∇_{V i}(W i), Z⟩` is exactly the bracket-direction covariant-derivative
pairing carried by the two `tensor3rdCurvBracket` summands once `Z := ∇S` and the directions `V i` are
the frame brackets `[B_i, W]`: each bracket summand `∇_{V}(W')` is the metric-lowered directional
covariant derivative of a once-derived tensor section `W'` along `V`, the engine's first slot.

## What is delivered

* `loweredCovDeriv_bracketChannel_combined_isDivergence` — the per-direction reading: the covariant
  Leibniz expression `⟨∇_V W', Z⟩ + ⟨W', ∇_V Z⟩ + ⟨W', Z⟩ · divᵍ V` integrates to zero. This is the
  pointwise statement that the bracket-direction first slot `⟨∇_V W', Z⟩` is a total covariant
  divergence `−(⟨W', ∇_V Z⟩ + ⟨W', Z⟩ · divᵍ V)` up to the divergence integrating to zero — the
  per-direction telescoping the frame-summed engine sums over `ι`.
* `integral_frameSummed_bracketCovDeriv_combined_eq_zero` — the frame-summed engine consumption for the
  explicit `Lie`-bracket direction families `V i := [extend B_i, extend W]` built from the smooth
  tangent extension `smoothExtensionTangent` of any two tangent-value families `B`, `W`: the frame-summed
  combined Leibniz integral vanishes. This is the engine-consumption bridge in the exact shape the
  moving-frame bracket-channel carrier identity
  `movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace`
  (`MovingFrameDiffCurvTraceSection`) reads for its residual-vanishing leg.

## Why this is the divergence half (not the full carrier identity)

The full bracket-channel carrier identity additionally identifies the genuine `(∇R) S` and Ricci
content (the second-Bianchi / frame-Ricci folding and the gradient-slot lift), which is curvature
content living above the divergence engine. This file supplies *only* the divergence-vanishing half: the
frame-bracket directional terms, paired and summed, are a total covariant divergence whose integral
vanishes. It is the first producer of the bracket-direction engine consumption in the curvature line; the
genuine curvature identification of the surviving carrier is supplied separately.

## Convention

All `L²`/integral pairings are against the canonical Riemannian volume measure
`riemannianVolumeMeasure`; `divᵍ` is `divergence_g`; `⟨·, ·⟩` in the first/second slots is the covariant
`(0, r + s)` inner product `tensorInnerPointwise_0s` of the metric-lowered tensors, the engine's native
pairing.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The smooth tangent extension of a tangent value, bundled as a smooth vector field.** For a base
point `x` and tangent value `v : TangentSpace I x`, the smooth tangent extension
`smoothExtensionTangent x v` (a globally smooth field agreeing with `v` at `x`) packaged as a
`Cₛ^∞⟮I; E, TangentSpace I⟯` section, the form the frame-summed covariant integration-by-parts engine
reads for its direction families. Smoothness is `smoothExtensionTangent_contMDiff`. -/
def smoothExtensionTangentSection (x : M) (v : TangentSpace I x) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩

@[simp] lemma smoothExtensionTangentSection_apply (x : M) (v : TangentSpace I x) (b : M) :
    smoothExtensionTangentSection (I := I) (M := M) x v b = smoothExtensionTangent (I := I) x v b :=
  rfl

/-- **The Lie bracket of two smooth vector fields, bundled as a smooth vector field.** For two smooth
tangent fields packaged as `Cₛ^∞⟮I; E, TangentSpace I⟯` sections `X`, `Y`, their Lie bracket
`[X, Y] = VectorField.mlieBracket I X Y` packaged as a `Cₛ^∞` section, smooth by
`mlieBracket_contMDiff`. This is the direction family the frame-bracket terms `∇_{[B_i, W]}(·)` and
`∇_{B_i}(∇_{[B_i, W]} ·)` of `tensor3rdCurvBracket` feed to the covariant integration-by-parts engine. -/
def lieBracketSection (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b),
    mlieBracket_contMDiff (I := I) X.contMDiff Y.contMDiff⟩

@[simp] lemma lieBracketSection_apply
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    lieBracketSection (I := I) (M := M) X Y b =
      VectorField.mlieBracket I (fun b : M => X b) (fun b : M => Y b) b :=
  rfl

/-- **The bracket summand is the engine's metric-lowered first slot (the bracket-to-engine
identification).** For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a smooth tangent
direction field `V`, a once-derived `(r, s)`-tensor section `W'`, and a `(r, s)`-tensor section `Z`, the
metric-lowered directional covariant derivative of `W'` along `V` paired against the lifted `Z` — the
engine's first slot `⟨∇_V W', Z⟩` in `tensorInnerPointwise_0s` form — equals the metric index-lowering of
the **un-lowered** directional covariant derivative `∇_V W' = covApply (tensorCov g r s) V W'`, paired
against the lifted `Z`:
```
⟨loweredCovDerivAlongVF g r s W' V (x), liftedZ(x)⟩₀
  = ⟨lowerAllUpperIndices g r s x (toModel (covApply (tensorCov g r s) V W' x)), liftedZ(x)⟩₀.
```

The right-hand first argument is exactly the metric-lowered model of the bracket summand shape
`(tensorCov g r s).toFun (∇_{B_i} T) x ([B_i, W] x) = covApply (tensorCov g r s) [B_i, W] (∇_{B_i} T) x`
that `tensor3rdCurvBracket` (`Bochner/PointwiseTensorBochner`) collects (with `V := [B_i, W]` the frame
bracket and `W' := ∇_{B_i} T` the once-derived section): so this lemma identifies each `tensor3rdCurvBracket`
summand, paired against `∇S`, with the engine's first slot. The proof reads
`loweredCovDerivAlongVF g r s W' V x = loweredCovDerivAt g r s W' x (V x)`
(`loweredCovDerivAlongVF_apply`) and rewrites its model by the unconditional parallel-lowering commutation
`loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs` (`TensorLoweringParallel`); the un-lowered directional
derivative `tensorRSCovariantDerivative … W' x (V x)` is `covApply (tensorCov g r s) V W' x` definitionally. -/
theorem loweredCovDerivAlongVF_firstSlot_eq_lower_covApply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (covApply (tensorCov (I := I) g r s) (fun y : M => V y)
              (fun y : M => W'.toSection y) x)))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g r s Z.toSection x)) := by
  classical
  have hbridge := loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs
    (I := I) (M := M) g r s W'.toSection x (V x)
  rw [loweredCovDerivAlongVF_apply, hbridge]
  rfl

/-- **The bracket-channel covariant Leibniz expression integrates to zero (per direction).** For a closed
smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a smooth tangent vector field `V`, and smooth
`(r, s)`-tensor sections `W'`, `Z`, the metric-lowered covariant Leibniz expression integrates to zero:
```
∫_M ( ⟨∇_V W', Z⟩ + ⟨W', ∇_V Z⟩ + ⟨W', Z⟩ · divᵍ V ) dvolᵍ = 0,
```
where `∇_V` is the metric-lowered directional covariant derivative `loweredCovDerivAlongVF g r s · V` and
`⟨·, ·⟩` is the covariant `(0, r + s)` inner product `tensorInnerPointwise_0s` of the metric-lowered
tensors.

This is the per-direction telescoping the frame-summed engine sums over the frame: the bracket-direction
first slot `⟨∇_V W', Z⟩` (with `V := [B_i, W]` and `W'` a once-derived tensor, the shape of the two
`tensor3rdCurvBracket` summands) is exhibited as the negative of the remaining two terms, a total
covariant divergence whose integral over the closed manifold vanishes. It is
`integral_tensorInner_covDeriv_combined_eq_zero` (`TensorConnLapLoweredIBP`) read in bracket-channel
language. -/
theorem loweredCovDeriv_bracketChannel_combined_isDivergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
          + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
          + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
            * divergence_g (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g r s
    W'.toSection Z.toSection V

/-- **The per-direction bracket-channel covariant Leibniz integrand IS a pointwise metric divergence.**
For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, smooth `(r, s)`-tensor sections `W'`,
`Z`, and a smooth tangent vector field `V`, the metric-lowered covariant Leibniz integrand
```
⟨∇_V W', Z⟩₀ + ⟨W', ∇_V Z⟩₀ + ⟨W', Z⟩ · divᵍ V
```
equals, **pointwise** (not merely under the integral), the metric divergence of the explicit smooth
`∇S`-order tangent field `⟨W', Z⟩ · V`:
```
divᵍ ( (tensorInnerScalar g r s W' Z) · V )  =  ⟨∇_V W', Z⟩₀ + ⟨W', ∇_V Z⟩₀ + ⟨W', Z⟩ · divᵍ V.
```
Here `∇_V` is the metric-lowered directional covariant derivative `loweredCovDerivAlongVF`, `⟨·, ·⟩₀`
is the covariant `(0, r + s)` inner product `tensorInnerPointwise_0s` of the metric-lowered tensors
(through `liftedTensorSection`), and `⟨W', Z⟩` is `tensorInnerScalar`. The current is the global
`smoothSmul (⟨W', Z⟩) V`, smooth by `tensorInnerScalar_contMDiff`.

This is the **pointwise** divergence form of each per-direction term, the genuine building block of the
moving-frame remainder divergence datum: the divergence-Leibniz rule `divergence_g_smoothSmul`
(`divᵍ(φ V) = φ · divᵍ V + V φ`) at `φ := ⟨W', Z⟩` evaluates `V φ` through the covariant inner-product
Leibniz rule `tangentSectionAction_tensorInnerScalar` (`V⟨W', Z⟩ = ⟨∇_V W', Z⟩₀ + ⟨W', ∇_V Z⟩₀`),
re-reading the lowered derivatives `loweredCovDerivAt` as `loweredCovDerivAlongVF` along `V`. Summed over
a frame it gives `integral_frameSummed_bracketCovDeriv_combined_eq_zero`, but here the identity is
pointwise, so the per-direction term is literally a divergence with a named explicit current. -/
theorem loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W' Z : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g
        (smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection)
          V) x =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s W'.toSection V x))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
        + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g r s W'.toSection x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection V x))
        + tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection x
          * divergence_g (I := I) g V x := by
  rw [divergence_g_smoothSmul (I := I) (M := M) g
    (tensorInnerScalar (I := I) (M := M) g r s W'.toSection Z.toSection)
    (tensorInnerScalar_contMDiff (I := I) (M := M) g r s W'.toSection Z.toSection) V x]
  rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g r s
    W'.toSection Z.toSection V x]
  rw [loweredCovDerivAlongVF_apply, loweredCovDerivAlongVF_apply]
  ring

/-- **The metric divergence is additive over a finite sum of smooth tangent fields.** For a closed
smooth Riemannian manifold `(M, g)`, a finite index family `ι`, and smooth tangent vector fields
`V i : Cₛ^∞⟮I; E, TangentSpace I⟯`, the divergence of the finite sum equals the sum of the divergences:
```
divᵍ (∑ i, V i) x = ∑ i, divᵍ (V i) x.
```
A `Finset.induction` over the two-field rule `divergence_g_add` and the zero rule `divergence_g_zero`,
using the pointwise additivity `ContMDiffSection.finset_sum_apply` of the section sum. This is the engine
that turns a per-direction current sum into a single explicit global divergence current. -/
theorem divergence_g_finset_sum
    (g : SmoothRiemannianMetric I M) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g (∑ i, V i) x = ∑ i, divergence_g (I := I) g (V i) x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact divergence_g_zero (I := I) (M := M) g x
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [divergence_g_add (I := I) (M := M) g (V a) (∑ i ∈ t, V i) x]
    rw [ih]

/-- **The frame-summed bracket-channel covariant Leibniz integrand is the metric divergence of an
explicit global current (the pointwise frame-summed divergence form).** For a closed smooth Riemannian
manifold `(M, g)`, ranks `(r, s)`, a finite index family `ι`, smooth tangent direction fields `V i`, and
smooth `(r, s)`-tensor sections `W i`, `Z`, the frame-summed metric-lowered covariant Leibniz integrand
```
∑ᵢ ( ⟨∇_{V i}(W i), Z⟩₀ + ⟨W i, ∇_{V i} Z⟩₀ + ⟨W i, Z⟩ · divᵍ (V i) )
```
equals, **pointwise**, the metric divergence of the explicit global tangent field
```
X := ∑ᵢ (tensorInnerScalar g r s (W i) Z) · (V i),
```
the finite sum of the per-direction `smoothSmul` currents:
```
divᵍ X (x) = ∑ᵢ ( ⟨∇_{V i}(W i), Z⟩₀(x) + ⟨W i, ∇_{V i} Z⟩₀(x) + ⟨W i, Z⟩(x) · divᵍ (V i)(x) ).
```
This is the pointwise (not merely integrated) global divergence form of the frame-summed
bracket-channel integrand: the divergence is pushed through the finite sum by `divergence_g_finset_sum`
and each per-direction summand is resolved by the pointwise per-direction divergence
`loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul`. The integral of this current vanishes
over the closed manifold (`integral_frameSummed_bracketCovDeriv_combined_eq_zero`), but here the identity
is the strictly stronger pointwise statement with a named explicit current `X`. -/
theorem frameSummed_bracketCovDeriv_combined_eq_divergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) (x : M) :
    divergence_g (I := I) g
        (∑ i, smoothSmul (I := I)
          (tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (tensorInnerScalar_contMDiff (I := I) (M := M) g r s (W i).toSection Z.toSection)
          (V i)) x =
      ∑ i, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x) := by
  classical
  rw [divergence_g_finset_sum (I := I) (M := M) g _ x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact loweredCovDeriv_bracketChannel_combined_eq_divergence_smoothSmul
    (I := I) (M := M) g r s (W i) Z (V i) x

/-- **The frame-summed bracket-channel covariant Leibniz integral vanishes (the engine consumption
bridge).** For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, a finite index family `ι`,
smooth tangent direction fields `V i`, and smooth `(r, s)`-tensor sections `W i`, `Z`, the frame-summed
metric-lowered covariant Leibniz integral vanishes:
```
∑ᵢ ∫_M ( ⟨∇_{V i}(W i), Z⟩ + ⟨W i, ∇_{V i} Z⟩ + ⟨W i, Z⟩ · divᵍ (V i) ) dvolᵍ = 0.
```

This is the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero` read for the bracket channel: when the direction fields
`V i` are the frame brackets `[B_i, W]` (the `lieBracketSection`/`smoothExtensionTangentSection` direction
families this file supplies) and the once-derived sections `W i` and `Z := ∇S` are the
`tensor3rdCurvBracket` data, the first slot `∑ᵢ ⟨∇_{V i}(W i), Z⟩` is the frame-bracket directional
pairing, and the identity exhibits it as a total covariant divergence `−∑ᵢ (⟨W i, ∇_{V i} Z⟩ +
⟨W i, Z⟩ · divᵍ (V i))` whose integral over the closed manifold vanishes. It is the divergence-vanishing
half consumed by the moving-frame bracket-channel carrier identity
`movingFrameBracketRemainder_integral_eq_genuineDiffCurv_ricTrace`
(`MovingFrameDiffCurvTraceSection`); the genuine `(∇R) S` and Ricci identification of the surviving
carrier is supplied separately (the second-Bianchi / frame-Ricci folding above the divergence engine). -/
theorem integral_frameSummed_bracketCovDeriv_combined_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {ι : Type*} [Fintype ι]
    (V : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (W : ι → SmoothCcTensor g r s) (Z : SmoothCcTensor g r s) :
    ∑ i, ∫ x, (tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s (W i).toSection (V i) x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s Z.toSection x))
            + tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g r s (W i).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g r s Z.toSection (V i) x))
            + tensorInnerScalar (I := I) (M := M) g r s (W i).toSection Z.toSection x
              * divergence_g (I := I) g (V i) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g r s V W Z

end Connection
end Integral
end DifferentialGeometry

end
