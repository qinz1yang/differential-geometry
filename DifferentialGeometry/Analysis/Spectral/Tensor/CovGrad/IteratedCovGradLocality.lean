import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSCovariantDerivativeCongrLocally
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs

/-! # Locality of the iterated section-level covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
section-level covariant gradient `covGrad g r s` is a genuinely *local* operator: its pointwise value
at a point `x` depends only on the germ of the section near `x`.  Concretely (`covGrad_toSection_apply`)
`covGrad g r s w` evaluates at `x` to `covGradBundleEquiv r s x` applied to the bundled `(r, s)`-tensor
covariant derivative `tensorRSCovariantDerivative I M r s (LeviCivita g)` of the raw fibre section
`fun y => w.toSection y` at `x`; the latter is local by
`tensorRSCovariantDerivative_congr_of_eventuallyEq`, and `covGradBundleEquiv r s x` is a fibrewise
linear equivalence.

The fibre sections are *dependent* maps `(y : M) → TensorRSSpace r s I y`, so the agreement of two
sections on a neighbourhood of `x` is stated as the eventual fibrewise equality
`∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y` (each `G₁.toSection y = G₂.toSection y` is a well-typed
equality in the fibre `TensorRSSpace r s I y`) rather than as a `Filter.EventuallyEq` of non-dependent
maps.  This file records that locality in the four forms the higher-order covariant-jet estimates need.

## Main results

* `covGrad_toSection_apply_congr_of_eventuallyEq` — single-step: two sections agreeing on a
  neighbourhood of `x` have the same covariant-gradient fibre value at `x`.
* `covGrad_toSection_eventuallyEq_of_eventuallyEq` — the neighbourhood persists: agreement near `x`
  propagates to agreement of the covariant gradients near `x` (the form needed to iterate).
* `iteratedCovGrad_toSection_apply_congr_of_eventuallyEq` — iterated: agreement near `x` gives equal
  `∇^k` fibre values at `x` for every gradient order `k` (induction on `k` through the previous item).
* `riemannianFiberNormSq_iteratedCovGrad_toSection_congr_of_eventuallyEq` — the Riemannian fibre
  norm-squared corollary: equal `∇^k` fibre values give equal `riemannianFiberNormSq`.

These are exactly the transfer lemmas a consumer holding "the moving section agrees with a
frozen-frame section on a neighbourhood of `x₀`" uses to carry `∇^k`-bounds at `x₀` from the
frozen object to the moving one. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Locality of the section-level covariant gradient at a point.** If two smooth compactly-supported
`(r, s)`-tensor sections `G₁`, `G₂` agree fibrewise on a neighbourhood of `x`
(`∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y`), then their covariant gradients have the same fibre
value at `x`.

By `covGrad_toSection_apply` the fibre value at `x` is `covGradBundleEquiv r s x` of the bundled
`(r, s)`-tensor covariant derivative of the raw section `fun y => Gᵢ.toSection y` at `x`; the latter is
equal for the two sections by `tensorRSCovariantDerivative_congr_of_eventuallyEq` (the covariant
derivative is local), so the fibre values agree. -/
theorem covGrad_toSection_apply_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    (covGrad (I := I) (M := M) g r s G₁).toSection x =
      (covGrad (I := I) (M := M) g r s G₂).toSection x := by
  rw [covGrad_toSection_apply, covGrad_toSection_apply]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) r s x) ?_
  exact tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s
    (σ := fun y : M => G₁.toSection y) (σ' := fun y : M => G₂.toSection y) (x := x)
    hagree
    (G₁.toSection.contMDiff.mdifferentiableAt (by simp))
    (G₂.toSection.contMDiff.mdifferentiableAt (by simp))

/-- **The covariant-gradient locality persists on a neighbourhood.** If two smooth compactly-supported
`(r, s)`-tensor sections agree fibrewise on a neighbourhood of `x`, then their covariant gradients also
agree fibrewise on a neighbourhood of `x`.

The agreement is eventual in `𝓝 x`, hence eventual at each nearby point
(`Filter.Eventually.eventually_nhds`); at every such point the previous pointwise locality
`covGrad_toSection_apply_congr_of_eventuallyEq` gives equality of the two covariant-gradient fibre
values.  This is the form needed to iterate the locality through `∇^k`. -/
theorem covGrad_toSection_eventuallyEq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    ∀ᶠ y in 𝓝 x,
      (covGrad (I := I) (M := M) g r s G₁).toSection y =
        (covGrad (I := I) (M := M) g r s G₂).toSection y := by
  filter_upwards [hagree.eventually_nhds] with y hy
  exact covGrad_toSection_apply_congr_of_eventuallyEq (I := I) g r s
    (G₁ := G₁) (G₂ := G₂) (x := y) hy

/-- **Locality of the iterated section-level covariant gradient at a point.** If two smooth
compactly-supported `(r, s)`-tensor sections agree fibrewise on a neighbourhood of `x`, then for every
gradient order `k` their `k`-fold iterated covariant gradients `∇^k` have the same fibre value at `x`.

Proven by establishing the stronger *neighbourhood* agreement of `∇^k` for every `k`, by induction on
`k`.  The base case `k = 0` is `iteratedCovGrad_zero` (the gradient is the section itself, so the
agreement is `hagree`).  The successor step rewrites `∇^{k+1}` as `covGrad` of `∇^k`
(`iteratedCovGrad_succ`) and upgrades the order-`k` neighbourhood agreement through
`covGrad_toSection_eventuallyEq_of_eventuallyEq`.  Reading the order-`k` neighbourhood agreement at the
point `x` itself (`Filter.Eventually.self_of_nhds`) gives the pointwise conclusion. -/
theorem iteratedCovGrad_toSection_apply_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y) :
    ∀ k : ℕ,
      (iteratedCovGrad g r s k G₁).toSection x =
        (iteratedCovGrad g r s k G₂).toSection x := by
  have hev : ∀ k : ℕ,
      ∀ᶠ y in 𝓝 x,
        (iteratedCovGrad g r s k G₁).toSection y =
          (iteratedCovGrad g r s k G₂).toSection y := by
    intro k
    induction k with
    | zero => simpa only [iteratedCovGrad_zero] using hagree
    | succ k ih =>
        simp only [iteratedCovGrad_succ]
        exact covGrad_toSection_eventuallyEq_of_eventuallyEq (I := I) g r (s + k)
          (G₁ := iteratedCovGrad g r s k G₁)
          (G₂ := iteratedCovGrad g r s k G₂) ih
  intro k
  exact (hev k).self_of_nhds

/-- **Riemannian fibre-norm-squared transfer for the iterated covariant gradient.** If two smooth
compactly-supported `(r, s)`-tensor sections agree fibrewise on a neighbourhood of `x`, then for every
gradient order `k` the Riemannian fibre norm-squared of `∇^k` at `x` agrees.  This is `congrArg` of
`riemannianFiberNormSq g r (s + k) x` applied to the pointwise iterated locality
`iteratedCovGrad_toSection_apply_congr_of_eventuallyEq`. -/
theorem riemannianFiberNormSq_iteratedCovGrad_toSection_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {G₁ G₂ : SmoothCcTensor g r s} {x : M}
    (hagree : ∀ᶠ y in 𝓝 x, G₁.toSection y = G₂.toSection y)
    (k : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + k) x
        ((iteratedCovGrad g r s k G₁).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + k) x
        ((iteratedCovGrad g r s k G₂).toSection x) :=
  congrArg (riemannianFiberNormSq (I := I) (M := M) g r (s + k) x)
    (iteratedCovGrad_toSection_apply_congr_of_eventuallyEq (I := I) g r s hagree k)

end RicciFlow
end PDE
end DifferentialGeometry

end
