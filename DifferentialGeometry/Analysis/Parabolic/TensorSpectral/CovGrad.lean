import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovariantLeibniz
import DifferentialGeometry.Tensor.RSTensor.GradientBundleEquiv

/-!
# The section-level covariant gradient of a smooth compactly-supported tensor section

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file assembles the *section-level covariant gradient*: an operator
sending a smooth compactly-supported `(r, s)`-tensor section to its covariant
gradient, packaged as a smooth compactly-supported `(r, s + 1)`-tensor section.

The covariant derivative of an `(r, s)`-tensor section adds one covariant
(tangent-input) slot, so the covariant gradient is naturally an `(r, s + 1)`-tensor.
Concretely the pointwise directional covariant derivative `tensorCovDerivAt` is a
continuous linear map from a tangent vector to an `(r, s)`-tensor, i.e. an element
of the covariant-gradient bundle fibre

`TangentSpace I x →L[ℝ] TensorRSSpace r s I x`,

and the just-constructed smooth bundle equivalence `covGradBundleSmoothEquiv`
identifies that bundle with the `(r, s + 1)`-tensor bundle. Composing the two
yields the section-level operator.

## Main constructions

* `covGrad g r s w` — the section-level covariant gradient: the covariant gradient
  of a smooth compactly-supported `(r, s)`-tensor section `w`, as a smooth
  compactly-supported `(r, s + 1)`-tensor section.

## Main results

* `covGrad_add`, `covGrad_smul` — `ℝ`-linearity of `covGrad` in the section.
* `covGrad_toSection_apply` — the pointwise-evaluation formula: at a point `x`,
  the underlying section value of `covGrad g r s w` is the image, under the
  fibrewise gradient-bundle equivalence `covGradBundleEquiv r s x`, of the
  pointwise directional covariant derivative `tensorCovDerivAt g r s w x`.

## Strategy

The directional covariant derivative `tensorCovDerivAt g r s w x v` is by
definition the bundled `(r, s)`-tensor covariant derivative
`tensorRSCovariantDerivative` applied to `w.toSection`, evaluated bilinearly at
`x` and `v`. As a function of the base point, the continuous-linear-map–valued
section `x ↦ tensorRSCovariantDerivative … x` is a smooth section of the
covariant-gradient bundle `Hom(TM, T^{(r,s)})`: this is the `contMDiff` field of
the `ContMDiffCovariantDerivative` instance carried by the bundled covariant
derivative, applied to the smooth section `w.toSection`.

Post-composing this smooth gradient-bundle section, fibrewise, with the smooth
vector-bundle equivalence `covGradBundleSmoothEquiv` lands in the
`(r, s + 1)`-tensor bundle; smoothness of the resulting section follows because the
total-space map of `covGradBundleSmoothEquiv` is `C^∞`. Compact support is
inherited: the directional covariant derivative vanishes off `tsupport w.toFun`
(by `tensorCovDerivAt_eq_zero_off_tsupport`), and the bundle equivalence sends the
zero fibre to the zero fibre. Linearity is the linearity of `tensorCovDerivAt` in
the section together with linearity of the fibrewise bundle equivalence.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The covariant-gradient-bundle-valued section of a smooth compactly-supported
`(r, s)`-tensor section `w`: the continuous-linear-map–valued function sending a
base point `x` to the directional covariant derivative `v ↦ tensorCovDerivAt …`.

Its value at `x` is the continuous linear map
`tensorRSCovariantDerivative I M r s (LeviCivita g) w.toSection x`. -/
private noncomputable def covGradGradSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => w.toSection y) x

/-- The covariant-gradient-bundle-valued section, evaluated bilinearly at a base
point `x` and a model-fibre direction `v`, equals the directional covariant
derivative `tensorCovDerivAt g r s w x v`. -/
private lemma covGradGradSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) (v : E) :
    covGradGradSection (I := I) (M := M) g r s w x v =
      tensorCovDerivAt (I := I) (M := M) g r s w x v := rfl

/-- The covariant-gradient-bundle-valued section is a `C^∞` section of the
covariant-gradient bundle `Hom(TM, T^{(r,s)})`.

This is the `contMDiff` field of the `ContMDiffCovariantDerivative` instance
carried by the bundled `(r, s)`-tensor covariant derivative
`tensorRSCovariantDerivative I M r s (LeviCivita g)`, applied to the smooth
section `w.toSection`. -/
private lemma covGradGradSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) with hcovLC
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => w.toSection y) x⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => w.toSection y)
      (w.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

/-- The covariant-gradient-bundle-valued section of `w`, transported fibrewise
through `covGradBundleSmoothEquiv` into the `(r, s + 1)`-tensor bundle, packaged as
a smooth section of the `(r, s + 1)`-tensor bundle.

The underlying map sends `x` to `covGradBundleEquiv r s x (covGradGradSection …)`.
In total-space form it is the composite of the smooth gradient-bundle section
`covGradGradSection` with the `C^∞` total-space map of the smooth vector-bundle
equivalence `covGradBundleSmoothEquiv`, which acts fibrewise by `covGradBundleEquiv`;
hence it is `C^∞`. -/
private noncomputable def covGradSmoothSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :=
  letI : NormedAddCommGroup (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (s + 1)
  letI : NormedSpace ℝ (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedSpace r (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) I :=
    tensorRSBundle_smooth ∞ r (s + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ∘
          (fun x : M =>
            (⟨x, covGradGradSection (I := I) (M := M) g r s w x⟩ :
              TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
                fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph.contMDiff.comp
      (covGradGradSection_contMDiff (I := I) (M := M) g r s w)
  have hsmooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        (fun x : M =>
          (⟨x, covGradBundleEquiv (I := I) (M := M) r s x
              (covGradGradSection (I := I) (M := M) g r s w x)⟩ :
            TotalSpace (TensorRSModel r (s + 1) ℝ E)
              fun y : M => TensorRSSpace r (s + 1) I y)) := by
    refine hcomp.congr ?_
    intro x
    rw [Function.comp_apply,
      covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x)]
  (ContMDiffSection.mk
      (fun x : M => covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x))
      hsmooth :
    Cₛ^∞⟮I; TensorRSModel r (s + 1) ℝ E,
      (fun x : M => TensorRSSpace r (s + 1) I x)⟯)

/-- The section value of `covGradSmoothSection g r s w` at a point `x` is the
`(r, s + 1)`-tensor `covGradBundleEquiv r s x (covGradGradSection g r s w x)`. -/
private lemma covGradSmoothSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    covGradSmoothSection (I := I) (M := M) g r s w x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (covGradGradSection (I := I) (M := M) g r s w x) := rfl

/-- The underlying model-valued map of `covGradSmoothSection g r s w` vanishes at
every point outside `tsupport w.toFun`.

The directional covariant derivative `tensorCovDerivAt g r s w x` is the zero
continuous linear map there (by `tensorCovDerivAt_eq_zero_off_tsupport`); the
fibrewise bundle equivalence `covGradBundleEquiv r s x` is linear, so it sends the
zero gradient-bundle fibre to the zero `(r, s + 1)`-tensor fibre. -/
private lemma covGradSmoothSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport w.toFun) :
    TensorRSSpace.toModel
      (covGradSmoothSection (I := I) (M := M) g r s w x) = 0 := by
  have hgrad_zero : covGradGradSection (I := I) (M := M) g r s w x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.zero_apply, covGradGradSection_apply]
    exact tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s w hx v
  rw [covGradSmoothSection_apply, hgrad_zero, map_zero, TensorRSSpace.toModel_zero]

/-- The underlying model-valued map of `covGradSmoothSection g r s w` has compact
support: it vanishes outside `tsupport w.toFun`, which is compact. -/
private lemma covGradSmoothSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covGradSmoothSection (I := I) (M := M) g r s w x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covGradSmoothSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s w hxnot)

/-- **The section-level covariant gradient.** The covariant gradient of a smooth
compactly-supported `(r, s)`-tensor section `w`, as a smooth compactly-supported
`(r, s + 1)`-tensor section.

Pointwise, its underlying section value at a base point `x` is the image, under
the fibrewise covariant-gradient bundle equivalence `covGradBundleEquiv r s x`, of
the directional covariant derivative `tensorCovDerivAt g r s w x` — the
continuous-linear-map–valued covariant derivative of `w` at `x`. The extra
covariant slot is the slot carrying the tangent-vector input. -/
noncomputable def covGrad (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r (s + 1) :=
  fun w =>
    { toSection := covGradSmoothSection (I := I) (M := M) g r s w
      hasCompactSupport :=
        covGradSmoothSection_hasCompactSupport (I := I) (M := M) g r s w }

/-- The underlying smooth section of `covGrad g r s w` is
`covGradSmoothSection g r s w`. -/
lemma covGrad_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) :
    (covGrad (I := I) (M := M) g r s w).toSection =
      covGradSmoothSection (I := I) (M := M) g r s w := rfl

/-- **Pointwise-evaluation formula for the section-level covariant gradient.**

At a base point `x`, the underlying section value of `covGrad g r s w` is the
image, under the fibrewise covariant-gradient bundle equivalence
`covGradBundleEquiv r s x`, of the continuous-linear-map–valued directional
covariant derivative `v ↦ tensorCovDerivAt g r s w x v` of `w` at `x` — which is
the bundled `(r, s)`-tensor covariant derivative `tensorRSCovariantDerivative`
applied to `w.toSection`. -/
theorem covGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g r s w).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => w.toSection y) x) := by
  rw [covGrad_toSection, covGradSmoothSection_apply]
  rfl

/-- **Pointwise-evaluation formula, expanded on a tensor and a tuple.**

The underlying section value of `covGrad g r s w` at `x` is an `(r, s + 1)`-tensor,
i.e. a continuous linear map `Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x`.
Evaluated at a `(0, r)`-tensor `D` and a `Fin (s + 1)`-tuple of tangent vectors
`v`, it reads off the tangent direction `v 0` from the leftmost covariant slot:
the result is the directional covariant derivative `tensorCovDerivAt g r s w x`,
taken in the direction `v 0`, applied to `D` and the remaining `Fin s`-tuple
`Matrix.vecTail v`. -/
theorem covGrad_toSection_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) (x : M)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s w).toSection x) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s w x (v 0)) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply]
  exact covGradBundleEquiv_apply_eval (I := I) (M := M) r s x
    (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun y : M => w.toSection y) x) D v

/-- The covariant-gradient-bundle-valued section is additive in the section: this
is the additivity of the directional covariant derivative. -/
private lemma covGradGradSection_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x =
      covGradGradSection (I := I) (M := M) g r s w₁ x +
        covGradGradSection (I := I) (M := M) g r s w₂ x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.add_apply, covGradGradSection_apply,
    covGradGradSection_apply, covGradGradSection_apply]
  exact tensorCovDerivAt_add (I := I) (M := M) g r s w₁ w₂ x v

/-- The covariant-gradient-bundle-valued section is `ℝ`-homogeneous in the
section: this is the homogeneity of the directional covariant derivative. -/
private lemma covGradGradSection_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) (x : M) :
    covGradGradSection (I := I) (M := M) g r s (c • w) x =
      c • covGradGradSection (I := I) (M := M) g r s w x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.smul_apply, covGradGradSection_apply,
    covGradGradSection_apply]
  exact tensorCovDerivAt_smul (I := I) (M := M) g r s c w x v

/-- The section-level covariant gradient is additive in the section. -/
theorem covGrad_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (w₁ + w₂) =
      covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((covGrad (I := I) (M := M) g r s w₁ +
        covGrad (I := I) (M := M) g r s w₂).toSection x) =
      (covGrad (I := I) (M := M) g r s w₁).toSection x +
        (covGrad (I := I) (M := M) g r s w₂).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (w₁ + w₂).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (w₁ + w₂) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₁.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₁ x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w₂.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w₂ x from rfl,
    covGradGradSection_add (I := I) (M := M) g r s w₁ w₂ x, map_add]

/-- The section-level covariant gradient is `ℝ`-homogeneous in the section. -/
theorem covGrad_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (c • w) =
      c • covGrad (I := I) (M := M) g r s w := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • covGrad (I := I) (M := M) g r s w).toSection x) =
      c • (covGrad (I := I) (M := M) g r s w).toSection x from rfl]
  rw [covGrad_toSection_apply, covGrad_toSection_apply]
  rw [show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => (c • w).toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s (c • w) x from rfl,
    show (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => w.toSection y) x) =
      covGradGradSection (I := I) (M := M) g r s w x from rfl,
    covGradGradSection_smul (I := I) (M := M) g r s c w x, map_smul]

/-- The section-level covariant gradient sends the zero section to the zero
section. -/
@[simp] theorem covGrad_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    covGrad (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := covGrad_smul (I := I) (M := M) g r s (0 : ℝ) 0
  rwa [zero_smul, zero_smul] at h

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
