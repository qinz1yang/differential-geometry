import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert

/-!
# The pointwise covariant Leibniz rule for a smooth-scalar-weighted tensor section

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file records the pointwise covariant Leibniz rule for the
directional covariant derivative of a *smooth-scalar-weighted* `(r, s)`-tensor
section, together with the resulting Leibniz identity for the pointwise
covariant-derivative inner product `tensorCovDerivPointwiseInner`.

The scaling is by a smooth real-valued function `ζ : C^∞⟮I, M; ℝ⟯` on `M`.
Multiplying a smooth compactly-supported `(r, s)`-tensor section `w` by `ζ`
produces another smooth compactly-supported tensor section `scalarSmul g r s ζ w`
(its support sits inside `tsupport w.toFun`, hence is still compact).

## Main constructions

* `scalarSmul g r s ζ w` — the smooth compactly-supported tensor section
  `ζ • w`, the smooth scalar `ζ` times the section `w`.
* `tensorCovDerivCrossLeft g r s ζ w S x` — the explicit cross term
  `⟨∇w, dζ ⊗ S⟩` of the Leibniz identity below, an inverse-Gram-weighted double
  sum of `∂ₖζ` times the `(r, s)`-tensor pointwise inner product.
* `tensorCovDerivCrossRight g r s ζ w S x` — the explicit cross term
  `⟨dζ ⊗ w, ∇S⟩` of the Leibniz identity below.

## Main results

* `tensorCovDerivAt_scalarSmul` — the pointwise covariant Leibniz rule:
  the directional covariant derivative of `ζ • w` at `x` along `v` is
  `ζ x • tensorCovDerivAt … w x v + (extDerivFun ζ x v) • w.toSection x`.
  This is the genuine non-constant analogue of `tensorCovDerivAt_smul`: the
  derivative-of-`ζ` term `extDerivFun ζ x` is retained.
* `tensorCovDerivPointwiseInner_scalarSmul_left` — the Leibniz identity for the
  pointwise covariant-derivative inner product: the inverse-Gram-weighted
  expression `tensorCovDerivPointwiseInner g r s (ζ • w) S` decomposes as
  `tensorCovDerivPointwiseInner g r s w (ζ • S)
     − ⟨∇w, dζ ⊗ S⟩ + ⟨dζ ⊗ w, ∇S⟩`
  with the two cross terms given the explicit concrete form above.

## Strategy

`tensorCovDerivAt g r s S x v` is the bundled `(r, s)`-tensor covariant
derivative `tensorRSCovariantDerivative` applied to `S.toSection`; that bundled
object satisfies `IsCovariantDerivativeOn … Set.univ`, so its `leibniz` field
applies verbatim once `ζ` and `w.toSection` are seen as manifold-differentiable.
This yields `tensorCovDerivAt_scalarSmul` directly. Headline 2 then substitutes
`tensorCovDerivAt_scalarSmul` into each summand of `tensorCovDerivPointwiseInner`
and expands the bilinear pointwise inner product `tensorInnerPointwise`; the two
remaining summands are precisely the explicit cross terms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

/-- The smooth real-valued function `ζ` times a smooth compactly-supported
`(r, s)`-tensor section `w`, packaged as a smooth compactly-supported tensor
section. The underlying section is the pointwise scalar product
`fun x => ζ x • w.toSection x`. -/
noncomputable def scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => (ζ : M → ℝ) x • w.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section ζ.contMDiff w.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport w.toFun ?_
    rw [Function.mem_support]
    intro hw_zero
    apply hx
    change TensorRSSpace.toModel ((ζ : M → ℝ) x • w.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (w.toSection x) = w.toFun x from rfl, hw_zero,
      smul_zero]

/-- The underlying section of `scalarSmul g r s ζ w` is the pointwise scalar
product of `ζ` and the underlying section of `w`. -/
@[simp] lemma scalarSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toSection x =
      (ζ : M → ℝ) x • w.toSection x := rfl

/-- The underlying map of `scalarSmul g r s ζ w` is the pointwise scalar product
of `ζ` and the underlying map of `w`. -/
@[simp] lemma scalarSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toFun x =
      (ζ : M → ℝ) x • w.toFun x := by
  rw [SmoothCcTensor.toFun_apply, scalarSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

/-- **The pointwise covariant Leibniz rule.** For a smooth real-valued function
`ζ` and a smooth compactly-supported `(r, s)`-tensor section `w`, the directional
covariant derivative of the smooth-scalar-weighted section `ζ • w` at a point
`x` along a model-fibre direction `v` is

  `ζ x • tensorCovDerivAt g r s w x v + (extDerivFun ζ x v) • w.toSection x`.

This is the genuine non-constant analogue of `tensorCovDerivAt_smul`: the
constant-scalar special case discards the term `extDerivFun ζ x`; here it is the
exterior derivative of `ζ` and is retained. -/
theorem tensorCovDerivAt_scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) x v =
      (ζ : M → ℝ) x • tensorCovDerivAt (I := I) (M := M) g r s w x v +
        (extDerivFun (I := I) (ζ : M → ℝ) x v) • w.toSection x := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ w).toSection y) =
      (fun y : M => (ζ : M → ℝ) y) • (fun y : M => w.toSection y) := by
    funext y
    rw [scalarSmul_toSection_apply]
    rfl
  rw [hpt]
  have hζ_mdiff : MDiffAt (fun y : M => (ζ : M → ℝ) y) x :=
    (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
  have hw_mdiff :=
    (w.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => w.toSection y)
      (g := fun y : M => (ζ : M → ℝ) y)
      (hσ := hw_mdiff)
      (hg := hζ_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun y : M => (ζ : M → ℝ) y) • fun y : M => w.toSection y) x v = _
  rw [hcov_leibniz]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]

/-- The explicit cross term `⟨∇w, dζ ⊗ S⟩` of the Leibniz identity for the
pointwise covariant-derivative inner product. The `dζ ⊗ S` factor contributes,
in the gradient direction `j`, only the scalar `extDerivFun ζ x (chartModelBasis E j)`;
the remaining factor is the `(r, s)`-tensor pointwise inner product of the
genuine covariant gradient `tensorCovDerivAt … w` against the section value
`S.toSection x`. The inverse Gram matrix `(gramMatrixAt g x)⁻¹` couples the two
gradient slots exactly as in `tensorCovDerivPointwiseInner`. -/
noncomputable def tensorCovDerivCrossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) i)))
          (S.toFun x))

/-- The explicit cross term `⟨dζ ⊗ w, ∇S⟩` of the Leibniz identity for the
pointwise covariant-derivative inner product. The `dζ ⊗ w` factor contributes,
in the gradient direction `i`, only the scalar `extDerivFun ζ x (chartModelBasis E i)`;
the remaining factor is the `(r, s)`-tensor pointwise inner product of the
section value `w.toSection x` against the genuine covariant gradient
`tensorCovDerivAt … S`. The inverse Gram matrix `(gramMatrixAt g x)⁻¹` couples
the two gradient slots exactly as in `tensorCovDerivPointwiseInner`. -/
noncomputable def tensorCovDerivCrossRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (w.toFun x)
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j))))

/-- Unfolding lemma for `tensorCovDerivCrossLeft`. -/
lemma tensorCovDerivCrossLeft_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (S.toFun x)) := rfl

/-- Unfolding lemma for `tensorCovDerivCrossRight`. -/
lemma tensorCovDerivCrossRight_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) := rfl

/-- Auxiliary expansion: the summand of `tensorCovDerivPointwiseInner` for the
smooth-scalar-weighted section `ζ • w` (first argument) splits, via the pointwise
covariant Leibniz rule and bilinearity of `tensorInnerPointwise`, into the
`ζ`-scaled genuine-gradient summand plus the `dζ`-contracted cross summand. -/
private lemma tensorCovDerivPointwiseInner_scalarSmul_left_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ w) x ((chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x
              ((chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ w x
    ((chartModelBasis E) i)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hwx : TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
  rw [hwx]
  rw [tensorInnerPointwise_add_left]
  simp only [tensorInnerPointwise_smul_left]
  ring

/-- Auxiliary expansion: the summand of `tensorCovDerivPointwiseInner` for the
smooth-scalar-weighted section `ζ • S` (second argument) splits, via the
pointwise covariant Leibniz rule and bilinearity of `tensorInnerPointwise`, into
the `ζ`-scaled genuine-gradient summand plus the `dζ`-contracted cross summand. -/
private lemma tensorCovDerivPointwiseInner_scalarSmul_right_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ S) x
                ((chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (S.toFun x)) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ S x
    ((chartModelBasis E) j)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hSx : TensorRSSpace.toModel (S.toSection x) = S.toFun x := rfl
  rw [hSx]
  rw [tensorInnerPointwise_add_right]
  simp only [tensorInnerPointwise_smul_right]
  ring

/-- A `ζ`-scaled rewriting of `tensorCovDerivPointwiseInner`: the inverse-Gram-
weighted double sum with each summand scaled by the constant `ζ x` equals the
constant `ζ x` times `tensorCovDerivPointwiseInner`. -/
private lemma smul_const_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) =
      (ζ : M → ℝ) x *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s w S x := by
  rw [tensorCovDerivPointwiseInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]

/-- **The Leibniz identity for the pointwise covariant-derivative inner
product.** For a smooth real-valued function `ζ` and smooth compactly-supported
`(r, s)`-tensor sections `w` and `S`, the inverse-Gram-weighted pointwise
covariant-derivative inner product of the smooth-scalar-weighted section
`ζ • w` against `S` decomposes as the inner product of `w` against the
smooth-scalar-weighted section `ζ • S`, corrected by the two explicit cross
terms:

  `tensorCovDerivPointwiseInner g r s (ζ • w) S x
     = tensorCovDerivPointwiseInner g r s w (ζ • S) x
       − tensorCovDerivCrossLeft g r s ζ w S x
       + tensorCovDerivCrossRight g r s ζ w S x`.

The cross term `tensorCovDerivCrossLeft` is `⟨∇w, dζ ⊗ S⟩` and
`tensorCovDerivCrossRight` is `⟨dζ ⊗ w, ∇S⟩`; both are inverse-Gram-weighted
double sums of `∂ₖζ = extDerivFun ζ x (chartModelBasis E ·)` against the
`(r, s)`-tensor pointwise inner product. Integrating over `M` against the
Riemannian volume measure splits the Dirichlet integrand
`∫ tensorCovDerivPointwiseInner g r s (ζ • w) S` into the corresponding three
integrals. -/
theorem tensorCovDerivPointwiseInner_scalarSmul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) S x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x -
        tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x +
        tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
  classical
  have hLHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ w) S x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((chartModelBasis E) j))))) +
          tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossRight_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_left_summand
      (I := I) (M := M) g r s ζ w S x i j
  have hRHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((chartModelBasis E) j))))) +
          tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_right_summand
      (I := I) (M := M) g r s ζ w S x i j
  rw [hLHS, hRHS]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
