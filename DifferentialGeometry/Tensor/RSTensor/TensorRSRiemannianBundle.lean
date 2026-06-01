import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannianBundle
import DifferentialGeometry.Tensor.RSTensor.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Model-fibre inner-product CLM for the `(r, s)`-tensor bundle

Given a smooth Riemannian metric `g` on a manifold `M` (encoded as a
`SmoothRiemannianMetric I M`, i.e., a
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`), this file
exposes the mixed `(r, s)` pointwise inner product
`tensorInnerPointwise g r s b` as a continuous bilinear pairing
`innerModelCLMRS g r s b` on the model fibre `TensorRSModel r s ℝ E`.

The mixed `(r, s)` pointwise inner product is defined in
`Integral/L2/PointwiseInner/Defs.lean` by lowering the `r` upper indices
via `lowerAllUpperIndices` and reducing to the covariant `(0, r + s)`
inner product `tensorInnerPointwise_0s` at arity `r + s`. The algebraic
properties (bilinearity, symmetry, non-negativity, positive
definiteness) are established in `Integral/L2/PointwiseInner/Algebra.lean`.

The construction here packages the inner product as a continuous bilinear
`→L[ℝ] · →L[ℝ] ·` pairing, the natural object for further use in
Mathlib's `Bundle.RiemannianMetric` and `IsContinuousRiemannianBundle`
machinery. Lifting this pairing through the bundle/norm topology diamond
to obtain a bundle-fibre pairing on `TensorRSSpace r s I b` (and ultimately
a `Bundle.RiemannianMetric` structure) requires diamond-handling along the
same lines as `TangentRiemannian.lean`; the model-fibre data delivered
here is the canonical algebraic input to that further construction.

We also prove von-Neumann boundedness of the diagonal-inner-product unit
ball on the model fibre, reducing to the abstract positive-definite
bilinear-form lemma `posDef_bilin_unit_ball_isBounded` already established
in `Tensor0SRiemannian.lean`.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannianBundle

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The mixed `(r, s)` pointwise inner product on the model fibre as a CLM

The pointwise inner product `tensorInnerPointwise g r s b` is bilinear and
the model fibre is finite-dimensional, so it is automatically a continuous
bilinear map. We package it as a `→L[ℝ] · →L[ℝ] ·` CLM. -/

/-- Underlying bilinear (`LinearMap`-valued) pairing on the model fibre. -/
private def innerModelBilinRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => tensorInnerPointwise (I := I) (M := M) g r s b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_add_right (I := I) (M := M) g r s b T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c T S)

@[simp] private lemma innerModelBilinRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelBilinRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

/-- The "outer" linear map: for each `T`, the inner-argument `S ↦ inner T S`
is linear and (since the model fibre is finite-dimensional) continuous. -/
private def innerModelLinearOuterRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] (TensorRSModel r s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilinRS (I := I) (M := M) g r s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (T₁ + T₂) S =
      tensorInnerPointwise (I := I) (M := M) g r s b T₁ S +
        tensorInnerPointwise (I := I) (M := M) g r s b T₂ S
    exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (c • T) S =
      c • tensorInnerPointwise (I := I) (M := M) g r s b T S
    rw [tensorInnerPointwise_smul_left]
    rfl

/-- The mixed `(r, s)` pointwise inner product as a continuous bilinear
pairing on the model fibre. -/
def innerModelCLMRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuterRS (I := I) (M := M) g r s b)

@[simp] lemma innerModelCLMRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

/-! ## Algebraic properties of `innerModelCLMRS` at the model-fibre level -/

/-- Symmetry of the model-fibre mixed inner product. -/
lemma innerModelCLMRS_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      innerModelCLMRS (I := I) (M := M) g r s b S T := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

/-- Positive definiteness on the diagonal: `inner b T T > 0` for `T ≠ 0`. -/
lemma innerModelCLMRS_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) (hT : T ≠ 0) :
    0 < innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b T T :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hT
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b T).mp heq.symm

/-- Non-negativity of the model-fibre mixed inner product on the diagonal. -/
lemma innerModelCLMRS_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    0 ≤ innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T

/-- Left additivity of the model-fibre mixed inner product. -/
lemma innerModelCLMRS_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (T₁ + T₂) S =
      innerModelCLMRS (I := I) (M := M) g r s b T₁ S +
        innerModelCLMRS (I := I) (M := M) g r s b T₂ S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b _ _ _

/-- Right additivity of the model-fibre mixed inner product. -/
lemma innerModelCLMRS_add_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (S₁ + S₂) =
      innerModelCLMRS (I := I) (M := M) g r s b T S₁ +
        innerModelCLMRS (I := I) (M := M) g r s b T S₂ := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_right (I := I) (M := M) g r s b _ _ _

/-- Left scalar-multiplication of the model-fibre mixed inner product. -/
lemma innerModelCLMRS_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (c • T) S =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c _ _

/-- Right scalar-multiplication of the model-fibre mixed inner product. -/
lemma innerModelCLMRS_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (c • S) =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c _ _

/-! ## Bundle-fibre `(r, s)` inner CLM via the CLE bridge

The bundle fibre `TensorRSSpace r s I b` is canonically continuously linearly equivalent
to the model fibre `TensorRSModel r s ℝ E` via `tensorRSSpace_continuousLinearEquiv`.
We package the model-fibre CLM `innerModelCLMRS` as a bundle-fibre CLM by precomposing
with this CLE on each argument. -/

/-- Shorthand for the CLE between the bundle fibre and the model fibre. -/
private def bundleCLERS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
  Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
    (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b

/-- The forward CLM of `bundleCLERS`. -/
private def bundleToModelCLMRS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E :=
  (bundleCLERS (I := I) (M := M) (E := E) r s b).toContinuousLinearMap

/-- The "pre-compose into bundle" CLM, post-composing a model-fibre CLM
`TensorRSModel r s ℝ E →L[ℝ] ℝ` with `bundleToModelCLMRS`. -/
private def precompBundleCLMRS (r s : ℕ) (b : M) :
    (TensorRSModel r s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (TensorRSSpace r s I b →L[ℝ] ℝ) :=
  ((bundleCLERS (I := I) (M := M) (E := E) r s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

@[simp] private lemma precompBundleCLMRS_apply (r s : ℕ) (b : M)
    (f : TensorRSModel r s ℝ E →L[ℝ] ℝ) (T : TensorRSSpace r s I b) :
    precompBundleCLMRS (I := I) (M := M) (E := E) r s b f T =
      f (Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
  rfl

/-- The `(r, s)` pointwise inner product packaged as a continuous bilinear
pairing on the bundle fibre `TensorRSSpace r s I b`. -/
def tensorRSRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSSpace r s I b →L[ℝ] ℝ :=
  let stepA : TensorRSModel r s ℝ E →L[ℝ] (TensorRSSpace r s I b →L[ℝ] ℝ) :=
    (precompBundleCLMRS (I := I) (M := M) (E := E) r s b).comp
      (innerModelCLMRS (I := I) (M := M) g r s b)
  stepA.comp (bundleToModelCLMRS (I := I) (M := M) (E := E) r s b)

@[simp] lemma tensorRSRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) S) := by
  rfl

/-! ## Algebraic properties of the bundle-fibre CLM -/

/-- Symmetry of the bundle-fibre `(r, s)` inner product. -/
theorem tensorRSRiemannianInnerCLM_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b S T := by
  rw [tensorRSRiemannianInnerCLM_apply, tensorRSRiemannianInnerCLM_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

/-- Positive-definiteness on the diagonal: `inner b T T > 0` for `T ≠ 0`. -/
theorem tensorRSRiemannianInnerCLM_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) (hT : T ≠ 0) :
    0 < tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T := by
  rw [tensorRSRiemannianInnerCLM_apply]
  have hTm :
      Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.TensorRSSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (0 : TensorRSSpace r s I b) = 0 :=
      Tensor0SBundle.TensorRSSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b _).mp heq.symm

/-- Left scalar-homogeneity. -/
theorem tensorRSRiemannianInnerCLM_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) c T
  change tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S = _
  rw [h]
  rfl

/-- Right scalar-homogeneity. -/
theorem tensorRSRiemannianInnerCLM_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T (c • S) =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) T) c S
  change (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T) (c • S) = _
  rw [h]
  rfl

/-! ## Diagonal continuity

We prove that `v ↦ tensorRSRiemannianInnerCLM g r s b v v` is continuous on
the bundle fibre `TensorRSSpace r s I b`. The argument transports through the
continuous CLE `bundleCLERS` to the model fibre, where the bilinear CLM
`innerModelCLMRS g r s b` has straightforward continuity. -/

/-- The model-fibre diagonal `T ↦ tensorInnerPointwise g r s b T T` is continuous
on the model fibre, viewed as a finite-dim normed space.

Proof strategy: Expand the quadratic form in a basis. Coordinates are continuous
(finite-dim linear functionals), products are continuous, finite sums of continuous
are continuous. -/
lemma innerModelRS_quadratic_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun T : TensorRSModel r s ℝ E =>
      tensorInnerPointwise (I := I) (M := M) g r s b T T) := by
  classical
  -- Use the canonical basis of the finite-dim model fibre.
  let ι := Fin (Module.finrank ℝ (TensorRSModel r s ℝ E))
  let basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E) :=
    Module.finBasis ℝ (TensorRSModel r s ℝ E)
  -- Coordinate functionals `φ_i : M →ₗ[ℝ] ℝ`, each continuous in finite-dim.
  let φ : ι → (TensorRSModel r s ℝ E →ₗ[ℝ] ℝ) := fun i => basis.coord i
  have hφ_cont : ∀ i, Continuous (φ i) := fun i =>
    LinearMap.continuous_of_finiteDimensional (φ i)
  -- Expansion: `T = ∑ φ i T • basis i`.
  have hexpand : ∀ T : TensorRSModel r s ℝ E,
      T = ∑ i : ι, (φ i T) • basis i := by
    intro T
    have := basis.linearCombination_repr T
    -- `linearCombination` over a Finsupp; convert to Finset.sum over Fintype.
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at this
    · exact this.symm
    · intros; rw [zero_smul]
  -- Bilin T T = ∑_{i,j} φ_i T * φ_j T * tensorInnerPointwise g r s b (basis i) (basis j)
  -- A general distributivity lemma: for any coefficient vector `a : ι → ℝ`, the
  -- inner product of `∑ i, a i • basis i` with itself expands to the double sum.
  have hgen_left : ∀ (a : ι → ℝ) (S : TensorRSModel r s ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b
        (∑ i : ι, a i • basis i) S =
        ∑ i : ι, (a i) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S := by
    intro a S
    let LL : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun T' => tensorInnerPointwise (I := I) (M := M) g r s b T' S
        map_add' := fun T₁ T₂ =>
          tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
        map_smul' := fun c T' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (c • T') S = c • _
          rw [tensorInnerPointwise_smul_left]
          rfl }
    have hLL_sum : LL (∑ i : ι, a i • basis i) =
        ∑ i : ι, LL (a i • basis i) :=
      map_sum LL _ _
    change LL _ = _
    rw [hLL_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LL.map_smul]
    rfl
  have hgen_right : ∀ (a : ι → ℝ) (i : ι),
      tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
        (∑ j : ι, a j • basis j) =
        ∑ j : ι, (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro a i
    let RR : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun S' => tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S'
        map_add' := fun S₁ S₂ =>
          tensorInnerPointwise_add_right (I := I) (M := M) g r s b (basis i) S₁ S₂
        map_smul' := fun c S' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (c • S') = c • _
          rw [tensorInnerPointwise_smul_right]
          rfl }
    have hRR_sum : RR (∑ j : ι, a j • basis j) =
        ∑ j : ι, RR (a j • basis j) :=
      map_sum RR _ _
    change RR _ = _
    rw [hRR_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [RR.map_smul]
    rfl
  -- Now the desired bilinear expansion. We separate coefficient computation from
  -- the structural rewrite using an auxiliary `aux T S` lemma.
  have hbilin_aux : ∀ (T : TensorRSModel r s ℝ E) (a : ι → ℝ),
      T = ∑ i : ι, a i • basis i →
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (a i) * (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T a hT
    calc tensorInnerPointwise (I := I) (M := M) g r s b T T
        = tensorInnerPointwise (I := I) (M := M) g r s b
            (∑ i : ι, a i • basis i) (∑ j : ι, a j • basis j) := by rw [← hT]
      _ = ∑ i : ι, (a i) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
              (∑ j : ι, a j • basis j) :=
            hgen_left a (∑ j : ι, a j • basis j)
      _ = ∑ i : ι, (a i) *
            ∑ j : ι, (a j) *
              tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hgen_right a i]
      _ = ∑ i : ι, ∑ j : ι, (a i) * (a j) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
  have hbilin_expand : ∀ T : TensorRSModel r s ℝ E,
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T
    exact hbilin_aux T (fun i => φ i T) (hexpand T)
  -- The function `T ↦ ∑_{i,j} ...` is continuous.
  have hcont : Continuous (fun T : TensorRSModel r s ℝ E =>
      ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
        tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j)) := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    refine continuous_finset_sum _ (fun j _ => ?_)
    refine ((hφ_cont i).mul (hφ_cont j)).mul continuous_const
  -- Conclude by rewriting via `hbilin_expand`.
  refine hcont.congr ?_
  intro T
  exact (hbilin_expand T).symm

/-- For each base point `b`, the function `v ↦ tensorRSRiemannianInnerCLM g r s b v v`
on the bundle fibre is continuous. Pulled back through the continuous CLE `toModel`. -/
lemma tensorRSRiemannianInnerCLM_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) := by
  have heq : (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) =
      (fun v : TensorRSSpace r s I b =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)) := by
    funext v; rw [tensorRSRiemannianInnerCLM_apply]
  rw [heq]
  exact (innerModelRS_quadratic_continuous (I := I) (M := M) g r s b).comp
    (Tensor0SBundle.TensorRSSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b))

/-- `ContinuousAt` form of the diagonal continuity at `0` on the bundle fibre. -/
theorem tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    ContinuousAt (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) 0 :=
  (tensorRSRiemannianInnerCLM_diagonal_continuous (I := I) (M := M) g r s b).continuousAt


/-! ## Von-Neumann boundedness of the inner-product unit ball

The set `{v : TensorRSSpace r s I b | inner b v v < 1}` is von-Neumann bounded.
We follow the Tensor0S strategy: transfer the unit ball to the model fibre via
the CLE `bundleCLERS` and use `posDef_bilin_unit_ball_isBounded`. -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Boundedness on the model fibre: the diagonal sublevel set is metrically
bounded as a subset of `TensorRSModel r s ℝ E`. -/
private lemma innerModelRS_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} := by
  by_cases hNT : Nontrivial (TensorRSModel r s ℝ E)
  · haveI := hNT
    have hPD : ∀ v : TensorRSModel r s ℝ E,
        v ≠ 0 → 0 < innerModelCLMRS (I := I) (M := M) g r s b v v := by
      intro v hv
      change 0 < tensorInnerPointwise (I := I) (M := M) g r s b v v
      have hQpos := (tensorInnerPointwise_eq_zero_iff
        (I := I) (M := M) g r s b v).not.mpr hv
      have hnn := tensorInnerPointwise_nonneg (I := I) (M := M) g r s b v
      exact lt_of_le_of_ne hnn (Ne.symm hQpos)
    have hNN : ∀ v : TensorRSModel r s ℝ E,
        0 ≤ innerModelCLMRS (I := I) (M := M) g r s b v v := fun v =>
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b v
    have hSmulL : ∀ (c : ℝ) (v w : TensorRSModel r s ℝ E),
        innerModelCLMRS (I := I) (M := M) g r s b (c • v) w =
          c * innerModelCLMRS (I := I) (M := M) g r s b v w := by
      intro c v w
      exact innerModelCLMRS_smul_left (I := I) (M := M) g r s b c v w
    have hSmulR : ∀ (c : ℝ) (v w : TensorRSModel r s ℝ E),
        innerModelCLMRS (I := I) (M := M) g r s b v (c • w) =
          c * innerModelCLMRS (I := I) (M := M) g r s b v w := by
      intro c v w
      exact innerModelCLMRS_smul_right (I := I) (M := M) g r s b c v w
    exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
      (innerModelCLMRS (I := I) (M := M) g r s b) hPD hNN hSmulL hSmulR
  · -- Trivial case: subsingleton model fibre.
    have hSubsingleton : Subsingleton (TensorRSModel r s ℝ E) :=
      not_nontrivial_iff_subsingleton.mp hNT
    haveI := hSubsingleton
    refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨1, ?_⟩
    intro v _
    rw [Metric.mem_ball, dist_zero_right]
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, norm_zero]; exact one_pos

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The model-side von-Neumann boundedness. -/
private lemma innerModelRS_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModelRS_diagonal_sublevel_isBounded (I := I) (M := M) g r s b)

/-- Diagonal-clm-apply form of `tensorRSRiemannianInnerCLM` at fixed `b`. -/
private lemma tensorRSRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) := by
  rw [tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 800000 in
/-- Von-Neumann boundedness of the inner-product unit ball on the bundle fibre. -/
theorem tensorRSRiemannianInnerCLM_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {v : TensorRSSpace r s I b |
        tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
  set e : TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b with he_def
  have hModel := innerModelRS_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g r s b
  have hImg :=
    hModel.image (e.symm.toContinuousLinearMap)
  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : TensorRSModel r s ℝ E |
          innerModelCLMRS (I := I) (M := M) g r s b T T < 1} =
      {v : TensorRSSpace r s I b |
          tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_setOf_eq] at hT
      rw [Set.mem_setOf_eq, tensorRSRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I b) T) = T := hRound
      rw [hToModel]
      change tensorInnerPointwise (I := I) (M := M) g r s b T T < 1
      rw [innerModelCLMRS_apply] at hT
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq, tensorRSRiemannianInner_diagonal_clm_apply] at hv
        rw [innerModelCLMRS_apply]
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImg

/-! ## Bundle `RiemannianMetric` packaging

We package the algebraic / continuity / boundedness data into Mathlib's
`Bundle.RiemannianMetric` structure on the `(r, s)`-tensor bundle. -/

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- The bundle Riemannian metric on the `(r, s)`-tensor bundle. -/
noncomputable def tensorRSRiemannianMetric
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => TensorRSSpace r s I b) where
  inner := fun b => tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b
  symm := fun b T S =>
    tensorRSRiemannianInnerCLM_symm (I := I) (M := M) g r s b T S
  pos := fun b T hT =>
    tensorRSRiemannianInnerCLM_pos (I := I) (M := M) g r s b T hT
  continuousAt := fun b =>
    tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
      (I := I) (M := M) g r s b
  isVonNBounded := fun b =>
    tensorRSRiemannianInnerCLM_isVonNBounded (I := I) (M := M) g r s b

end TensorRSRiemannianBundle
end Tensor
end DifferentialGeometry

/-! ## Public `RiemannianBundle` instance for the `(r, s)`-tensor bundle -/

namespace Tensor0SBundle

open DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `RiemannianBundle` class instance for the `(r, s)`-tensor bundle, built
from a smooth tangent-bundle Riemannian metric `g`. Supplied as a definition
parameterised by the metric for downstream `letI`-style installation. -/
@[reducible]
noncomputable def tensorRS_riemannianBundle
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
  ⟨tensorRSRiemannianMetric (I := I) (M := M) g r s⟩

end Tensor0SBundle

/-! ## `IsContinuousRiemannianBundle` instance for the `(r, s)`-tensor bundle

The `IsContinuousRiemannianBundle` typeclass instance for the `(r, s)`-tensor
bundle is installed at a higher layer in the project, in
`Analysis/Parabolic/TensorSpectral/ChartTensor/TensorRSContRiemannianBundle.lean`,
where the chart-frame `(r, s)`-inner product machinery
(`chartTensorInnerPointwise_rs_model`, with its smoothness theorem and bridge
identity) is available. -/
