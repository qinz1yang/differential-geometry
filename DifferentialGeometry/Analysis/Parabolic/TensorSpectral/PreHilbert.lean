import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Tensor.Multilinear.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian
import DifferentialGeometry.Geometry.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn

/-!
# H^1 pre-Hilbert structure on compactly-supported smooth tensor sections

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file installs an `H^1` (gradient-augmented)
pre-Hilbert structure on a wrapper type around `SmoothCcTensor g r s`.

The `H^1` inner product is the sum of the `L^2` inner product of the sections
and the `L^2` inner product of their covariant derivatives, the latter
computed against the inverse Gram matrix of `g` on the canonical model basis:

  ⟨S, T⟩_{H^1} := tensorL2Inner g r s S.toFun T.toFun
                + ∫_M ∑_{i, j} (G(x)⁻¹)_{ij}
                    ⟨(∇S)(x)(e_i), (∇T)(x)(e_j)⟩_g dvol_g

where `∇` is the Levi-Civita-induced covariant derivative on the
`(r, s)`-tensor bundle, `e_i = chartModelBasis E i` is the fixed model-fibre
basis, `(G(x)⁻¹)_{ij} = (gramMatrixAt g x)⁻¹ i j` is the inverse Gram matrix
of `g` on that basis, and `⟨·, ·⟩_g` is the pointwise metric inner product
on tensor fibres.

## Main constructions

* `tensorCovDerivAt g r s S x v` — the directional covariant derivative of a
  smooth compactly-supported `(r, s)`-tensor section at a point.
* `tensorCovDerivPointwiseInner g r s S T x` — the metric-induced pointwise
  Hilbert-Schmidt inner product of two covariant derivatives at a point.
* `tensorH1Inner g r s S T` — the global `H^1` inner product.
* `SmoothCcTensorH1 g r s` — a wrapper around `SmoothCcTensor g r s` carrying
  the `H^1` pre-Hilbert structure.
* `instPreInnerProductSpaceCore` (in the `SmoothCcTensorH1` setting),
  `instSeminormedAddCommGroup`, `instInnerProductSpace`.

## Strategy

The four `PreInnerProductSpace.Core` axioms reduce to algebraic properties
of `tensorL2Inner` (the `L^2` part, already established in companion files)
together with the analogous algebraic properties of the gradient term:

* symmetry, additivity, and homogeneity hold pointwise and integrate;
* non-negativity of the gradient term on the diagonal follows from the same
  spectral argument used in `tensorInnerPointwise_0s_nonneg`.

Integrability of the cross-gradient term is the key analytic ingredient. On a
closed manifold the Riemannian volume measure is finite, so it suffices to
bound the integrand by a continuous (hence bounded on compact `M`) function
and to verify AE-strong measurability. Both properties are obtained by a
chart-by-chart argument that converts the model-frame double sum to the
chart-basis-frame double sum, the latter built from smooth bundle sections
via `covApply_contMDiffOn`.
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
open DifferentialGeometry.Integral.DivergenceTheorem
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

/-- The directional covariant derivative of a smooth compactly-supported
`(r, s)`-tensor section at a point `x`, along a model-fibre direction `v : E`
(canonically identified with `TangentSpace I x`). -/
noncomputable def tensorCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    TensorRSSpace r s I x :=
  tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x v

/-- Unfolding lemma for `tensorCovDerivAt`. -/
lemma tensorCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => S.toSection y) x v := rfl

/-- The directional covariant derivative is additive in the section. -/
lemma tensorCovDerivAt_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x v =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x v +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (S₁ + S₂).toSection y) =
      (fun y : M => S₁.toSection y) + (fun y : M => S₂.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [hpt]
  have hadd := (tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g)).isCovariantDerivativeOn.add
    (σ := fun y : M => S₁.toSection y)
    (σ' := fun y : M => S₂.toSection y)
    (S₁.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (S₂.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (by trivial : x ∈ (Set.univ : Set M))
  have hclm : (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => S₁.toSection y + S₂.toSection y) x =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₁.toSection y) x +
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₂.toSection y) x := hadd
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      (fun y : M => S₁.toSection y + S₂.toSection y) x v = _
  rw [hclm]
  rfl

/-- The directional covariant derivative is `ℝ`-homogeneous in the section. -/
lemma tensorCovDerivAt_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (c • S) x v =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (c • S).toSection y) =
      (fun _ : M => c) • (fun y : M => S.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hpt]
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hf_mdiff : MDiffAt (fun y : M => c) x :=
    (hf_smooth.mdifferentiable (by norm_num)).mdifferentiableAt
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => S.toSection y)
      (g := fun _ : M => c)
      (hσ := (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt)
      (hg := hf_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  have hext_zero : extDerivFun (I := I) (fun _ : M => c) x = 0 := by
    unfold extDerivFun
    simp [mfderiv_const]
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun _ : M => c) • fun y : M => S.toSection y) x v = _
  rw [hcov_leibniz]
  rw [hext_zero]
  simp [ContinuousLinearMap.smul_apply]

/-- The pointwise Hilbert-Schmidt-type inner product of the covariant
derivatives of two smooth compactly-supported `(r, s)`-tensor sections at a
point `x`, expanded against the inverse Gram matrix of `g(x)` on the canonical
model-fibre basis. -/
noncomputable def tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T x ((chartModelBasis E) j)))

/-- Unfolding lemma for `tensorCovDerivPointwiseInner`. -/
lemma tensorCovDerivPointwiseInner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((chartModelBasis E) i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T x
                ((chartModelBasis E) j))) := rfl

/-- Symmetry of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T S x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hG : (gramMatrixAt (I := I) (M := M) g x)⁻¹ j i =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j := by
    have hherm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
    have := hherm.apply i j
    simpa [star_trivial] using this
  rw [hG]
  rw [tensorInnerPointwise_symm]

/-- Additivity in the first argument of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (S₁ + S₂) T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x := by
  unfold tensorCovDerivPointwiseInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hAdd : tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x
        ((chartModelBasis E) i) =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x ((chartModelBasis E) i) +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x ((chartModelBasis E) i) :=
    tensorCovDerivAt_add (I := I) (M := M) g r s S₁ S₂ x ((chartModelBasis E) i)
  rw [hAdd, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  ring

/-- Homogeneity in the first argument of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (c • S) T x =
      c * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hSmul : tensorCovDerivAt (I := I) (M := M) g r s (c • S) x
        ((chartModelBasis E) i) =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i) :=
    tensorCovDerivAt_smul (I := I) (M := M) g r s c S x ((chartModelBasis E) i)
  rw [hSmul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
  ring

/-- Non-negativity of the pointwise gradient inner product on the diagonal,
proved by the spectral argument: diagonalise the inverse Gram matrix,
re-expand the sum into a sum of squares of the pointwise inner product, each
of which is non-negative. -/
lemma tensorCovDerivPointwiseInner_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    0 ≤ tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set Ginv : Matrix (Fin n) (Fin n) ℝ :=
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  have hGinv_psd : Ginv.PosSemidef := by
    simpa [hGinv] using gramMatrixAt_inv_posSemidef (I := I) (M := M) g x
  have hGinv_herm : Ginv.IsHermitian := hGinv_psd.isHermitian
  set vfam : Fin n → TensorRSModel r s ℝ E :=
    fun i => TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i))
    with hvfam_def
  have hspec := hGinv_herm.spectral_theorem
  set U : Matrix (Fin n) (Fin n) ℝ :=
    (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
  set μ : Fin n → ℝ := hGinv_herm.eigenvalues with hμ_def
  have hμ_nonneg : ∀ k, 0 ≤ μ k := hGinv_psd.eigenvalues_nonneg
  have hGinv_entry :
      ∀ i j : Fin n,
        Ginv i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
    intro i j
    have hUDstar : Ginv = U * (Matrix.diagonal μ) * star U := by
      have := hspec
      simp only [Unitary.conjStarAlgAut_apply] at this
      have hofReal : (RCLike.ofReal ∘ hGinv_herm.eigenvalues :
          Fin n → ℝ) = hGinv_herm.eigenvalues := by
        funext k
        simp
      rw [hofReal] at this
      exact this
    rw [hUDstar]
    rw [Matrix.mul_apply]
    have hUD_entry : ∀ k : Fin n,
        (U * Matrix.diagonal μ) i k = U i k * μ k := by
      intro k
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single k]
      · simp [Matrix.diagonal]
      · intro l _ hl
        simp [Matrix.diagonal, hl]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hUD_entry k]
    have hstar : (star U) k j = U j k := by
      simp [Matrix.star_apply, star_trivial]
    rw [hstar]
    ring
  unfold tensorCovDerivPointwiseInner
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
    Ginv i j * tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
  have hrewrite :
      ∑ i : Fin n, ∑ j : Fin n,
        Ginv i j *
          tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
        = ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j) := by
    have hsum_left :
        ∀ (A : Finset (Fin n)) (a : Fin n → ℝ)
          (φ : Fin n → TensorRSModel r s ℝ E)
          (T₀ : TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i ∈ A, a i • φ i) T₀
              =
            ∑ i ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                (a i • φ i) T₀ := by
      intro A a φ T₀
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_left]
      | insert i A hi ih =>
          rw [Finset.sum_insert hi]
          rw [tensorInnerPointwise_add_left]
          rw [ih]
          rw [Finset.sum_insert hi]
    have hsum_right :
        ∀ (A : Finset (Fin n))
          (S₀ : TensorRSModel r s ℝ E)
          (a : Fin n → ℝ) (φ : Fin n → TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              S₀ (∑ j ∈ A, a j • φ j)
              =
            ∑ j ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                S₀ (a j • φ j) := by
      intro A S₀ a φ
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_right]
      | insert j A hj ih =>
          rw [Finset.sum_insert hj]
          rw [tensorInnerPointwise_add_right]
          rw [ih]
          rw [Finset.sum_insert hj]
    have hbilin :
        ∀ k : Fin n,
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i : Fin n, U i k • vfam i)
              (∑ j : Fin n, U j k • vfam j)
            = ∑ i : Fin n, ∑ j : Fin n,
              U i k * U j k *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      intro k
      rw [hsum_left Finset.univ (fun i => U i k) vfam
        (∑ j : Fin n, U j k • vfam j)]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsum_right Finset.univ (U i k • vfam i) (fun j => U j k) vfam]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
      ring
    have hRHS :
        ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j)
          = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (μ k * (U i k * U j k)) *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hbilin k, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    have hLHS :
        ∑ i : Fin n, ∑ j : Fin n,
          Ginv i j *
            tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ j : Fin n,
              ∑ k : Fin n,
                (μ k * (U i k * U j k)) *
                  tensorInnerPointwise (I := I) (M := M) g r s x
                    (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hGinv_entry i j, Finset.sum_mul]
    rw [hLHS]
    have h_swap_inner :
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_comm]
    rw [h_swap_inner, Finset.sum_comm]
  rw [hrewrite]
  refine Finset.sum_nonneg ?_
  intro k _
  refine mul_nonneg (hμ_nonneg k) ?_
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x
    (∑ i : Fin n, U i k • vfam i)

/-- The global H^1 inner product of two smooth compactly-supported
`(r, s)`-tensor sections on a closed Riemannian manifold:

  `⟨S, T⟩_{H^1} := tensorL2Inner g r s S.toFun T.toFun
                 + ∫_M tensorCovDerivPointwiseInner g r s S T x dvol_g(x)`. -/
noncomputable def tensorH1Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) : ℝ :=
  tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

/-- Unfolding lemma for the global H^1 inner product. -/
lemma tensorH1Inner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl

/-- Auxiliary: if `S.toSection y = 0` for all `y` in a neighbourhood of `x`, then
the directional covariant derivative of `S` at `x` vanishes in every direction. -/
private lemma tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M)
    (hx_nhds : ∀ᶠ y in 𝓝 x, S.toSection y = 0) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  set cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  have hS_diff :=
    (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  have hzero_diff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (Bundle.zeroSection (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y)) x :=
    (Bundle.mdifferentiable_zeroSection
      (𝕜 := ℝ) (IB := I) (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)).mdifferentiableAt
  have hev : ∀ᶠ y in 𝓝 x,
      (fun y : M => S.toSection y) y =
        ((0 : (y : M) → TensorRSSpace r s I y)) y := hx_nhds
  have hcongr := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := fun y : M => S.toSection y)
    (σ' := (0 : (y : M) → TensorRSSpace r s I y))
    hS_diff hzero_diff (Filter.univ_mem) hev
  have hcov_zero := cov.isCovariantDerivativeOnUniv.zero
    (x := x) (hx := (by trivial : x ∈ (Set.univ : Set M)))
  unfold tensorCovDerivAt
  change cov.toFun (fun y : M => S.toSection y) x v = (0 : E →L[ℝ] _) v
  rw [hcongr, hcov_zero]
  rfl

/-- If `x ∉ tsupport S.toFun`, then the directional covariant derivative of `S` at `x`
vanishes in every direction. -/
lemma tensorCovDerivAt_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  have hopen : IsOpen (tsupport S.toFun)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hmem : x ∈ (tsupport S.toFun)ᶜ := hx
  have hnhd : (tsupport S.toFun)ᶜ ∈ 𝓝 x := hopen.mem_nhds hmem
  have hev : ∀ᶠ y in 𝓝 x, S.toSection y = 0 := by
    filter_upwards [hnhd] with y hy
    have hy_notsupp : y ∉ Function.support S.toFun := fun hyS => hy (subset_tsupport _ hyS)
    have hy_zero : S.toFun y = 0 := by
      simpa [Function.support, Function.mem_support] using hy_notsupp
    have hto : TensorRSSpace.toModel (S.toSection y) = 0 := by
      have : S.toFun y = TensorRSSpace.toModel (S.toSection y) := rfl
      rw [this] at hy_zero
      exact hy_zero
    have htoModel_zero : TensorRSSpace.toModel
        (0 : TensorRSSpace r s I y) = 0 := TensorRSSpace.toModel_zero
    have hcomb : TensorRSSpace.toModel (S.toSection y) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I y) := by
      rw [hto, htoModel_zero]
    exact TensorRSSpace.toModel_injective
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := y) hcomb
  exact tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (I := I) (M := M) g r s S x hev v

/-- The integrand vanishes at any point outside `tsupport S.toFun`. -/
private lemma tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x = 0 := by
  unfold tensorCovDerivPointwiseInner
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S x
      ((chartModelBasis E) i) = 0 :=
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S
      hx ((chartModelBasis E) i)
  rw [hSi, TensorRSSpace.toModel_zero, tensorInnerPointwise_zero_left]
  ring

/-- The integrand `tensorCovDerivPointwiseInner g r s S T` has compact support: it
vanishes outside `tsupport S.toFun`, which is compact in `M`. -/
theorem tensorCovDerivPointwiseInner_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    HasCompactSupport
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  refine IsCompact.of_isClosed_subset S.hasCompactSupport (isClosed_tsupport _) ?_
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  exact hx (tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (I := I) (M := M) g r s S T hx_notsupp)

/-- The topological support of the integrand `tensorCovDerivPointwiseInner g r s
S T` is contained in the topological support of `S.toFun`: the integrand
vanishes wherever the first section vanishes. -/
theorem tensorCovDerivPointwiseInner_tsupport_subset_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tsupport (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      tsupport S.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx_notsupp
  exact hx (tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (I := I) (M := M) g r s S T hx_notsupp)

/-- The topological support of the integrand `tensorCovDerivPointwiseInner g r s
S T` is contained in the topological support of `T.toFun`: the integrand
vanishes wherever the second section vanishes. -/
theorem tensorCovDerivPointwiseInner_tsupport_subset_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tsupport (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      tsupport T.toFun := by
  have hswap : tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T S := by
    funext x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x
  rw [hswap]
  exact tensorCovDerivPointwiseInner_tsupport_subset_left
    (I := I) (M := M) g r s T S

/-- An abstract linear-algebra identity: for any change-of-basis matrix `T` and
any inner product matrix `G` with `G' := T^T G T` (the Gram matrix under the new
basis), the trace expression `∑_{ij} G⁻¹_{ij} ⟨L(e_i), L(e_j)⟩` is independent of
the basis, when `L` is linear and `⟨·,·⟩` is a bilinear form.

Formulated as: if `e_i' = ∑_k T_{ki} e_k`, then
`∑_{ij} G'⁻¹_{ij} B(e_i', e_j') = ∑_{ij} G⁻¹_{ij} B(e_i, e_j)`
where `B(u, v) := ⟨L(u), L(v)⟩` and `G'_{ij} := ⟨e_i', e_j'⟩` (Gram), provided
`G_{ij} := ⟨e_i, e_j⟩`. -/
private lemma trace_invariance_under_change_of_basis
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    let G' := Tᵀ * G * T
    let B' := Tᵀ * B * T
    ∑ i : Fin n, ∑ j : Fin n, G'⁻¹ i j * B' i j =
      ∑ i : Fin n, ∑ j : Fin n, G⁻¹ i j * B i j := by
  classical
  simp only
  have hsum_eq : ∀ M N : Matrix (Fin n) (Fin n) ℝ,
      ∑ i : Fin n, ∑ j : Fin n, M i j * N i j = Matrix.trace (M * Nᵀ) := by
    intro M N
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Matrix.transpose_apply]
  rw [hsum_eq, hsum_eq]
  set G' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * G * T with hG'_def
  have hG'_inv : G'⁻¹ = T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ := by
    rw [hG'_def]
    have hT_unit : IsUnit T := hT
    have hTT_unit : IsUnit Tᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
      simpa [Matrix.det_transpose] using hT
    have hG_unit : IsUnit G := hG
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mul_assoc]
  rw [hG'_inv]
  set B' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * B * T with hB'_def
  have hB'_trans : B'ᵀ = Tᵀ * Bᵀ * T := by
    rw [hB'_def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mul_assoc]
  rw [hB'_trans]
  have hTT_unit : IsUnit Tᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
    simpa [Matrix.det_transpose] using hT
  have hT_inv_T : (Tᵀ)⁻¹ * Tᵀ = 1 := Matrix.nonsing_inv_mul _
    (by simpa [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] using hT)
  have hT_T_inv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (by simpa [Matrix.isUnit_iff_isUnit_det] using hT)
  have hcyc :
      T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T) =
        T⁻¹ * G⁻¹ * ((Tᵀ)⁻¹ * Tᵀ) * Bᵀ * T := by
    repeat rw [mul_assoc]
  rw [hcyc, hT_inv_T, mul_one]
  have hreassoc : T⁻¹ * G⁻¹ * Bᵀ * T = T⁻¹ * (G⁻¹ * Bᵀ * T) := by
    rw [mul_assoc T⁻¹ G⁻¹ Bᵀ, mul_assoc T⁻¹ (G⁻¹ * Bᵀ) T]
  rw [hreassoc, Matrix.trace_mul_comm T⁻¹ (G⁻¹ * Bᵀ * T)]
  rw [mul_assoc (G⁻¹ * Bᵀ) T T⁻¹, hT_T_inv, mul_one]

/-- The integrand `tensorCovDerivPointwiseInner g r s S T b` rewritten using the
chart-α basis `chartBasisVecFiber α i b` instead of `chartModelBasis E i`. The
expression involves the chart-α Gram matrix `chartGramMatrix g α b`. -/
noncomputable def chartTensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (chartGramMatrix (I := I) g α b)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b)))

/-- The change-of-basis matrix from `chartModelBasis E` to `chartBasisFamily α b`
(at base-set points `b`). The `(k, i)` entry is the `e_k`-coefficient of
`chartBasisVecFiber α i b` in the basis `chartModelBasis E`. -/
private noncomputable def chartBasisTransitionMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    ((chartModelBasis E).repr (chartBasisVecFiber (I := I) α i b)) k

/-- Recovery formula: `chartBasisVecFiber α i b = ∑_k T_{ki} (chartModelBasis E k)`,
where `T = chartBasisTransitionMatrix α b`. This is `Module.Basis.sum_repr` for the
basis `chartModelBasis E` applied to the vector `chartBasisVecFiber α i b`. -/
private lemma chartBasisVecFiber_eq_sum_chartModelBasis
    (α : M) (b : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i b =
      ∑ k : Fin (Module.finrank ℝ E),
        chartBasisTransitionMatrix (I := I) α b k i • (chartModelBasis E) k := by
  classical
  unfold chartBasisTransitionMatrix
  simp only [Matrix.of_apply]
  exact (((chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i b))).symm

/-- Identification: `chartBasisTransitionMatrix α b = (chartModelBasis E).toMatrix
(fun i => chartBasisVecFiber α i b)`. -/
private lemma chartBasisTransitionMatrix_eq_toMatrix
    (α : M) (b : M) :
    chartBasisTransitionMatrix (I := I) α b =
      (chartModelBasis E).toMatrix
        (fun i : Fin (Module.finrank ℝ E) =>
          chartBasisVecFiber (I := I) α i b) := by
  classical
  unfold chartBasisTransitionMatrix
  ext k i
  rw [Module.Basis.toMatrix_apply, Matrix.of_apply]

/-- The change-of-basis matrix is invertible at base-set points. -/
private lemma chartBasisTransitionMatrix_isUnit
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartBasisTransitionMatrix (I := I) α b) := by
  classical
  rw [chartBasisTransitionMatrix_eq_toMatrix]
  set chartBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartBasisFamily (I := I) α hb with hCB_def
  have hfam_eq : (fun i : Fin (Module.finrank ℝ E) =>
      chartBasisVecFiber (I := I) α i b)
      = (chartBasis : Fin (Module.finrank ℝ E) → E) := by
    funext i
    rw [hCB_def]
    exact (chartBasisFamily_apply (I := I) α hb i).symm
  rw [hfam_eq]
  refine ⟨⟨_, chartBasis.toMatrix (chartModelBasis E), ?_, ?_⟩, rfl⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- A helper: a continuous bilinear form on `E` evaluated on linear combinations of
basis vectors. -/
private lemma g_inner_bilinear_expand
    (g : SmoothRiemannianMetric I M) (b : M) {n : ℕ}
    (a c : Fin n → ℝ) (u : Fin n → E) :
    g.inner b (∑ k : Fin n, a k • u k) (∑ l : Fin n, c l • u l) =
      ∑ k : Fin n, ∑ l : Fin n,
        a k * c l * g.inner b (u k) (u l) := by
  classical
  have houter : g.inner b (∑ k : Fin n, a k • u k) =
      ∑ k : Fin n, a k • (g.inner b (u k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [map_smul, smul_eq_mul]
  ring

/-- Gram-matrix transformation: `chartGramMatrix g α b = T^T * gramMatrixAt g b * T`
where `T = chartBasisTransitionMatrix α b`. This holds for all `b`. -/
private lemma chartGramMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartGramMatrix (I := I) g α b =
      (chartBasisTransitionMatrix (I := I) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartBasisTransitionMatrix (I := I) α b := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set T : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hT_def
  ext i j
  rw [chartGramMatrix_apply]
  rw [chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i,
      chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j]
  rw [g_inner_bilinear_expand g b
        (fun k => T k i) (fun l => T l j) (chartModelBasis E)]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, gramMatrixAt_apply]
  ring

/-- Bilinearity of `tensorInnerPointwise` in the left argument over a finite sum. -/
lemma tensorInnerPointwise_sum_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : ι → TensorRSModel r s ℝ E)
    (c : ι → ℝ) (B : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b (∑ k ∈ s', c k • A k) B =
      ∑ k ∈ s', c k *
        tensorInnerPointwise (I := I) (M := M) g r s b (A k) B := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_left]
  | insert i₀ s'' hi₀ ih =>
      rw [Finset.sum_insert hi₀, tensorInnerPointwise_add_left,
          tensorInnerPointwise_smul_left, ih, Finset.sum_insert hi₀]

/-- Bilinearity of `tensorInnerPointwise` in the right argument over a finite sum. -/
lemma tensorInnerPointwise_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : TensorRSModel r s ℝ E)
    (B : ι → TensorRSModel r s ℝ E) (c : ι → ℝ) :
    tensorInnerPointwise (I := I) (M := M) g r s b A (∑ l ∈ s', c l • B l) =
      ∑ l ∈ s', c l *
        tensorInnerPointwise (I := I) (M := M) g r s b A (B l) := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_right]
  | insert j₀ s'' hj₀ ih =>
      rw [Finset.sum_insert hj₀, tensorInnerPointwise_add_right,
          tensorInnerPointwise_smul_right, ih, Finset.sum_insert hj₀]

/-- The B-matrix transformation: `B'_{ij} = (T^T B T)_{ij}` where
`B'_{ij} = tensorInnerPointwise (toModel(cov_S e'_i)) (toModel(cov_T e'_j))`,
`B_{ij}` is the same with `e_i`, and `T = chartBasisTransitionMatrix α b`. -/
private lemma chartTensorCovDeriv_innerMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))) =
      ((chartBasisTransitionMatrix (I := I) α b)ᵀ *
          (Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  ((chartModelBasis E) l)))) *
          chartBasisTransitionMatrix (I := I) α b) i j := by
  classical
  set Tmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  have hexp_i := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i
  have hexp_j := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b) =
      ∑ k : Fin (Module.finrank ℝ E), Tmat k i •
        tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k) := by
    rw [hexp_i]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  have hTj : tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b) =
      ∑ l : Fin (Module.finrank ℝ E), Tmat l j •
        tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l) := by
    rw [hexp_j]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
  rw [hSi, hTj]
  have htoM_sum : ∀ (s' : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → TensorRSSpace r s I b)
      (c : Fin (Module.finrank ℝ E) → ℝ),
      TensorRSSpace.toModel (∑ k ∈ s', c k • f k) =
        ∑ k ∈ s', c k • TensorRSSpace.toModel (f k) := by
    intro s' f c
    classical
    induction s' using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add,
            TensorRSSpace.toModel_smul, ih, Finset.sum_insert hi₀]
  have htoM_left := htoM_sum Finset.univ
    (fun k => tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k))
    (fun k => Tmat k i)
  have htoM_right := htoM_sum Finset.univ
    (fun l => tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l))
    (fun l => Tmat l j)
  rw [htoM_left, htoM_right]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ]
  conv_lhs =>
    rhs
    ext k
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b Finset.univ]
    rw [Finset.mul_sum]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.transpose_apply, Matrix.of_apply]
  ring

/-- **The coordinate-invariance identity**: on the chart base set,
the chart-α-frame integrand equals the model-basis integrand. -/
lemma chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b := by
  classical
  set n := Module.finrank ℝ E
  set Tmat : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  set Gmat : Matrix (Fin n) (Fin n) ℝ :=
    gramMatrixAt (I := I) (M := M) g b with hGmat_def
  set Bmat : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun k l : Fin n =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l)))
    with hBmat_def
  unfold chartTensorCovDerivPointwiseInner
  unfold tensorCovDerivPointwiseInner
  have hG_eq : chartGramMatrix (I := I) g α b = Tmatᵀ * Gmat * Tmat :=
    chartGramMatrix_eq_transition (I := I) g α b
  have hLHS_term_eq : ∀ i j : Fin n,
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (chartBasisVecFiber (I := I) α j b))) =
        (Tmatᵀ * Bmat * Tmat) i j := by
    intro i j
    exact chartTensorCovDeriv_innerMatrix_eq_transition (I := I) (M := M) g α r s S T b i j
  have hLHS_rewrite :
      ∑ i : Fin n, ∑ j : Fin n,
          (chartGramMatrix (I := I) g α b)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  (chartBasisVecFiber (I := I) α j b))) =
        ∑ i : Fin n, ∑ j : Fin n,
          (Tmatᵀ * Gmat * Tmat)⁻¹ i j * (Tmatᵀ * Bmat * Tmat) i j := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hLHS_term_eq i j, hG_eq]
  rw [hLHS_rewrite]
  have hT_unit : IsUnit Tmat := chartBasisTransitionMatrix_isUnit (I := I) α hb
  have hG_unit : IsUnit Gmat := by
    rw [hGmat_def]
    have hinv_herm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g b
    have hpos := gramMatrixAt_inv_posSemidef (I := I) (M := M) g b
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hposdef : (gramMatrixAt (I := I) (M := M) g b).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (gramMatrixAt_isHermitian (I := I) (M := M) g b) ?_
      intro v hv
      let w : E := ∑ i : Fin (Module.finrank ℝ E),
        v i • (chartModelBasis E) i
      have hw_ne : w ≠ 0 := by
        intro h
        have hlin : LinearIndependent ℝ ((chartModelBasis E) : Fin _ → E) :=
          (chartModelBasis E).linearIndependent
        rw [Fintype.linearIndependent_iff] at hlin
        exact hv (funext (hlin v h))
      have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g b) *ᵥ v =
          g.inner b w w := by
        have hexp : g.inner b w w =
            ∑ j : Fin (Module.finrank ℝ E),
              v j * ∑ i : Fin (Module.finrank ℝ E),
                v i * gramMatrixAt (I := I) (M := M) g b i j := by
          change g.inner b (∑ i, v i • (chartModelBasis E) i)
              (∑ j, v j • (chartModelBasis E) j) = _
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          have hsm1 : (g.inner b (∑ i, v i • (chartModelBasis E) i))
                (v j • (chartModelBasis E) j) =
              v j * (g.inner b (∑ i, v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) := by
            rw [map_smul, smul_eq_mul]
          rw [hsm1]
          congr 1
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsm2 : (g.inner b (v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) =
              v i * (g.inner b ((chartModelBasis E) i)) ((chartModelBasis E) j) := by
            rw [show (g.inner b) (v i • (chartModelBasis E) i) =
                v i • (g.inner b) ((chartModelBasis E) i) from by rw [map_smul]]
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hsm2, gramMatrixAt_apply]
        rw [hexp]
        change ∑ j : Fin (Module.finrank ℝ E),
            star (v j) * (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * gramMatrixAt (I := I) (M := M) g b i j
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_trivial]
        rw [show (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
              ∑ i : Fin (Module.finrank ℝ E),
                gramMatrixAt (I := I) (M := M) g b j i * v i from rfl]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [gramMatrixAt_apply, gramMatrixAt_apply, g.symm]
        ring
      rw [hquad]
      exact g.pos b w hw_ne
    have hdet_pos := hposdef.det_pos
    exact ne_of_gt hdet_pos
  exact trace_invariance_under_change_of_basis Tmat hT_unit Gmat hG_unit Bmat

/-- The transition matrix from the canonical model basis `chartModelBasis E`
to an arbitrary tangent frame `frame : Fin n → E`: the `(k, i)`-entry is the
`e_k`-coefficient of `frame i` in the model basis. -/
private noncomputable def frameTransitionMatrix
    (frame : Fin (Module.finrank ℝ E) → E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i => ((chartModelBasis E).repr (frame i)) k

/-- Recovery formula: each frame vector is the model-basis expansion with the
transition-matrix coefficients. -/
private lemma frame_eq_sum_chartModelBasis
    (frame : Fin (Module.finrank ℝ E) → E) (i : Fin (Module.finrank ℝ E)) :
    frame i =
      ∑ k : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame k i • (chartModelBasis E) k := by
  classical
  unfold frameTransitionMatrix
  simp only [Matrix.of_apply]
  exact ((chartModelBasis E).sum_repr (frame i)).symm

/-- The transition matrix of a basis frame is invertible. -/
private lemma frameTransitionMatrix_isUnit
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    IsUnit (frameTransitionMatrix (E := E)
      (frame : Fin (Module.finrank ℝ E) → E)) := by
  classical
  have hmat : frameTransitionMatrix (E := E)
      (frame : Fin (Module.finrank ℝ E) → E) =
      (chartModelBasis E).toMatrix (frame : Fin (Module.finrank ℝ E) → E) := by
    unfold frameTransitionMatrix
    ext k i
    rw [Module.Basis.toMatrix_apply, Matrix.of_apply]
  rw [hmat]
  refine ⟨⟨_, frame.toMatrix (chartModelBasis E), ?_, ?_⟩, rfl⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

/-- The frame Gram matrix `(g(b)(frameᵢ, frameⱼ))` equals `Tᵀ * G * T`, where
`T` is the transition matrix from the model basis to the frame and `G` is the
model-basis Gram matrix `gramMatrixAt g b`. -/
private lemma frameGram_eq_transition
    (g : SmoothRiemannianMetric I M) (b : M)
    (frame : Fin (Module.finrank ℝ E) → E) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        g.inner b (frame i) (frame j)) =
      (frameTransitionMatrix (E := E) frame)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        frameTransitionMatrix (E := E) frame := by
  classical
  ext i j
  rw [Matrix.of_apply]
  rw [frame_eq_sum_chartModelBasis (E := E) frame i,
    frame_eq_sum_chartModelBasis (E := E) frame j]
  rw [g_inner_bilinear_expand g b
        (fun k => frameTransitionMatrix (E := E) frame k i)
        (fun l => frameTransitionMatrix (E := E) frame l j) (chartModelBasis E)]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, gramMatrixAt_apply]
  ring

/-- The frame inner-product matrix `(⟨∇_{frameᵢ}S, ∇_{frameⱼ}T⟩)ᵢⱼ` equals
`Tᵀ * B * T`, where `B` is the model-basis inner-product matrix. -/
private lemma frameInnerMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Fin (Module.finrank ℝ E) → E)
    (i j : Fin (Module.finrank ℝ E)) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
      ((frameTransitionMatrix (E := E) frame)ᵀ *
          (Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  ((chartModelBasis E) l)))) *
          frameTransitionMatrix (E := E) frame) i j := by
  classical
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S b (frame i) =
      ∑ k : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame k i •
        tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k) := by
    rw [frame_eq_sum_chartModelBasis (E := E) frame i]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  have hTj : tensorCovDerivAt (I := I) (M := M) g r s T b (frame j) =
      ∑ l : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame l j •
        tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l) := by
    rw [frame_eq_sum_chartModelBasis (E := E) frame j]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
  rw [hSi, hTj]
  have htoM_sum : ∀ (s' : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → TensorRSSpace r s I b)
      (c : Fin (Module.finrank ℝ E) → ℝ),
      TensorRSSpace.toModel (∑ k ∈ s', c k • f k) =
        ∑ k ∈ s', c k • TensorRSSpace.toModel (f k) := by
    intro s' f c
    classical
    induction s' using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add,
            TensorRSSpace.toModel_smul, ih, Finset.sum_insert hi₀]
  rw [htoM_sum Finset.univ
        (fun k => tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k))
        (fun k => frameTransitionMatrix (E := E) frame k i),
      htoM_sum Finset.univ
        (fun l => tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l))
        (fun l => frameTransitionMatrix (E := E) frame l j)]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ]
  conv_lhs =>
    rhs
    ext k
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b Finset.univ]
    rw [Finset.mul_sum]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.transpose_apply, Matrix.of_apply]
  ring

/-- **Frame-invariance of the gradient inner product.** For any tangent
*basis* frame `frame` at `b`, the inverse-frame-Gram-weighted double sum of
the directional covariant derivatives equals the canonical
`tensorCovDerivPointwiseInner`. -/
lemma tensorCovDerivPointwiseInner_eq_frameGram_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
          g.inner b (frame i') (frame j'))⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b := by
  classical
  let Tmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    frameTransitionMatrix (E := E) (frame : Fin (Module.finrank ℝ E) → E)
  let Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    gramMatrixAt (I := I) (M := M) g b
  let Bmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l)))
  have hG_eq : (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
      g.inner b (frame i') (frame j')) = Tmatᵀ * Gmat * Tmat :=
    frameGram_eq_transition (I := I) (M := M) g b (frame : Fin (Module.finrank ℝ E) → E)
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
            g.inner b (frame i') (frame j'))⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
        (Tmatᵀ * Gmat * Tmat)⁻¹ i j * (Tmatᵀ * Bmat * Tmat) i j := by
    intro i j
    rw [frameInnerMatrix_eq_transition (I := I) (M := M) g r s S T b
      (frame : Fin (Module.finrank ℝ E) → E) i j, hG_eq]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  unfold tensorCovDerivPointwiseInner
  have hT_unit : IsUnit Tmat := frameTransitionMatrix_isUnit (E := E) frame
  have hG_unit : IsUnit Gmat := by
    have hGmat_def : Gmat = gramMatrixAt (I := I) (M := M) g b := rfl
    rw [hGmat_def, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hposdef : (gramMatrixAt (I := I) (M := M) g b).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (gramMatrixAt_isHermitian (I := I) (M := M) g b) ?_
      intro v hv
      let w : E := ∑ i : Fin (Module.finrank ℝ E),
        v i • (chartModelBasis E) i
      have hw_ne : w ≠ 0 := by
        intro h
        have hlin : LinearIndependent ℝ ((chartModelBasis E) : Fin _ → E) :=
          (chartModelBasis E).linearIndependent
        rw [Fintype.linearIndependent_iff] at hlin
        exact hv (funext (hlin v h))
      have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g b) *ᵥ v =
          g.inner b w w := by
        have hexp : g.inner b w w =
            ∑ j : Fin (Module.finrank ℝ E),
              v j * ∑ i : Fin (Module.finrank ℝ E),
                v i * gramMatrixAt (I := I) (M := M) g b i j := by
          change g.inner b (∑ i, v i • (chartModelBasis E) i)
              (∑ j, v j • (chartModelBasis E) j) = _
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          have hsm1 : (g.inner b (∑ i, v i • (chartModelBasis E) i))
                (v j • (chartModelBasis E) j) =
              v j * (g.inner b (∑ i, v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) := by
            rw [map_smul, smul_eq_mul]
          rw [hsm1]
          congr 1
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsm2 : (g.inner b (v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) =
              v i * (g.inner b ((chartModelBasis E) i)) ((chartModelBasis E) j) := by
            rw [show (g.inner b) (v i • (chartModelBasis E) i) =
                v i • (g.inner b) ((chartModelBasis E) i) from by rw [map_smul]]
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hsm2, gramMatrixAt_apply]
        rw [hexp]
        change ∑ j : Fin (Module.finrank ℝ E),
            star (v j) * (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * gramMatrixAt (I := I) (M := M) g b i j
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_trivial]
        rw [show (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
              ∑ i : Fin (Module.finrank ℝ E),
                gramMatrixAt (I := I) (M := M) g b j i * v i from rfl]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [gramMatrixAt_apply, gramMatrixAt_apply, g.symm]
        ring
      rw [hquad]
      exact g.pos b w hw_ne
    exact ne_of_gt hposdef.det_pos
  exact trace_invariance_under_change_of_basis Tmat hT_unit Gmat hG_unit Bmat

/-- **Orthonormal-frame diagonal form of the gradient inner product.** For a
`g(b)`-orthonormal *basis* frame `frame` at `b`, the Dirichlet integrand
`tensorCovDerivPointwiseInner g r s S T b` equals the plain diagonal sum
`∑ᵢ ⟨∇_{frameᵢ}S, ∇_{frameᵢ}T⟩` of the pointwise tensor inner products of the
directional covariant derivatives. -/
lemma tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (horth : ∀ i j, g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b (frame i))) := by
  classical
  have hGframe_eq_one :
      (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
        g.inner b (frame i') (frame j')) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
    ext i j
    rw [Matrix.of_apply, horth i j, Matrix.one_apply]
  rw [← tensorCovDerivPointwiseInner_eq_frameGram_sum (I := I) (M := M) g r s S T b
    frame]
  rw [hGframe_eq_one, inv_one]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hji
    rw [Matrix.one_apply_ne (Ne.symm hji), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The covariant derivative of a smooth compactly-supported tensor section
applied to a chart-basis tangent vector field is smooth as a tensor section
on the chart base set. -/
lemma tensorCovDeriv_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have := chartBasisVec_contMDiffOn (I := I) α i
    exact this
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hcov_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) x₀ :=
    hop.contMDiffAt (Filter.univ_mem)
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b)) x₀ :=
    (hX_on x₀ hx₀).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  exact hcov_at.clm_bundle_apply hX_at

/-- The trivialization-α-image of `cov_S b · chartBasisVecFiber α i b` is smooth on
chart α base set. By bundle smoothness of the section, the chart-α trivialization
image is smooth in `b`. -/
lemma tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)⟩).2)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hsection := tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s S α i
  have hbase_eq : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := by
    change ((trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (trivializationAt E (TangentSpace I) α).baseSet
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet =
            (trivializationAt E (TangentSpace I) α).baseSet
    exact Set.inter_self _
  rw [← hbase_eq]
  rw [← Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α)]
  rw [hbase_eq]
  exact hsection

/-- Linear "evaluation at all basis tuples" map on `Tensor0SModel n ℝ E`. -/
private noncomputable def evalAtBasisLinearLocal (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

@[simp] private lemma evalAtBasisLinearLocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinearLocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

/-- `evalAtBasisLinearLocal` is injective: two multilinear forms agreeing on
all model-basis tuples are equal. -/
private lemma evalAtBasisLinearLocal_injective (n : ℕ) :
    Function.Injective (evalAtBasisLinearLocal (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

/-- Dimension of the model fibre `Tensor0SModel n ℝ E`. -/
private lemma finrank_tensor0SModel_local (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

private lemma finrank_basis_pi_local (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

private lemma evalAtBasisLinearLocal_bijective (n : ℕ) :
    Function.Bijective (evalAtBasisLinearLocal (E := E) n) := by
  have h_inj := evalAtBasisLinearLocal_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_local, finrank_basis_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

private noncomputable def evalAtBasisCLELocal (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (evalAtBasisLinearLocal (E := E) n)
    (evalAtBasisLinearLocal_bijective (E := E) n)).toContinuousLinearEquiv

@[simp] private lemma evalAtBasisCLELocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLELocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

/-- Smoothness into `Tensor0SModel n ℝ E` from smoothness of basis-tuple
evaluations. Sister of the private
`TensorMetricLowering.contMDiffOn_into_tensor0SModel_of_eval_basis`. -/
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_local
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLELocal (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLELocal (E := E) n).symm :=
    (evalAtBasisCLELocal (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLELocal (E := E) n).symm_apply_apply (Φ b)).symm

/-- Local unfolding of `loweredCompose` at a model-basis tuple. -/
private lemma loweredCompose_at_basis_tuple_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    loweredCompose (I := I) (M := M) g r s α b T
        (fun i : Fin (r + s) => (chartModelBasis E) (φ i)) =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ i) b) := by
  rw [loweredCompose_apply]
  rfl

/-- Smoothness of `(chartGramMatrix g α ·)⁻¹ i j` on the chart-α base set. -/
private lemma chartGramMatrixInv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix (I := I) g α b).det⁻¹ *
              (chartGramMatrix (I := I) g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix (I := I) g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix (I := I) g α b).det ≠ 0 := ne_of_gt hpos
  exact (ContMDiffWithinAt.inv₀ hdet hpos_ne).mul hadj

/-- The `(0, r)` separable-form bundle section, attached to a chart-α base
point, evaluated at the chart-α basis indexed by `φ_first`. The trivialisation
fibre at `α` evaluates, on a model-basis tuple `e_ψ`, to a product of
chart-Gram-matrix entries. -/
private noncomputable def separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    M → TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
  fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
    (E := fun y : M => Tensor0SSpace r I y) b
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))

/-- The trivialisation fibre at `α` of the `(0, r)` separable-form bundle
section, evaluated on a model-basis tuple `e_ψ`, equals a product of
chart-Gram-matrix entries. -/
private theorem trivializationAt_separableFormBundleSectionLocal_eval_basis
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) {b : M}
    (_hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (ψ : Fin r → Fin (Module.finrank ℝ E)) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first b)).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  unfold separableFormBundleSectionLocal
  change ((separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)).compContinuousLinearMap
        (fun _ : Fin r => (trivializationAt E (TangentSpace I) α).symmL ℝ b))
      (fun k : Fin r => (chartModelBasis E) (ψ k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramMatrix_apply]
  rfl

/-- The `(0, r)` separable-form bundle section is smooth on the chart base set
at `α` — a sister of `TensorMetricLowering.contMDiffOn_separableFormBundleSection`
that we re-derive here to avoid the `private` qualifier on the original. -/
private lemma contMDiffOn_separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set e : Trivialization (Tensor0SModel r ℝ E)
    (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) → M) :=
    trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α
  have hbaseSet_eq : e.baseSet = (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_iff := e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
    (s := fun b => Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))
  rw [hbaseSet_eq] at h_iff
  refine h_iff.mpr ?_
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro ψ
  have h_prod_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    refine contMDiffOn_finset_prod (fun k _ => ?_)
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)
  refine h_prod_smooth.congr (fun b hb => ?_)
  exact trivializationAt_separableFormBundleSectionLocal_eval_basis
    (I := I) (M := M) g r α φ_first hb ψ

/-- Chart-local smoothness of
`b ↦ lowerAllUpperIndices g r s b (toModel (cov_S(b) · chartBasisVecFiber α i b))
        (chartBasisVec α (φ ·) b)`
on the chart base set. -/
private lemma contMDiffOn_lower_chartCov_at_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E))
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (fun j : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ j) b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have h_sep_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (separableFormBundleSectionLocal (I := I) (M := M) g r α
          (fun k : Fin r => φ (Fin.castAdd s k)))
        x₀ :=
    (contMDiffOn_separableFormBundleSectionLocal (I := I) (M := M) g r α
      (fun k : Fin r => φ (Fin.castAdd s k))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_S_smooth_on := tensorCovDeriv_chartBasis_contMDiffOn
    (I := I) (M := M) g r s S α i
  have h_S_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))) x₀ :=
    h_S_smooth_on.contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_applied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace s I y) b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))
            (Tensor0SSpace.ofModel
              (separableFormAt (I := I) (M := M) g b r
                (fun k : Fin r =>
                  chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (IM := I) (IB := I)
      (b := id)
      (ϕ := fun b : M =>
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
      (v := fun b : M =>
        Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b)))
      h_S_smooth_at h_sep_smooth_at
  have h_tangent_smooth_at : ∀ j : Fin s,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)) x₀ := by
    intro j
    exact (chartBasisVec_contMDiffOn (I := I) α (φ (Fin.natAdd r j))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_eval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M)
    (T := fun b : M =>
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))
        (Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))
    h_applied
    (v := fun (j : Fin s) (b : M) =>
      chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)
    h_tangent_smooth_at
  refine h_eval.congr_of_eventuallyEq ?_
  filter_upwards with b
  rw [lowerAllUpperIndices_apply]
  rfl

/-- Chart-local smoothness of
`b ↦ loweredCompose g r s α b (toModel (cov_S(b) · chartBasisVecFiber α i b))`
as a function valued in `Tensor0SModel (r + s) ℝ E`, on the chart base set. -/
private lemma contMDiffOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple_local
      (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b))) φ).symm)
  exact contMDiffOn_lower_chartCov_at_basis (I := I) (M := M) g r s S α i φ

/-- Chart-local continuity (as `ContinuousOn`) of the above. -/
private lemma continuousOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (contMDiffOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i).continuousOn

/-- Chart-local continuity, on the chart-α base set, of
`b ↦ tensorInnerPointwise g r s b
       (toModel (cov_S(b) · chartBasisVecFiber α i b))
       (toModel (cov_T(b) · chartBasisVecFiber α j b))`. -/
private lemma continuousOn_tensorInnerPointwise_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hSα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i
  have hTα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s T α j
  have hchart :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn
      (I := I) (M := M) g α r s
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b)))
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (chartBasisVecFiber (I := I) α j b)))
      hSα hTα
  refine ContinuousOn.congr hchart ?_
  intro b hb
  exact tensorInnerPointwise_bridge_identity
    (I := I) (M := M) g α r s hb
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)))
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b)))

private lemma chartTensorCovDerivPointwiseInner_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartTensorCovDerivPointwiseInner
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact (chartGramMatrixInv_entry_contMDiffOn (I := I) (M := M) g α i j).continuousOn
  · exact continuousOn_tensorInnerPointwise_chartCov (I := I) (M := M) g r s S T α i j

/-- **Global continuity** of the gradient integrand
`tensorCovDerivPointwiseInner g r s S T`. The proof glues chart-local continuity
(via the coordinate-invariance identity) over the chart cover of `M`. -/
theorem tensorCovDerivPointwiseInner_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have h_chart_cont := chartTensorCovDerivPointwiseInner_continuousOn
    (I := I) (M := M) g r s S T x
  have h_cong : ∀ b ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
        chartTensorCovDerivPointwiseInner (I := I) (M := M) g x r s S T b := by
    intro b hb
    exact (chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
      (I := I) (M := M) g x r s S T hb).symm
  have h_local : ContinuousOn
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    h_chart_cont.congr h_cong
  exact h_local.continuousAt (hOpen.mem_nhds hx_base)

/-- **Integrability** of the gradient integrand against the Riemannian volume
measure on a closed manifold. Follows from continuity and compact support of
the integrand, plus the local-finiteness of the Riemannian volume measure. -/
theorem tensorCovDerivPointwiseInner_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (tensorCovDerivPointwiseInner_continuous
      (I := I) (M := M) g r s S T).integrable_of_hasCompactSupport
    (tensorCovDerivPointwiseInner_hasCompactSupport
      (I := I) (M := M) g r s S T)

/-- Symmetry of `tensorH1Inner`. -/
theorem tensorH1Inner_symm (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorH1Inner (I := I) (M := M) g r s T S := by
  unfold tensorH1Inner
  congr 1
  · exact tensorL2Inner_symm (I := I) (M := M) g r s S.toFun T.toFun
  · refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x

/-- Non-negativity of `tensorH1Inner` on the diagonal. -/
theorem tensorH1Inner_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ tensorH1Inner (I := I) (M := M) g r s S S := by
  unfold tensorH1Inner
  refine add_nonneg ?_ ?_
  · exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  · refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S x

/-- Additivity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorH1Inner (I := I) (M := M) g r s S₁ T +
        tensorH1Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
          tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (S₁ + S₂) T x) =
      (fun x : M => tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_add_left
      (I := I) (M := M) g r s S₁ S₂ T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_add
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₁ T)
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₂ T)]
  ring

/-- Homogeneity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorH1Inner (I := I) (M := M) g r s S T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
        c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (c • S) T x) =
      (fun x : M => c * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_smul_left
      (I := I) (M := M) g r s c S T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Compactly-supported smooth `(r, s)`-tensor section wrapped to carry the
`H^1` pre-Hilbert structure, a distinct Lean type from `SmoothCcTensor`. -/
structure SmoothCcTensorH1 (g : SmoothRiemannianMetric I M) (r s : ℕ) where
  /-- The underlying `L^2`-wrapped compactly-supported smooth section. -/
  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorH1

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

/-- Two `SmoothCcTensorH1` are equal iff their underlying sections are equal. -/
@[ext] theorem ext {S T : SmoothCcTensorH1 g r s}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

/-- `toCcTensor` is injective. -/
lemma toCcTensor_injective :
    Function.Injective (fun S : SmoothCcTensorH1 g r s => S.toCcTensor) := by
  intro S T h
  exact ext h

instance : Zero (SmoothCcTensorH1 g r s) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorH1 g r s) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorH1 g r s) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorH1 g r s).toCcTensor = 0 := rfl
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorH1 g r s) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorH1 g r s) :
    (-S).toCcTensor = -S.toCcTensor := rfl
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorH1 g r s) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorH1 g r s) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorH1 g r s) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorH1 g r s) := ⟨zsmulRec⟩

@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorH1 g r s) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorH1 g r s) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

/-- Additive monoid hom from `SmoothCcTensorH1 g r s` to the underlying
compactly-supported smooth section. -/
def toCcTensorAddHom : SmoothCcTensorH1 g r s →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorH1

set_option linter.unusedSectionVars false in
/-- The pre-inner-product core on `SmoothCcTensorH1 g r s`, whose inner product
is the `H^1` pairing `tensorH1Inner g r s` of the underlying smooth
compactly-supported sections. -/
noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorH1 g r s) where
  inner S T := tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
  conj_inner_symm S T := by
    change (tensorH1Inner (I := I) (M := M) g r s T.toCcTensor S.toCcTensor : ℝ) =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    exact tensorH1Inner_symm (I := I) (M := M) g r s T.toCcTensor S.toCcTensor
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
    exact tensorH1Inner_nonneg (I := I) (M := M) g r s S.toCcTensor
  add_left S₁ S₂ T := by
    change tensorH1Inner (I := I) (M := M) g r s
        (S₁ + S₂).toCcTensor T.toCcTensor =
      tensorH1Inner (I := I) (M := M) g r s S₁.toCcTensor T.toCcTensor +
        tensorH1Inner (I := I) (M := M) g r s S₂.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact tensorH1Inner_add_left (I := I) (M := M) g r s
      S₁.toCcTensor S₂.toCcTensor T.toCcTensor
  smul_left S T c := by
    change tensorH1Inner (I := I) (M := M) g r s
        (c • S).toCcTensor T.toCcTensor =
      c * tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact tensorH1Inner_smul_left (I := I) (M := M) g r s
      c S.toCcTensor T.toCcTensor

set_option linter.unusedSectionVars false in
/-- The seminormed structure on `SmoothCcTensorH1 g r s` derived from the
pre-inner-product core. -/
noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in
/-- The inner-product-space structure on `SmoothCcTensorH1 g r s` derived from
the pre-inner-product core. -/
noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.ofCore _

set_option linter.unusedSectionVars false in
/-- The `H^1` inner product on `SmoothCcTensorH1 g r s` unfolds to the
`tensorH1Inner` pairing of the underlying smooth compactly-supported
sections. -/
@[simp] theorem SmoothCcTensorH1.inner_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensorH1 g r s) :
    ⟪S, T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := rfl

set_option linter.unusedSectionVars false in
/-- The `H^1` seminorm on `SmoothCcTensorH1 g r s` is the square root of the
`tensorH1Inner` pairing of the underlying section with itself. -/
theorem SmoothCcTensorH1.norm_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ = Real.sqrt (tensorH1Inner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) := rfl

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
