import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The spectral `Hˢ` Sobolev scale of tensor sections

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a real
parameter `σ ≥ 0`, this file builds the **spectral Sobolev space** `Hˢ`
of mixed `(r, s)`-tensor fields: the subspace of `TensorL2 r s g`
consisting of tensors `T` whose eigenbasis coordinates
`cᵢ = ⟪bᵢ, T⟫` against the rough-Laplacian eigenbasis decay fast
enough that

  `∑ᵢ (1 + λᵢ)^σ · cᵢ² < ∞`,

where `{bᵢ}` is the eigenbasis `tensorResolventHilbertEigenbasisSigma`
and `λᵢ ≥ 0` the associated connection-Laplacian eigenvalues. The space
is equipped with the weighted inner product

  `⟪S, T⟫_{Hˢ} = ∑ᵢ (1 + λᵢ)^σ · ⟪bᵢ, S⟫ · ⟪bᵢ, T⟫`,

making it a real Hilbert space. For `σ = 0` the weight is `(1+λ)^0 = 1`
and `H⁰` is isometrically `TensorL2 r s g` itself.

## Design

`tensorHs g r s σ` is a one-field structure carrying the
coordinate family `coeff : TensorEigenIdx g r s → ℝ` together with the
weighted square-summability witness. A structure (rather than a subtype
of `TensorL2`) is used so the carrier is topology-free: this lets the
`Hˢ` Hilbert topology — strictly stronger than the `L²`-subspace
topology — be installed without a `UniformSpace` diamond.

The weighted inner product is supplied via an `InnerProductSpace.Core`,
which yields the `NormedAddCommGroup` and `InnerProductSpace ℝ`
instances. Completeness is obtained by transporting along the explicit
linear isometric equivalence `tensorHs … σ ≃ₗᵢ ℓ²(ι, ℝ)` given by the
diagonal rescaling `cᵢ ↦ √(1+λᵢ)^σ · cᵢ`.

## Main definitions

* `tensorHs g r s σ` — the spectral `Hˢ` Sobolev space, a
  real Hilbert space.
* `tensorHs.coeff` — the `i`-th eigenbasis coordinate of an element.
* `tensorHsToL2` — the inclusion `Hˢ →L[ℝ] TensorL2 r s g`.
* `tensorHsRescaleEquivL2` — the rescaling isometry
  `Hˢ ≃ₗᵢ[ℝ] ℓ²(ι, ℝ)`.
* `tensorHsZeroEquivL2` — the `σ = 0` identification
  `H⁰ ≃ₗᵢ[ℝ] TensorL2 r s g`.

## Main results

* weighted-Parseval: `‖T‖² = ∑ᵢ (1+λᵢ)^σ (coeff i T)²`;
* the weighted inner-product formula;
* `tensorHsToL2` is injective with operator norm `≤ 1` for
  `σ ≥ 0`, and its coordinates agree with those of the image in `TensorL2`;
* finitely-supported coordinate families give elements of every `Hˢ`.

## Sign convention

The eigenvalues `λᵢ ≥ 0` are the connection-Laplacian eigenvalues
attached to the resolvent eigenbasis (geometer convention
`Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`); the resolvent is `(1 - Δ_∇)⁻¹`.
The weight `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`, so `Hˢ ⊆ H⁰ = L²`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The spectral Sobolev weight at eigen-index `i` and exponent `σ`,
namely `(1 + λᵢ)^σ` with `λᵢ ≥ 0` the connection-Laplacian eigenvalue.
For `σ ≥ 0` the weight is `≥ 1`; for `σ = 0` it is `1`. -/
def tensorSobolevWeight {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) : ℝ :=
  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ

/-- The base `1 + λᵢ` of the Sobolev weight is `≥ 1`. -/
lemma one_le_one_add_lambda {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
  have h := tensor_lambda_nonneg (I := I) (M := M) i
  linarith

/-- The Sobolev weight `(1 + λᵢ)^σ` is positive. -/
lemma tensorSobolevWeight_pos {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    0 < tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  have h : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h) σ

/-- The Sobolev weight `(1 + λᵢ)^σ` is non-negative. -/
lemma tensorSobolevWeight_nonneg {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
  (tensorSobolevWeight_pos (I := I) (M := M) i σ).le

/-- For `σ ≥ 0` the Sobolev weight `(1 + λᵢ)^σ` is `≥ 1`. -/
lemma one_le_tensorSobolevWeight {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 ≤ tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) hσ

/-- At `σ = 0` the Sobolev weight is `1`. -/
@[simp] lemma tensorSobolevWeight_zero {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i (0 : ℝ) = 1 := by
  unfold tensorSobolevWeight
  exact Real.rpow_zero _

/-- The square root of the Sobolev weight, squared, is the weight. -/
lemma sq_sqrt_tensorSobolevWeight {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ :=
  Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)

/-- The `i`-th eigenbasis coordinate of an `L²` tensor field `T`, against
the chart-locality-free eigenbasis
`tensorResolventHilbertEigenbasisSigma h_compact`. Concretely
this is `(b.repr T) i`. No chart-selection hypothesis is required. -/
def tensorL2Coeff {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℝ :=
  (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact).repr T i

/-- The chart-locality-free eigenbasis coordinate equals the inner
product `⟪bᵢ, T⟫`. -/
lemma tensorL2Coeff_eq_inner {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact T i =
      ⟪tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_compact i, T⟫_ℝ := by
  unfold tensorL2Coeff
  exact HilbertBasis.repr_apply_apply _ T i

/-- The chart-locality-free eigenbasis-coordinate family of `T` is
square-summable. -/
lemma tensorL2Coeff_summable_sq {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (tensorL2Coeff (I := I) (M := M) h_compact T i) ^ 2) := by
  have h := tensorSummable_basis_coeff_sq
    (I := I) (M := M) h_compact T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_compact i, T⟫_ℝ‖ ^ 2) =
      (fun i => (tensorL2Coeff (I := I) (M := M) h_compact T i) ^ 2)
      := by
    funext i
    rw [tensorL2Coeff_eq_inner, Real.norm_eq_abs, sq_abs]
  rwa [h_eq] at h

/-- `tensorL2Coeff` is additive in its `L²` argument. -/
lemma tensorL2Coeff_add {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (S T : TensorL2 r s g) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact (S + T) i =
      tensorL2Coeff (I := I) (M := M) h_compact S i +
        tensorL2Coeff (I := I) (M := M) h_compact T i := by
  unfold tensorL2Coeff
  rw [map_add]
  rfl

/-- `tensorL2Coeff` is `ℝ`-homogeneous in its `L²` argument. -/
lemma tensorL2Coeff_smul {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (c : ℝ) (T : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact (c • T) i =
      c * tensorL2Coeff (I := I) (M := M) h_compact T i := by
  unfold tensorL2Coeff
  rw [map_smul]
  rfl

/-- The spectral `Hˢ` Sobolev space of mixed `(r, s)`-tensor fields, for
exponent `σ`.

An element is a coordinate family `coeff : TensorEigenIdx g r s → ℝ`
against the rough-Laplacian eigenbasis, together with a witness that the
weighted squares `(1 + λᵢ)^σ · (coeff i)²` are summable. For `σ ≥ 0`
this is exactly the subspace of `TensorL2 r s g` of tensors whose
eigenbasis expansion lies in the weighted `ℓ²`; see `tensorHsToL2`.

The structure is intentionally topology-free: the `Hˢ` Hilbert topology
is installed below via an `InnerProductSpace.Core`. -/
structure tensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) where
  /-- The eigenbasis-coordinate family. -/
  coeff : TensorEigenIdx (I := I) (M := M) g r s → ℝ
  /-- The weighted square-summability witness placing `coeff` in `Hˢ`. -/
  weighted_summable :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      (coeff i) ^ 2)

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

/-- Two `Hˢ` elements are equal once their coordinate families agree. -/
@[ext] lemma ext {S T : tensorHs (I := I) (M := M) g r s σ}
    (h : S.coeff = T.coeff) : S = T := by
  cases S; cases T; cases h; rfl

instance : Zero (tensorHs (I := I) (M := M) g r s σ) where
  zero := ⟨fun _ => 0, by simp⟩

@[simp] lemma zero_coeff :
    (0 : tensorHs (I := I) (M := M) g r s σ).coeff =
      (fun _ => 0) := rfl

instance : Add (tensorHs (I := I) (M := M) g r s σ) where
  add S T :=
    { coeff := fun i => S.coeff i + T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
              2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
            tensorSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
            tensorSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i + T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i - T.coeff i)]
          calc
            tensorSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i + T.coeff i) ^ 2
                ≤ tensorSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

@[simp] lemma add_coeff
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    (S + T).coeff = (fun i => S.coeff i + T.coeff i) := rfl

instance : Neg (tensorHs (I := I) (M := M) g r s σ) where
  neg S :=
    { coeff := fun i => -S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
              tensorSobolevWeight (I := I) (M := M) i σ *
                (-S.coeff i) ^ 2) =
            (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2) := by
          funext i; ring
        rwa [h_eq] }

@[simp] lemma neg_coeff (S : tensorHs (I := I) (M := M) g r s σ) :
    (-S).coeff = (fun i => -S.coeff i) := rfl

instance : SMul ℝ (tensorHs (I := I) (M := M) g r s σ) where
  smul c S :=
    { coeff := fun i => c * S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
              tensorSobolevWeight (I := I) (M := M) i σ *
                (c * S.coeff i) ^ 2) =
            (fun i => c ^ 2 * (tensorSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2)) := by
          funext i; ring
        rw [h_eq]
        exact hS.mul_left _ }

@[simp] lemma smul_coeff (c : ℝ)
    (S : tensorHs (I := I) (M := M) g r s σ) :
    (c • S).coeff = (fun i => c * S.coeff i) := rfl

instance : AddCommGroup (tensorHs (I := I) (M := M) g r s σ) where
  add_assoc S T U := by ext i; simp [add_assoc]
  zero_add S := by ext i; simp
  add_zero S := by ext i; simp
  add_comm S T := by ext i; simp [add_comm]
  neg_add_cancel S := by ext i; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (tensorHs (I := I) (M := M) g r s σ) where
  one_smul S := by ext i; simp
  mul_smul a b S := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c S T := by ext i; simp [mul_add]
  add_smul a b S := by ext i; simp [add_mul]
  zero_smul S := by ext i; simp

/-- The weighted product family `i ↦ (1+λᵢ)^σ · (coeff i S) · (coeff i T)`
is summable: it is dominated by the AM–GM bound coming from the two
weighted-square-summable families. -/
lemma weightedProd_summable
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i)) := by
  have hS := S.weighted_summable
  have hT := T.weighted_summable
  have h_dom : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2)) :=
    (hS.mul_left _).add (hT.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have h_amgm :
      |tensorSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i)| ≤
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw]
    have h_prod : |S.coeff i * T.coeff i| ≤
        (1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|S.coeff i| - |T.coeff i|),
        abs_nonneg (S.coeff i), abs_nonneg (T.coeff i),
        sq_abs (S.coeff i), sq_abs (T.coeff i)]
    calc
      tensorSobolevWeight (I := I) (M := M) i σ *
            |S.coeff i * T.coeff i|
          ≤ tensorSobolevWeight (I := I) (M := M) i σ *
            ((1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_left h_prod hw
      _ = (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
              (S.coeff i) ^ 2) +
            (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i σ *
              (T.coeff i) ^ 2) := by ring
  simpa using h_amgm

/-- The weighted `Hˢ` inner-product value, as a bare function:
`⟪S, T⟫ = ∑ᵢ (1 + λᵢ)^σ · (coeff i S) · (coeff i T)`. -/
def innerFun (S T : tensorHs (I := I) (M := M) g r s σ) : ℝ :=
  ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
    (S.coeff i * T.coeff i)

/-- `innerFun T T` is the weighted sum of squares
`∑ᵢ (1 + λᵢ)^σ (coeff i T)²`. -/
lemma innerFun_self (T : tensorHs (I := I) (M := M) g r s σ) :
    innerFun (I := I) (M := M) T T =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  unfold innerFun
  refine tsum_congr (fun i => ?_)
  rw [sq]

/-- The pre-inner-product `Core` underlying the weighted `Hˢ` inner
product: symmetry, positive-definiteness, additivity and homogeneity in
the first slot are all immediate from the corresponding `tsum`
identities. -/
@[reducible] def innerCore :
    InnerProductSpace.Core ℝ
      (tensorHs (I := I) (M := M) g r s σ) where
  inner S T := innerFun (I := I) (M := M) S T
  conj_inner_symm S T := by
    simp only [conj_trivial]
    unfold innerFun
    refine tsum_congr (fun i => ?_)
    ring
  re_inner_nonneg T := by
    simp only [RCLike.re_to_real]
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T]
    refine tsum_nonneg (fun i => ?_)
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    positivity
  add_left S T U := by
    change innerFun (I := I) (M := M) (S + T) U =
      innerFun (I := I) (M := M) S U + innerFun (I := I) (M := M) T U
    unfold innerFun
    rw [← Summable.tsum_add
      (weightedProd_summable (I := I) (M := M) S U)
      (weightedProd_summable (I := I) (M := M) T U)]
    refine tsum_congr (fun i => ?_)
    simp only [add_coeff]
    ring
  smul_left S T c := by
    simp only [conj_trivial]
    change innerFun (I := I) (M := M) (c • S) T =
      c * innerFun (I := I) (M := M) S T
    unfold innerFun
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    simp only [smul_coeff]
    ring
  definite T hT := by
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T] at hT
    have h_nonneg : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        0 ≤ tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
      intro i
      have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ
      positivity
    have h_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 = 0 := by
      intro i
      have h_le := Summable.le_tsum T.weighted_summable i
        (fun j _ => h_nonneg j)
      rw [hT] at h_le
      exact le_antisymm h_le (h_nonneg i)
    ext i
    have hwi : tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2
        = 0 := h_zero i
    have hw_ne : tensorSobolevWeight (I := I) (M := M) i σ ≠ 0 :=
      (tensorSobolevWeight_pos (I := I) (M := M) i σ).ne'
    have h_sq : (T.coeff i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hwi with h | h
      · exact absurd h hw_ne
      · exact h
    have : T.coeff i = 0 := by nlinarith [h_sq]
    simpa using this

/-- The `NormedAddCommGroup` instance on `Hˢ` induced by the weighted
inner product. -/
instance instNormedAddCommGroup :
    NormedAddCommGroup (tensorHs (I := I) (M := M) g r s σ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := innerCore (I := I) (M := M) (g := g) (r := r) (s := s)
      (σ := σ))

/-- The `InnerProductSpace ℝ` instance on `Hˢ`. -/
instance instInnerProductSpace :
    InnerProductSpace ℝ (tensorHs (I := I) (M := M) g r s σ) :=
  InnerProductSpace.ofCore
    (innerCore (I := I) (M := M) (g := g) (r := r) (s := s)
      (σ := σ)).1

/-- The `Hˢ` inner product is the weighted `tsum`
`∑ᵢ (1 + λᵢ)^σ · (coeff i S) · (coeff i T)`. -/
lemma inner_def (S T : tensorHs (I := I) (M := M) g r s σ) :
    (inner ℝ S T : ℝ) =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i) := rfl

/-- The `Hˢ` inner product of `T` with itself is the weighted sum of
squares `∑ᵢ (1+λᵢ)^σ (coeff i T)²`. -/
lemma inner_self_eq (T : tensorHs (I := I) (M := M) g r s σ) :
    (inner ℝ T T : ℝ) =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
  innerFun_self (I := I) (M := M) T

/-- The squared `Hˢ` norm equals the weighted sum of squared
coordinates: `‖T‖² = ∑ᵢ (1 + λᵢ)^σ · (coeff i T)²`. -/
theorem norm_sq_eq_tsum
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_self_eq]

/-- The `Hˢ` norm is the square root of the weighted sum of squared
coordinates. -/
theorem norm_eq_sqrt_tsum
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖T‖ =
      Real.sqrt (∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2) := by
  rw [← norm_sq_eq_tsum]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

end tensorHs

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

/-- The rescaled coordinate family `i ↦ √(1+λᵢ)^σ · coeff i` of an `Hˢ`
element is square-summable, hence a member of `ℓ²(ι, ℝ)`. -/
lemma rescale_memℓp (T : tensorHs (I := I) (M := M) g r s σ) :
    Memℓp (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) 2 := by
  apply memℓp_gen
  have h_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ‖Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    have hpr : ‖Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℝ≥0∞).toReal =
        ‖Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℕ) := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hsq : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_tensorSobolevWeight (I := I) (M := M) i σ
    rw [hpr, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
  rw [h_eq]
  exact T.weighted_summable

/-- The forward rescaling map `Hˢ → ℓ²(ι, ℝ)`,
`T ↦ (i ↦ √(1+λᵢ)^σ · coeff i)`. -/
def rescaleToL2 (T : tensorHs (I := I) (M := M) g r s σ) :
    lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 :=
  ⟨fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
      T.coeff i, rescale_memℓp (I := I) (M := M) T⟩

@[simp] lemma rescaleToL2_apply
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (rescaleToL2 (I := I) (M := M) T : _ → ℝ) i =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i := rfl

/-- Any `ℓ²(ι, ℝ)` family, divided by `√(1+λᵢ)^σ`, satisfies the
weighted square-summability defining `Hˢ`. -/
lemma rescaleFromL2_weighted_summable
    (f : lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ *
          (f : _ → ℝ) i) ^ 2) := by
  have hf : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ((f : _ → ℝ) i) ^ 2) := by
    have hmem := lp.memℓp f
    have h := hmem.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖(f : _ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ((f : _ → ℝ) i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rwa [h_eq] at h
  have h_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ *
            (f : _ → ℝ) i) ^ 2) =
      (fun i => ((f : _ → ℝ) i) ^ 2) := by
    funext i
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_pos (I := I) (M := M) i σ
    have hsq : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_tensorSobolevWeight (I := I) (M := M) i σ
    rw [mul_pow, inv_pow, hsq]
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [h_eq]
  exact hf

/-- The inverse rescaling map `ℓ²(ι, ℝ) → Hˢ`,
`f ↦ (i ↦ √(1+λᵢ)^σ ⁻¹ · f i)`. -/
def rescaleFromL2
    (f : lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2) :
    tensorHs (I := I) (M := M) g r s σ where
  coeff i := (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ *
    (f : _ → ℝ) i
  weighted_summable := rescaleFromL2_weighted_summable (I := I) (M := M) f

@[simp] lemma rescaleFromL2_coeff
    (f : lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (rescaleFromL2 (I := I) (M := M) (σ := σ)
        f).coeff i =
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ *
        (f : _ → ℝ) i := rfl

/-- The rescaling map `Hˢ → ℓ²(ι, ℝ)` packaged as a linear isometric
equivalence. The forward map is the diagonal rescaling
`cᵢ ↦ √(1+λᵢ)^σ · cᵢ`; norm preservation is the weighted-norm
identity. -/
def rescaleEquivL2 :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 where
  toFun := rescaleToL2 (I := I) (M := M)
  invFun := rescaleFromL2 (I := I) (M := M)
  map_add' S T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_add, Pi.add_apply, add_coeff]
    ring
  map_smul' c T := by
    apply lp.ext
    funext i
    simp only [rescaleToL2, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
      smul_eq_mul, RingHom.id_apply]
    ring
  left_inv T := by
    ext i
    simp only [rescaleFromL2_coeff, rescaleToL2_apply]
    have hsqrt_pos :
        0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_pos.ne', one_mul]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [rescaleToL2_apply, rescaleFromL2_coeff]
    have hsqrt_pos :
        0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  norm_map' T := by
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_lp_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 =
          ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2 := by
      have h := lp.norm_rpow_eq_tsum
        (p := 2)
        (E := fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (by norm_num) (rescaleToL2 (I := I) (M := M) T)
      rw [hpr] at h
      have h_lhs : ‖rescaleToL2 (I := I) (M := M) T‖ ^ (2 : ℝ) =
          ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 := by norm_cast
      rw [h_lhs] at h
      rw [h]
      refine tsum_congr (fun i => ?_)
      have hsq :
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) ^ 2 =
            tensorSobolevWeight (I := I) (M := M) i σ :=
        sq_sqrt_tensorSobolevWeight (I := I) (M := M) i σ
      have hcast :
          ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℝ) =
            ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast, rescaleToL2_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
    have h_norm_sq : ‖T‖ ^ 2 =
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
      norm_sq_eq_tsum (I := I) (M := M) T
    have h_eq_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 = ‖T‖ ^ 2 := by
      rw [h_lp_sq, h_norm_sq]
    have h1 : 0 ≤ ‖rescaleToL2 (I := I) (M := M) T‖ := norm_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have := congrArg Real.sqrt h_eq_sq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

@[simp] lemma rescaleEquivL2_apply
    (T : tensorHs (I := I) (M := M) g r s σ) :
    (rescaleEquivL2 (I := I) (M := M)
      (σ := σ) T : _ → ℝ) =
      (fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) := rfl

instance instCompleteSpace :
    CompleteSpace (tensorHs (I := I) (M := M) g r s σ) :=
  (rescaleEquivL2 (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (σ := σ)).toIsometryEquiv.completeSpace

end tensorHs

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

/-- For `σ ≥ 0`, the (unweighted) coordinate family of an `Hˢ` element
is square-summable. -/
lemma coeff_summable_sq_of_nonneg (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_
    T.weighted_summable
  intro i
  have hw : 1 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    one_le_tensorSobolevWeight (I := I) (M := M) i hσ
  have hsq : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
  nlinarith [hw, hsq]

/-- For `σ ≥ 0`, the coordinate family of an `Hˢ` element, viewed in
`ℓ²(ι, ℝ)`. -/
def toL2Seq (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    lp (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ) 2 :=
  ⟨T.coeff, by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]
    exact coeff_summable_sq_of_nonneg (I := I) (M := M) hσ T⟩

@[simp] lemma toL2Seq_apply (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (toL2Seq (I := I) (M := M) hσ T : _ → ℝ) i = T.coeff i := rfl

/-- `toL2Seq` is additive. -/
lemma toL2Seq_add (hσ : 0 ≤ σ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    toL2Seq (I := I) (M := M) hσ (S + T) =
      toL2Seq (I := I) (M := M) hσ S + toL2Seq (I := I) (M := M) hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_add, Pi.add_apply, add_coeff]

/-- `toL2Seq` is `ℝ`-homogeneous. -/
lemma toL2Seq_smul (hσ : 0 ≤ σ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    toL2Seq (I := I) (M := M) hσ (c • T) =
      c • toL2Seq (I := I) (M := M) hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
    smul_eq_mul]

/-- The underlying function of the chart-locality-free inclusion
`Hˢ → TensorL2`: it sends an `Hˢ` element to the `L²` tensor with the
same eigenbasis coordinate family, reconstructed via the inverse of the
`_ofCompact` Hilbert-basis representation. -/
def toL2Fun_ofCompact
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    TensorL2 r s g :=
  (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact).repr.symm
    (toL2Seq (I := I) (M := M) hσ T)

/-- The chart-locality-free `L²` eigenbasis coordinate of `toL2Fun_ofCompact T`
is the `Hˢ` coordinate of `T`. -/
@[simp] lemma tensorL2Coeff_ofCompact_toL2Fun_ofCompact
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T) i = T.coeff i := by
  unfold tensorL2Coeff toL2Fun_ofCompact
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- `toL2Fun_ofCompact` is additive. -/
lemma toL2Fun_ofCompact_add
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hσ : 0 ≤ σ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    toL2Fun_ofCompact (I := I) (M := M) h_compact hσ (S + T) =
      toL2Fun_ofCompact (I := I) (M := M) h_compact hσ S +
        toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T := by
  unfold toL2Fun_ofCompact
  rw [toL2Seq_add (I := I) (M := M) hσ S T, map_add]

/-- `toL2Fun_ofCompact` is `ℝ`-homogeneous. -/
lemma toL2Fun_ofCompact_smul
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hσ : 0 ≤ σ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    toL2Fun_ofCompact (I := I) (M := M) h_compact hσ (c • T) =
      c • toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T := by
  unfold toL2Fun_ofCompact
  rw [toL2Seq_smul (I := I) (M := M) hσ c T, map_smul]

/-- For `σ ≥ 0`, the `L²` norm of `toL2Fun_ofCompact T` is bounded by the
`Hˢ` norm of `T`: the chart-locality-free inclusion is norm-non-increasing. -/
lemma norm_toL2Fun_ofCompact_le
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hσ : 0 ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T‖ ≤ ‖T‖ := by
  have h_l2_sq : ‖toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T‖ ^ 2 =
      ∑' i, (T.coeff i) ^ 2 := by
    have h_par := tensorParseval_norm_sq (I := I) (M := M) h_compact
      (toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T)
    have h_eq :
        (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
          ‖⟪tensorResolventHilbertEigenbasisSigma
              (I := I) (M := M) h_compact i,
            toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T⟫_ℝ‖ ^ 2) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      rw [← tensorL2Coeff_eq_inner,
        tensorL2Coeff_ofCompact_toL2Fun_ofCompact,
        Real.norm_eq_abs, sq_abs]
    rwa [h_eq] at h_par
  have h_hs_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_summ_unweighted :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (T.coeff i) ^ 2) :=
    coeff_summable_sq_of_nonneg (I := I) (M := M) hσ T
  have h_le_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (T.coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    have hw : 1 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      one_le_tensorSobolevWeight (I := I) (M := M) i hσ
    nlinarith [hw, sq_nonneg (T.coeff i)]
  have h_tsum_le :
      ∑' i, (T.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms h_summ_unweighted T.weighted_summable
  have h_sq_le :
      ‖toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_l2_sq, h_hs_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T‖ :=
    norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end tensorHs

/-- For `σ ≥ 0`, the chart-locality-free inclusion of the spectral
Sobolev space `Hˢ` into `TensorL2 r s g`, as a continuous linear map.
Operator norm `≤ 1`, injective. No chart-selection hypothesis. -/
def tensorHsToL2 {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      TensorL2 r s g :=
  LinearMap.mkContinuous
    { toFun := tensorHs.toL2Fun_ofCompact (I := I) (M := M) h_compact hσ
      map_add' := tensorHs.toL2Fun_ofCompact_add (I := I) (M := M) h_compact hσ
      map_smul' := fun c T =>
        tensorHs.toL2Fun_ofCompact_smul (I := I) (M := M) h_compact hσ c T }
    1
    (fun T => by
      change ‖tensorHs.toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T‖
          ≤ 1 * ‖T‖
      rw [one_mul]
      exact tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M) h_compact hσ T)

/-- `tensorHsToL2` applied to `T` is the underlying
`toL2Fun_ofCompact T`. -/
@[simp] lemma tensorHsToL2_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)} {σ : ℝ}
    (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        h_compact hσ T =
      tensorHs.toL2Fun_ofCompact (I := I) (M := M) h_compact hσ T := rfl

/-- The operator norm of the chart-locality-free inclusion
`Hˢ →L[ℝ] TensorL2` is at most `1` for `σ ≥ 0`. -/
theorem tensorHsToL2_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)} {σ : ℝ}
    (hσ : 0 ≤ σ) :
    ‖tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        h_compact hσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The chart-locality-free `L²` eigenbasis coordinate of the image of
`T` under the inclusion equals the `Hˢ` coordinate of `T`. -/
@[simp] theorem tensorHsToL2_tensorL2Coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)} {σ : ℝ}
    (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ T) i = T.coeff i := by
  rw [tensorHsToL2_apply]
  exact tensorHs.tensorL2Coeff_ofCompact_toL2Fun_ofCompact
    (I := I) (M := M) h_compact hσ T i

/-- The chart-locality-free inclusion `Hˢ →L[ℝ] TensorL2` is injective for
`σ ≥ 0`. -/
theorem tensorHsToL2_injective {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)} {σ : ℝ}
    (hσ : 0 ≤ σ) :
    Function.Injective
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        h_compact hσ) := by
  intro S T hST
  ext i
  have hS := tensorHsToL2_tensorL2Coeff
    (I := I) (M := M) (h_compact := h_compact) hσ S i
  have hT := tensorHsToL2_tensorL2Coeff
    (I := I) (M := M) (h_compact := h_compact) hσ T i
  rw [← hS, ← hT, hST]

/-- The spectral `H⁰` Sobolev space is isometrically isomorphic to the
`L²` Hilbert space `TensorL2 r s g`, via the chart-locality-free
eigenbasis. No chart-selection hypothesis is required. -/
def tensorHsZeroEquivL2 {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    tensorHs (I := I) (M := M) g r s 0 ≃ₗᵢ[ℝ]
      TensorL2 r s g :=
  (tensorHs.rescaleEquivL2 (I := I) (M := M)
    (g := g) (r := r) (s := s) (σ := 0)).trans
    (tensorResolventHilbertEigenbasisSigma
      (I := I) (M := M) h_compact).repr.symm

/-- The chart-locality-free `H⁰`-to-`L²` identification sends `T` to the
`L²` tensor with the same eigenbasis coordinates. -/
theorem tensorHsZeroEquivL2_tensorL2Coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : tensorHs (I := I) (M := M) g r s 0)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsZeroEquivL2 (I := I) (M := M) h_compact T) i =
      T.coeff i := by
  unfold tensorHsZeroEquivL2 tensorL2Coeff
  rw [LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (tensorHs.rescaleEquivL2 (I := I) (M := M) T : _ → ℝ) i = T.coeff i
  rw [tensorHs.rescaleEquivL2_apply]
  simp only [tensorSobolevWeight_zero, Real.sqrt_one, one_mul]

/-- The chart-locality-free `H⁰`-to-`L²` identification, read backwards:
the `L²` tensor `U` becomes the `H⁰` element whose coordinate family is
`U`'s eigenbasis coordinate family. -/
theorem tensorHsZeroEquivL2_symm_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (U : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ((tensorHsZeroEquivL2 (I := I) (M := M) h_compact).symm U).coeff i =
      tensorL2Coeff (I := I) (M := M) h_compact U i := by
  have h := tensorHsZeroEquivL2_tensorL2Coeff
    (I := I) (M := M) h_compact
    ((tensorHsZeroEquivL2 (I := I) (M := M) h_compact).symm U) i
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- A finitely-supported coordinate family `f` defines an element of
`Hˢ` for every exponent `σ`. -/
def tensorHsOfFiniteSupport {g : SmoothRiemannianMetric I M} {r s : ℕ} (σ : ℝ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (hf : (Function.support f).Finite) :
    tensorHs (I := I) (M := M) g r s σ where
  coeff := f
  weighted_summable := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset hf
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro hfi
    apply hi
    rw [hfi]
    ring

@[simp] lemma tensorHsOfFiniteSupport_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (σ : ℝ)
    (f : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (hf : (Function.support f).Finite) :
    (tensorHsOfFiniteSupport (I := I) (M := M) σ f hf).coeff =
      f := rfl

open scoped Classical in
/-- The standard basis coordinate family `i ↦ if i = j then 1 else 0`
defines an element of every `Hˢ` — the spectral representation of the
`j`-th eigenvector `b j`. -/
def tensorHsBasisVec {g : SmoothRiemannianMetric I M} {r s : ℕ} (σ : ℝ)
    (j : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHs (I := I) (M := M) g r s σ :=
  tensorHsOfFiniteSupport (I := I) (M := M) σ
    (fun i => if i = j then (1 : ℝ) else 0)
    (by
      apply Set.Finite.subset (Set.finite_singleton j)
      intro i hi
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hi
      simpa using hi)

open scoped Classical in
@[simp] lemma tensorHsBasisVec_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (σ : ℝ)
    (j i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j).coeff i =
      (if i = j then (1 : ℝ) else 0) := rfl

/-- For `σ ≥ 0`, the chart-locality-free inclusion `Hˢ → TensorL2` carries
the spectral basis vector `tensorHsBasisVec σ j` to the actual
`_ofCompact` eigenbasis vector `b j`. -/
theorem tensorHsToL2_tensorHsBasisVec {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)} {σ : ℝ}
    (hσ : 0 ≤ σ) (j : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        h_compact hσ
        (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j) =
      tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_compact j := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hb
  apply b.repr.injective
  ext i
  have h_lhs : (b.repr (tensorHsToL2
        (I := I) (M := M) (g := g) (r := r) (s := s) h_compact hσ
        (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j))) i =
      (if i = j then (1 : ℝ) else 0) := by
    have h_coeff : tensorL2Coeff (I := I) (M := M) h_compact
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ
          (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j)) i =
        (if i = j then (1 : ℝ) else 0) := by
      rw [tensorHsToL2_tensorL2Coeff, tensorHsBasisVec_coeff]
    rw [← h_coeff]
    rfl
  have h_rhs : (b.repr (b j)) i = (if i = j then (1 : ℝ) else 0) := by
    rw [b.repr_self, lp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [h_lhs, h_rhs]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    Type _ :=
  tensorHs (I := I) (M := M) g r s σ

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    NormedAddCommGroup (tensorHs (I := I) (M := M) g r s σ) :=
  inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    InnerProductSpace ℝ
      (tensorHs (I := I) (M := M) g r s σ) :=
  inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    CompleteSpace (tensorHs (I := I) (M := M) g r s σ) :=
  inferInstance

/-- Chart-locality-free coordinate functional access (no `h_atlas`). -/
example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorL2Coeff (I := I) (M := M) h_compact T i

/-- Chart-locality-free inclusion access (no `h_atlas`). -/
example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      TensorL2 r s g :=
  tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
    h_compact hσ

/-- Chart-locality-free `σ = 0` identification access (no `h_atlas`). -/
example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    tensorHs (I := I) (M := M) g r s 0 ≃ₗᵢ[ℝ]
      TensorL2 r s g :=
  tensorHsZeroEquivL2 (I := I) (M := M) h_compact

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
