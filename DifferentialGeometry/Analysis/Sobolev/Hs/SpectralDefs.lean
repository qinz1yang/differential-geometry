import DifferentialGeometry.Analysis.Laplacian.Spectral.EigenIdx
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The spectral `Hˢ` Sobolev scale of scalar fields

For a closed Riemannian manifold `(M, g)` and a real parameter `σ`,
this file builds the **spectral Sobolev space** `Hˢ` of scalar
functions: the subspace of `L² := Lp ℝ 2 (riemannianVolumeMeasure g)`
consisting of functions `u` whose eigenbasis coordinates
`cᵢ = ⟪bᵢ, u⟫` against the scalar resolvent eigenbasis decay fast
enough that

  `∑ᵢ (1 + λᵢ)^σ · cᵢ² < ∞`,

where `{bᵢ}` is the eigenbasis `resolventHilbertEigenbasisSigma` and
`λᵢ ≥ 0` the associated Laplacian eigenvalues. The space is equipped
with the weighted inner product

  `⟪S, T⟫_{Hˢ} = ∑ᵢ (1 + λᵢ)^σ · ⟪bᵢ, S⟫ · ⟪bᵢ, T⟫`,

making it a real Hilbert space. For `σ = 0` the weight is `(1+λ)^0 = 1`
and `H⁰` is isometrically `L²` itself.

## Design

`scalarHs g σ` is a one-field structure carrying the coordinate family
`coeff : EigenIdx g → ℝ` together with the weighted square-summability
witness. A structure (rather than a subtype of `L²`) is used so the
carrier is topology-free: this lets the `Hˢ` Hilbert topology — strictly
stronger than the `L²`-subspace topology — be installed without a
`UniformSpace` diamond.

The weighted inner product is supplied via an `InnerProductSpace.Core`,
which yields the `NormedAddCommGroup` and `InnerProductSpace ℝ`
instances. Completeness is obtained by transporting along the explicit
linear isometric equivalence `scalarHs g σ ≃ₗᵢ ℓ²(EigenIdx g, ℝ)` given
by the diagonal rescaling `cᵢ ↦ √(1+λᵢ)^σ · cᵢ`.

## Main definitions

* `scalarHs g σ` — the spectral `Hˢ` Sobolev space, a real Hilbert
  space.
* `scalarHs.coeff` — the `i`-th eigenbasis coordinate of an element.
* `scalarL2Coeff u i` — the `i`-th eigenbasis coordinate of an `L²`
  function `u`.
* `scalarHs.rescaleEquivL2` — the rescaling isometry
  `Hˢ ≃ₗᵢ[ℝ] ℓ²(EigenIdx g, ℝ)`.

## Sign convention

The eigenvalues `λᵢ ≥ 0` are the Laplacian eigenvalues attached to the
resolvent eigenbasis (geometer convention `Δ_g = div_g ∘ grad_g`,
spectrum `⊆ (-∞, 0]`); the resolvent is `(1 - Δ_g)⁻¹`. The weight
`(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`, so `Hˢ ⊆ H⁰ = L²`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The Sobolev weight `(1 + λᵢ)^σ` -/

/-- The spectral Sobolev weight at eigen-index `i` and exponent `σ`,
namely `(1 + λᵢ)^σ` with `λᵢ ≥ 0` the Laplacian eigenvalue. For
`σ ≥ 0` the weight is `≥ 1`; for `σ = 0` it is `1`. -/
def scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) : ℝ :=
  (1 + EigenIdx.lambda (I := I) (M := M) i) ^ σ

/-- The base `1 + λᵢ` of the Sobolev weight is `≥ 1`. -/
lemma one_le_one_add_lambda {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i := by
  have h := EigenIdx.lambda_nonneg (I := I) (M := M) i
  linarith

/-- The Sobolev weight `(1 + λᵢ)^σ` is positive. -/
lemma scalarSobolevWeight_pos {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 < scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  have h : (1 : ℝ) ≤ 1 + EigenIdx.lambda (I := I) (M := M) i :=
    one_le_one_add_lambda (I := I) (M := M) i
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h) σ

/-- The Sobolev weight `(1 + λᵢ)^σ` is non-negative. -/
lemma scalarSobolevWeight_nonneg {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
  (scalarSobolevWeight_pos (I := I) (M := M) i σ).le

/-- For `σ ≥ 0` the Sobolev weight `(1 + λᵢ)^σ` is `≥ 1`. -/
lemma one_le_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {σ : ℝ} (hσ : 0 ≤ σ) :
    1 ≤ scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) hσ

/-- At `σ = 0` the Sobolev weight is `1`. -/
@[simp] lemma scalarSobolevWeight_zero {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    scalarSobolevWeight (I := I) (M := M) i (0 : ℝ) = 1 := by
  unfold scalarSobolevWeight
  exact Real.rpow_zero _

/-- The square root of the Sobolev weight, squared, is the weight. -/
lemma sq_sqrt_scalarSobolevWeight {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (σ : ℝ) :
    Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
      scalarSobolevWeight (I := I) (M := M) i σ :=
  Real.sq_sqrt (scalarSobolevWeight_nonneg (I := I) (M := M) i σ)

/-! ## The eigenbasis-coordinate functional on `L²` -/

/-- The `i`-th eigenbasis coordinate of an `L²` scalar field `u`, i.e.
`⟪bᵢ, u⟫` for the eigenbasis `b = resolventHilbertEigenbasisSigma`.
Concretely this is `(b.repr u) i`. -/
def scalarL2Coeff {g : SmoothRiemannianMetric I M}
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  (resolventHilbertEigenbasisSigma (I := I) (M := M) g).repr u i

/-! ## The spectral `Hˢ` Sobolev space carrier -/

/-- The spectral `Hˢ` Sobolev space of scalar fields, for exponent `σ`.

An element is a coordinate family `coeff : EigenIdx g → ℝ` against the
resolvent eigenbasis, together with a witness that the weighted squares
`(1 + λᵢ)^σ · (coeff i)²` are summable. For `σ ≥ 0` this is exactly the
subspace of `L²` of functions whose eigenbasis expansion lies in the
weighted `ℓ²`.

The structure is intentionally topology-free: the `Hˢ` Hilbert topology
is installed below via an `InnerProductSpace.Core`. -/
structure scalarHs (g : SmoothRiemannianMetric I M) (σ : ℝ) where
  /-- The eigenbasis-coordinate family. -/
  coeff : EigenIdx (I := I) (M := M) g → ℝ
  /-- The weighted square-summability witness placing `coeff` in `Hˢ`. -/
  weighted_summable :
    Summable (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
      (coeff i) ^ 2)

namespace scalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

/-- Two `Hˢ` elements are equal once their coordinate families agree. -/
@[ext] lemma ext {S T : scalarHs (I := I) (M := M) g σ}
    (h : S.coeff = T.coeff) : S = T := by
  cases S; cases T; cases h; rfl

/-! ### Additive-group and module structure -/

instance : Zero (scalarHs (I := I) (M := M) g σ) where
  zero := ⟨fun _ => 0, by simp⟩

@[simp] lemma zero_coeff :
    (0 : scalarHs (I := I) (M := M) g σ).coeff =
      (fun _ => 0) := rfl

instance : Add (scalarHs (I := I) (M := M) g σ) where
  add S T :=
    { coeff := fun i => S.coeff i + T.coeff i
      weighted_summable := by
        -- `(a+b)² ≤ 2a² + 2b²`, so the weighted family is dominated by
        -- a summable family.
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i + T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i - T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i + T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

@[simp] lemma add_coeff
    (S T : scalarHs (I := I) (M := M) g σ) :
    (S + T).coeff = (fun i => S.coeff i + T.coeff i) := rfl

instance : Neg (scalarHs (I := I) (M := M) g σ) where
  neg S :=
    { coeff := fun i => -S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (-S.coeff i) ^ 2) =
            (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2) := by
          funext i; ring
        rwa [h_eq] }

@[simp] lemma neg_coeff (S : scalarHs (I := I) (M := M) g σ) :
    (-S).coeff = (fun i => -S.coeff i) := rfl

instance : Sub (scalarHs (I := I) (M := M) g σ) where
  sub S T :=
    { coeff := fun i => S.coeff i - T.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have hT := T.weighted_summable
        have h_dom : Summable
            (fun i : EigenIdx (I := I) (M := M) g =>
              2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i) ^ 2) +
                2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                  (T.coeff i) ^ 2)) :=
          (hS.mul_left 2).add (hT.mul_left 2)
        refine Summable.of_nonneg_of_le ?_ ?_ h_dom
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          positivity
        · intro i
          have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
            scalarSobolevWeight_nonneg (I := I) (M := M) i σ
          have h_sq : (S.coeff i - T.coeff i) ^ 2 ≤
              2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2 := by
            nlinarith [sq_nonneg (S.coeff i + T.coeff i)]
          calc
            scalarSobolevWeight (I := I) (M := M) i σ *
                  (S.coeff i - T.coeff i) ^ 2
                ≤ scalarSobolevWeight (I := I) (M := M) i σ *
                  (2 * (S.coeff i) ^ 2 + 2 * (T.coeff i) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_sq hw
            _ = 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (S.coeff i) ^ 2) +
                  2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                    (T.coeff i) ^ 2) := by ring }

@[simp] lemma sub_coeff
    (S T : scalarHs (I := I) (M := M) g σ) :
    (S - T).coeff = (fun i => S.coeff i - T.coeff i) := rfl

instance : SMul ℝ (scalarHs (I := I) (M := M) g σ) where
  smul c S :=
    { coeff := fun i => c * S.coeff i
      weighted_summable := by
        have hS := S.weighted_summable
        have h_eq :
            (fun i : EigenIdx (I := I) (M := M) g =>
              scalarSobolevWeight (I := I) (M := M) i σ *
                (c * S.coeff i) ^ 2) =
            (fun i => c ^ 2 * (scalarSobolevWeight (I := I) (M := M) i σ *
                (S.coeff i) ^ 2)) := by
          funext i; ring
        rw [h_eq]
        exact hS.mul_left _ }

@[simp] lemma smul_coeff (c : ℝ)
    (S : scalarHs (I := I) (M := M) g σ) :
    (c • S).coeff = (fun i => c * S.coeff i) := rfl

instance : AddCommGroup (scalarHs (I := I) (M := M) g σ) where
  add_assoc S T U := by ext i; simp [add_assoc]
  zero_add S := by ext i; simp
  add_zero S := by ext i; simp
  add_comm S T := by ext i; simp [add_comm]
  neg_add_cancel S := by ext i; simp
  sub_eq_add_neg S T := by ext i; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℝ (scalarHs (I := I) (M := M) g σ) where
  one_smul S := by ext i; simp
  mul_smul a b S := by ext i; simp [mul_assoc]
  smul_zero c := by ext i; simp
  smul_add c S T := by ext i; simp [mul_add]
  add_smul a b S := by ext i; simp [add_mul]
  zero_smul S := by ext i; simp

/-! ### The weighted inner product

`⟪S, T⟫_{Hˢ} = ∑ᵢ (1 + λᵢ)^σ · (coeff i S) · (coeff i T)`. The series
is absolutely convergent by Cauchy–Schwarz on the weighted squares. -/

/-- The weighted product family `i ↦ (1+λᵢ)^σ · (coeff i S) · (coeff i T)`
is summable: it is dominated by the AM–GM bound coming from the two
weighted-square-summable families. -/
lemma weightedProd_summable
    (S T : scalarHs (I := I) (M := M) g σ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i)) := by
  have hS := S.weighted_summable
  have hT := T.weighted_summable
  have h_dom : Summable
      (fun i : EigenIdx (I := I) (M := M) g =>
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2)) :=
    (hS.mul_left _).add (hT.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
    scalarSobolevWeight_nonneg (I := I) (M := M) i σ
  have h_amgm :
      |scalarSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i)| ≤
        (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (S.coeff i) ^ 2) +
          (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hw]
    have h_prod : |S.coeff i * T.coeff i| ≤
        (1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|S.coeff i| - |T.coeff i|),
        abs_nonneg (S.coeff i), abs_nonneg (T.coeff i),
        sq_abs (S.coeff i), sq_abs (T.coeff i)]
    calc
      scalarSobolevWeight (I := I) (M := M) i σ *
            |S.coeff i * T.coeff i|
          ≤ scalarSobolevWeight (I := I) (M := M) i σ *
            ((1 / 2) * (S.coeff i) ^ 2 + (1 / 2) * (T.coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_left h_prod hw
      _ = (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (S.coeff i) ^ 2) +
            (1 / 2) * (scalarSobolevWeight (I := I) (M := M) i σ *
              (T.coeff i) ^ 2) := by ring
  simpa using h_amgm

/-- The weighted `Hˢ` inner-product value, as a bare function:
`⟪S, T⟫ = ∑ᵢ (1 + λᵢ)^σ · (coeff i S) · (coeff i T)`. -/
def innerFun (S T : scalarHs (I := I) (M := M) g σ) : ℝ :=
  ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
    (S.coeff i * T.coeff i)

/-- `innerFun T T` is the weighted sum of squares
`∑ᵢ (1 + λᵢ)^σ (coeff i T)²`. -/
lemma innerFun_self (T : scalarHs (I := I) (M := M) g σ) :
    innerFun (I := I) (M := M) T T =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  unfold innerFun
  refine tsum_congr (fun i => ?_)
  rw [sq]

/-! ### The `InnerProductSpace.Core` -/

/-- The pre-inner-product `Core` underlying the weighted `Hˢ` inner
product: symmetry, positive-definiteness, additivity and homogeneity in
the first slot are all immediate from the corresponding `tsum`
identities. -/
@[reducible] def innerCore :
    InnerProductSpace.Core ℝ
      (scalarHs (I := I) (M := M) g σ) where
  inner S T := innerFun (I := I) (M := M) S T
  conj_inner_symm S T := by
    simp only [conj_trivial]
    unfold innerFun
    refine tsum_congr (fun i => ?_)
    ring
  re_inner_nonneg T := by
    simp only [RCLike.re_to_real]
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T]
    refine tsum_nonneg (fun i => ?_)
    have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i σ
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
    -- `∑ wᵢ (coeff i)² = 0` with nonnegative summable terms forces each
    -- term to vanish; since `wᵢ > 0`, every coordinate is `0`.
    rw [show (innerFun (I := I) (M := M) T T) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 from innerFun_self (I := I) (M := M) T] at hT
    have h_nonneg : ∀ i : EigenIdx (I := I) (M := M) g,
        0 ≤ scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
      intro i
      have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
        scalarSobolevWeight_nonneg (I := I) (M := M) i σ
      positivity
    have h_zero : ∀ i : EigenIdx (I := I) (M := M) g,
        scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 = 0 := by
      intro i
      have h_le := Summable.le_tsum T.weighted_summable i
        (fun j _ => h_nonneg j)
      rw [hT] at h_le
      exact le_antisymm h_le (h_nonneg i)
    ext i
    have hwi : scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2
        = 0 := h_zero i
    have hw_ne : scalarSobolevWeight (I := I) (M := M) i σ ≠ 0 :=
      (scalarSobolevWeight_pos (I := I) (M := M) i σ).ne'
    have h_sq : (T.coeff i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hwi with h | h
      · exact absurd h hw_ne
      · exact h
    have : T.coeff i = 0 := by nlinarith [h_sq]
    simpa using this

/-- The `NormedAddCommGroup` instance on `Hˢ` induced by the weighted
inner product. -/
instance instNormedAddCommGroup :
    NormedAddCommGroup (scalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := innerCore (I := I) (M := M) (g := g) (σ := σ))

/-- The `InnerProductSpace ℝ` instance on `Hˢ`. -/
instance instInnerProductSpace :
    InnerProductSpace ℝ (scalarHs (I := I) (M := M) g σ) :=
  InnerProductSpace.ofCore
    (innerCore (I := I) (M := M) (g := g) (σ := σ)).1

/-- The `Hˢ` inner product is the weighted `tsum`
`∑ᵢ (1 + λᵢ)^σ · (coeff i S) · (coeff i T)`. -/
lemma inner_def (S T : scalarHs (I := I) (M := M) g σ) :
    (inner ℝ S T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (S.coeff i * T.coeff i) := rfl

/-- The `Hˢ` inner product of `T` with itself is the weighted sum of
squares `∑ᵢ (1+λᵢ)^σ (coeff i T)²`. -/
lemma inner_self_eq (T : scalarHs (I := I) (M := M) g σ) :
    (inner ℝ T T : ℝ) =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
  innerFun_self (I := I) (M := M) T

/-! ### The weighted-norm identity -/

/-- The squared `Hˢ` norm equals the weighted sum of squared
coordinates: `‖T‖² = ∑ᵢ (1 + λᵢ)^σ · (coeff i T)²`. -/
theorem norm_sq_eq_tsum
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_self_eq]

/-- The `Hˢ` norm is the square root of the weighted sum of squared
coordinates. -/
theorem norm_eq_sqrt_tsum
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖T‖ =
      Real.sqrt (∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2) := by
  rw [← norm_sq_eq_tsum]
  exact (Real.sqrt_sq (norm_nonneg T)).symm

end scalarHs

/-! ## The rescaling isometry `Hˢ ≃ₗᵢ ℓ²(EigenIdx g, ℝ)`

The diagonal rescaling `cᵢ ↦ √(1+λᵢ)^σ · cᵢ` carries `Hˢ` bijectively
onto `ℓ²(EigenIdx g, ℝ)`: weighted square-summability of `cᵢ` is exactly
square-summability of the rescaled family. -/

namespace scalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

/-- The rescaled coordinate family `i ↦ √(1+λᵢ)^σ · coeff i` of an `Hˢ`
element is square-summable, hence a member of `ℓ²(EigenIdx g, ℝ)`. -/
lemma rescale_memℓp (T : scalarHs (I := I) (M := M) g σ) :
    Memℓp (fun i : EigenIdx (I := I) (M := M) g =>
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) 2 := by
  apply memℓp_gen
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun i => scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    have hpr : ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℝ≥0∞).toReal =
        ‖Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i‖ ^ (2 : ℕ) := by
      rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [hpr, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
  rw [h_eq]
  exact T.weighted_summable

/-- The forward rescaling map `Hˢ → ℓ²(EigenIdx g, ℝ)`,
`T ↦ (i ↦ √(1+λᵢ)^σ · coeff i)`. -/
def rescaleToL2 (T : scalarHs (I := I) (M := M) g σ) :
    lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 :=
  ⟨fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
      T.coeff i, rescale_memℓp (I := I) (M := M) T⟩

@[simp] lemma rescaleToL2_apply
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleToL2 (I := I) (M := M) T : _ → ℝ) i =
      Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i := rfl

/-- Any `ℓ²(EigenIdx g, ℝ)` family, divided by `√(1+λᵢ)^σ`, satisfies the
weighted square-summability defining `Hˢ`. -/
lemma rescaleFromL2_weighted_summable
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
          (f : _ → ℝ) i) ^ 2) := by
  have hf : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ((f : _ → ℝ) i) ^ 2) := by
    have hmem := lp.memℓp f
    have h := hmem.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : EigenIdx (I := I) (M := M) g =>
          ‖(f : _ → ℝ) i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ((f : _ → ℝ) i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rwa [h_eq] at h
  have h_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        scalarSobolevWeight (I := I) (M := M) i σ *
          ((Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
            (f : _ → ℝ) i) ^ 2) =
      (fun i => ((f : _ → ℝ) i) ^ 2) := by
    funext i
    have hw_pos : 0 < scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_pos (I := I) (M := M) i σ
    have hsq : Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
        scalarSobolevWeight (I := I) (M := M) i σ :=
      sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
    rw [mul_pow, inv_pow, hsq]
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  rw [h_eq]
  exact hf

/-- The inverse rescaling map `ℓ²(EigenIdx g, ℝ) → Hˢ`,
`f ↦ (i ↦ √(1+λᵢ)^σ ⁻¹ · f i)`. -/
def rescaleFromL2
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2) :
    scalarHs (I := I) (M := M) g σ where
  coeff i := (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
    (f : _ → ℝ) i
  weighted_summable := rescaleFromL2_weighted_summable (I := I) (M := M) f

@[simp] lemma rescaleFromL2_coeff
    (f : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2)
    (i : EigenIdx (I := I) (M := M) g) :
    (rescaleFromL2 (I := I) (M := M) (g := g) (σ := σ) f).coeff i =
      (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ))⁻¹ *
        (f : _ → ℝ) i := rfl

/-- The rescaling map `Hˢ → ℓ²(EigenIdx g, ℝ)` packaged as a linear
isometric equivalence. The forward map is the diagonal rescaling
`cᵢ ↦ √(1+λᵢ)^σ · cᵢ`; norm preservation is the weighted-norm
identity. -/
def rescaleEquivL2 :
    scalarHs (I := I) (M := M) g σ ≃ₗᵢ[ℝ]
      lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 where
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
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt_pos.ne', one_mul]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [rescaleToL2_apply, rescaleFromL2_coeff]
    have hsqrt_pos :
        0 < Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr (scalarSobolevWeight_pos (I := I) (M := M) i σ)
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  norm_map' T := by
    -- `‖rescale T‖² = ∑ ‖√wᵢ · coeffᵢ‖² = ∑ wᵢ coeffᵢ² = ‖T‖²`.
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_lp_sq :
        ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 =
          ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
            (T.coeff i) ^ 2 := by
      have h := lp.norm_rpow_eq_tsum
        (p := 2)
        (E := fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (by norm_num) (rescaleToL2 (I := I) (M := M) T)
      rw [hpr] at h
      have h_lhs : ‖rescaleToL2 (I := I) (M := M) T‖ ^ (2 : ℝ) =
          ‖rescaleToL2 (I := I) (M := M) T‖ ^ 2 := by norm_cast
      rw [h_lhs] at h
      rw [h]
      refine tsum_congr (fun i => ?_)
      have hsq :
          Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) ^ 2 =
            scalarSobolevWeight (I := I) (M := M) i σ :=
        sq_sqrt_scalarSobolevWeight (I := I) (M := M) i σ
      have hcast :
          ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℝ) =
            ‖(rescaleToL2 (I := I) (M := M) T : _ → ℝ) i‖ ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hcast, rescaleToL2_apply, Real.norm_eq_abs, sq_abs, mul_pow, hsq]
    have h_norm_sq : ‖T‖ ^ 2 =
        ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
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
    (T : scalarHs (I := I) (M := M) g σ) :
    (rescaleEquivL2 (I := I) (M := M) (g := g) (σ := σ) T : _ → ℝ) =
      (fun i => Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
        T.coeff i) := rfl

/-! ### Completeness of `Hˢ`

Transported from completeness of `ℓ²(EigenIdx g, ℝ)` along the linear
isometric equivalence `rescaleEquivL2`. -/

instance instCompleteSpace :
    CompleteSpace (scalarHs (I := I) (M := M) g σ) :=
  (rescaleEquivL2 (I := I) (M := M)
    (g := g) (σ := σ)).toIsometryEquiv.completeSpace

end scalarHs

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
