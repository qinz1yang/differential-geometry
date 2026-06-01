import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.FaithfulH1Embedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.TensorAllOrdersRegularity

/-!
# Finite eigen-combinations as smooth weak solutions and their spectral identities

For a closed Riemannian manifold `(M, g)` and rank `(0, 2)`, this file builds the
*finite eigen-combination*
`finiteEigenCombo F c := ∑_{i ∈ F} c i • eᵢ`,
where `eᵢ = eigenvectorSmooth g 0 2 i` is the chart-locality-free
smooth representative of the connection-Laplacian resolvent eigenbasis vector at
index `i`, `F` a finite set of eigen-indices and `c` a real coefficient family.
This is a genuine smooth compactly-supported `(0, 2)`-tensor section.

It is the grounded analytic base of the spectral smooth-representative gate: a
finite combination of eigenvectors is honestly a smooth weak solution of the
connection Laplacian, and its eigenbasis coordinates are *exactly* the indicator
of `F` weighted by `c` (the diagonal nature of the eigenbasis). From those two
facts the spectral norms of the combination — at every `Hˢ` scale and after every
iterate of the connection Laplacian — collapse to *finite* weighted sums over `F`,
with no cross-terms, which is the orthogonality that avoids a `|F|`-blowup.

## Main definitions

* `finiteEigenCombo F c` — the finite eigen-combination as `SmoothCcTensor g 0 2`.

## Main results

* `finiteEigenCombo_contMDiff` — the underlying section is `C^∞`.
* `finiteEigenCombo_toL2` — its `L²` image is `∑_{i ∈ F} c i • bᵢ`, `bᵢ` the
  resolvent eigenbasis vector.
* `finiteEigenCombo_tensorL2Coeff` — its `i`-th eigenbasis coordinate is
  `if i ∈ F then c i else 0` (diagonality / orthonormality of the eigenbasis).
* `finiteEigenCombo_weakSolution` — the `(T, F)`-weak-solution identity of the
  connection Laplacian in the exact shape consumed by
  `tensorComponent_memWkp_allOrders_interior`, with source
  `F = -Δ_∇ (finiteEigenCombo F c)`.
* `finiteEigenCombo_rawConnLap_tensorL2Coeff` — the `L²`-coordinate eigen-equation
  `cᵢ(Δ_∇ u) = -λᵢ · cᵢ(u)` for `u = finiteEigenCombo F c` (the honest spectral
  content; the strong pointwise eigen-equation is not used / not on disk).
* `finiteEigenCombo_spectral_normSq` — the `Hˢ`-norm identity
  `‖finiteEigenCombo F c‖²_{Hˢ} = ∑_{i ∈ F} (1 + λᵢ)^σ · (c i)²`.
* `finiteEigenCombo_l2NormSq` — `‖finiteEigenCombo F c‖²_{L²} = ∑_{i ∈ F} (c i)²`.
* `finiteEigenCombo_iterRawConnLap_l2NormSq` — the iterated-Laplacian identity
  `‖Δ_∇^j (finiteEigenCombo F c)‖²_{L²} = ∑_{i ∈ F} λᵢ^{2j} · (c i)²`.

## Sign convention

Geometer Laplacian `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹` (spectrum `⊆ [1, ∞)`), and `1 + λᵢ = (i.fst.val)⁻¹`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

variable (g : SmoothRiemannianMetric I M)

/-- The chart-locality-free smooth representative of the resolvent eigenbasis
vector at eigen-index `i`, as a smooth compactly-supported `(0, 2)`-tensor. -/
abbrev eigenSmooth
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) : SmoothCcTensor g 0 2 :=
  eigenvectorSmooth (I := I) (M := M) g 0 2 i

/-- **The finite eigen-combination.** For a finite set `F` of eigen-indices and a
real coefficient family `c`, the finite sum `∑_{i ∈ F} c i • eᵢ` of the smooth
eigenvector representatives, a smooth compactly-supported `(0, 2)`-tensor. -/
def finiteEigenCombo
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) : SmoothCcTensor g 0 2 :=
  ∑ i ∈ F, c i • eigenSmooth (I := I) (M := M) g i

/-- The finite eigen-combination unfolds to the finite sum of scaled smooth
eigenvectors. -/
lemma finiteEigenCombo_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    finiteEigenCombo (I := I) (M := M) g F c =
      ∑ i ∈ F, c i • eigenSmooth (I := I) (M := M) g i := rfl

/-- **The finite eigen-combination is `C^∞`.** The underlying tensor section of
`finiteEigenCombo F c` is a `C^∞` section of the `(0, 2)`-tensor bundle. -/
theorem finiteEigenCombo_contMDiff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M =>
        TotalSpace.mk' (TensorRSModel 0 2 ℝ E) x
          ((finiteEigenCombo (I := I) (M := M) g F c).toSection x)) :=
  (finiteEigenCombo (I := I) (M := M) g F c).toSection.contMDiff

/-- The compactness witness used throughout: the chart-locality-free compactness
of the L²-side tensor resolvent at rank `(0, 2)`. -/
abbrev hCompact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2

/-- **The `L²` image of the finite eigen-combination.** It is the finite
combination `∑_{i ∈ F} c i • bᵢ` of the chart-locality-free resolvent eigenbasis
vectors `bᵢ = tensorResolventEigenbasisVec i`. -/
theorem finiteEigenCombo_toL2
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) =
      ∑ i ∈ F, c i •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (hCompact (I := I) (M := M) g) i := by
  rw [← SmoothCcTensor.toL2_apply, finiteEigenCombo_eq, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, SmoothCcTensor.toL2_apply,
    eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 i]

open scoped Classical in
/-- The `i`-th eigenbasis coordinate of the smooth eigenvector representative `eⱼ`
is the orthonormality indicator: `cᵢ(eⱼ) = if i = j then 1 else 0`.

The eigenbasis-coordinate functional is `⟪bᵢ, ·⟫` against the chart-locality-free
Hilbert eigenbasis `b`; since `(eⱼ : L²) = b j` and `b` is orthonormal, this is the
Kronecker delta. -/
theorem tensorL2Coeff_ofCompact_eigenSmooth
    (i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((eigenSmooth (I := I) (M := M) g j : TensorL2 0 2 g)) i =
      (if i = j then (1 : ℝ) else 0) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g) with hb_def
  have hbj : (eigenSmooth (I := I) (M := M) g j : TensorL2 0 2 g) = b j := by
    rw [hb_def, tensorResolventHilbertEigenbasisSigma_apply
      (I := I) (M := M) (hCompact (I := I) (M := M) g) j,
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 j]
  rw [tensorL2Coeff_eq_inner, hbj]
  have horth := b.orthonormal
  rw [orthonormal_iff_ite] at horth
  exact horth i j

open scoped Classical in
/-- **The eigenbasis coordinate of the finite eigen-combination.** The `i`-th
eigenbasis coordinate of `finiteEigenCombo F c` is `c i` when `i ∈ F` and `0`
otherwise. -/
theorem finiteEigenCombo_tensorL2Coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i =
      (if i ∈ F then c i else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, finiteEigenCombo_toL2,
    inner_sum]
  have h_term : ∀ j ∈ F,
      (inner ℝ
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) i)
          (c j • tensorResolventEigenbasisVec (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j) : ℝ) =
        (if i = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    rw [show tensorResolventEigenbasisVec (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j =
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j from
        (tensorResolventHilbertEigenbasisSigma_apply
          (I := I) (M := M) (hCompact (I := I) (M := M) g) j).symm]
    have horth := (tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) (hCompact (I := I) (M := M) g)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth i j]
    by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hiF : i ∈ F
  · rw [Finset.sum_eq_single i]
    · simp [hiF]
    · intro j _ hji
      rw [if_neg (fun h => hji h.symm)]
    · intro h; exact absurd hiF h
  · rw [if_neg hiF, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hiF (by rw [h]; exact hj))]

/-- **The smooth weak-solution identity.** For the finite eigen-combination
`u = finiteEigenCombo F c` and any smooth compactly-supported test tensor `v`, the
integrated covariant-gradient pairing of `u` against `v` equals the `L²` pairing of
the source `-Δ_∇ u` against `v`:
`∫_M ⟨∇u, ∇v⟩ dμ_g = ⟨-Δ_∇ u, v⟩_{L²}`.

This is precisely the `hweak` hypothesis of
`tensorComponent_memWkp_allOrders_interior` with solution `T = u` and source
`F = -Δ_∇ u = -rawTensorConnLapSmooth g 0 2 u`. -/
theorem finiteEigenCombo_weakSolution
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (v : SmoothCcTensor g 0 2) :
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2
        (finiteEigenCombo (I := I) (M := M) g F c) v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (- rawTensorConnLapSmooth (I := I) g 0 2
            (finiteEigenCombo (I := I) (M := M) g F c)).toFun v.toFun := by
  set u : SmoothCcTensor g 0 2 := finiteEigenCombo (I := I) (M := M) g F c with hu
  rw [(tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
        (I := I) (M := M) g 0 2 u v).symm]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
    (I := I) (M := M) g u v]
  rw [show (- rawTensorConnLapSmooth (I := I) g 0 2 u).toFun =
        (-1 : ℝ) • (rawTensorConnLapSmooth (I := I) g 0 2 u).toFun by
      funext x
      rw [Pi.smul_apply, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
        SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
        TensorRSSpace.toModel_neg, neg_one_smul]]
  rw [tensorL2Inner_smul_left]
  ring

/-- **The `L²`-coordinate eigen-equation for `Δ_∇`.** For any smooth
compactly-supported `(0, 2)`-tensor `T`, applying the rough connection Laplacian
scales the `i`-th eigenbasis coordinate by `-λᵢ`:
`cᵢ(Δ_∇ T) = -λᵢ · cᵢ(T)`.

Since `Δ_∇ T = T - (1 - Δ_∇) T` and the per-step identity gives
`cᵢ((1 - Δ_∇) T) = (1 + λᵢ) · cᵢ(T)`, additivity of the coordinate functional
yields `cᵢ(Δ_∇ T) = cᵢ(T) - (1 + λᵢ) cᵢ(T) = -λᵢ · cᵢ(T)`. -/
theorem rawConnLapSmooth_tensorL2Coeff
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 T) i := by
  have h_split :
      rawTensorConnLapSmooth (I := I) g 0 2 T =
        T - oneMinusConnLapSmooth (I := I) g 0 2 T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 2 T =
          T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl]
    abel
  rw [h_split, map_sub, tensorL2Coeff_eq_inner, inner_sub_right,
    ← tensorL2Coeff_eq_inner, ← tensorL2Coeff_eq_inner,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
      (I := I) (M := M) g (hCompact (I := I) (M := M) g) T i]
  ring

/-- **The iterated `L²`-coordinate eigen-equation.** The `i`-th eigenbasis
coordinate of `Δ_∇^j T` is `(-λᵢ)^j · cᵢ(T)`. -/
theorem rawConnLapIter_tensorL2Coeff
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) (j : ℕ) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 T) i := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rawTensorConnLapIter_succ,
        rawConnLapSmooth_tensorL2Coeff (I := I) (M := M) g
          (rawTensorConnLapIter (I := I) g 0 2 j T) i, ih, pow_succ]
      ring

open scoped Classical in
/-- The eigenbasis coordinate of `Δ_∇^j (finiteEigenCombo F c)` is supported on
`F`: at index `i ∈ F` it is `(-λᵢ)^j · c i`, and `0` off `F`. -/
private lemma finiteEigenCombo_iterRawConnLap_tensorL2Coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (j : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))) i =
      (if i ∈ F then (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j * c i
        else 0) := by
  rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g
    (finiteEigenCombo (I := I) (M := M) g F c) i j,
    show SmoothCcTensor.toL2 (finiteEigenCombo (I := I) (M := M) g F c) =
        (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) from
      SmoothCcTensor.toL2_apply _,
    finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i]
  by_cases h : i ∈ F <;> simp [h]

/-- **The iterated-Laplacian `L²`-norm identity.** The squared `L²` norm of
`Δ_∇^j (finiteEigenCombo F c)` is the finite weighted sum
`∑_{i ∈ F} λᵢ^{2j} · (c i)²`.

This is the orthogonality that avoids the `|F|`-blowup: Parseval turns the squared
`L²` norm into the sum of squared eigenbasis coordinates, which — being supported
on `F` and free of cross-terms by orthonormality — is exactly the finite sum. -/
theorem finiteEigenCombo_iterRawConnLap_l2NormSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (j : ℕ) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ^ 2 =
      ∑ i ∈ F,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (c i) ^ 2 := by
  classical
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
    (hCompact (I := I) (M := M) g)]
  rw [tsum_eq_sum (s := F) (f := fun i =>
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))) i) ^ 2) ?_]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [finiteEigenCombo_iterRawConnLap_tensorL2Coeff (I := I) (M := M) g F c j i,
      if_pos hi, mul_pow, ← pow_mul, mul_comm j 2]
    rw [(even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
  · intro b hb
    simp only [finiteEigenCombo_iterRawConnLap_tensorL2Coeff
      (I := I) (M := M) g F c j b]
    rw [if_neg hb]
    ring

/-- **The `L²`-norm identity.** The squared `L²` norm of `finiteEigenCombo F c` is
the finite sum `∑_{i ∈ F} (c i)²` (the `j = 0` case of the iterated identity). -/
theorem finiteEigenCombo_l2NormSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    ‖(finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)‖ ^ 2 =
      ∑ i ∈ F, (c i) ^ 2 := by
  have h := finiteEigenCombo_iterRawConnLap_l2NormSq (I := I) (M := M) g F c 0
  rw [rawTensorConnLapIter_zero, SmoothCcTensor.toL2_apply] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

open scoped Classical in
/-- The `Hˢ`-spectral element whose eigenbasis coordinates are the indicator
`(if i ∈ F then c i else 0)` — the coordinates of `finiteEigenCombo F c`. -/
def finiteEigenComboHs
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ) :
    tensorHs (I := I) (M := M) g 0 2 σ where
  coeff i := if i ∈ F then c i else 0
  weighted_summable := by
    classical
    refine summable_of_ne_finset_zero (s := F) ?_
    intro i hiF
    rw [if_neg hiF]
    ring

open scoped Classical in
/-- The `coeff` of `finiteEigenComboHs F c σ` is the indicator
`if i ∈ F then c i else 0`. -/
@[simp] lemma finiteEigenComboHs_coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i =
      (if i ∈ F then c i else 0) := rfl

/-- The `coeff` of `finiteEigenComboHs F c σ` matches the `L²` eigenbasis
coordinate of `finiteEigenCombo F c`. -/
lemma finiteEigenComboHs_coeff_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i := by
  rw [finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i]
  rfl

/-- **The `Hˢ`-norm identity (spectral orthogonality).** The squared `Hˢ` norm of
the spectral packaging of `finiteEigenCombo F c` is the weighted finite sum
`∑_{i ∈ F} (1 + λᵢ)^σ · (c i)²`.

The `Hˢ` inner product is diagonal in the eigenbasis coordinates, so the squared
norm is the weighted tsum of squared coordinates (`norm_sq_eq_tsum`); since the
coordinates are supported on `F`, the tsum collapses to a finite sum with no
cross-terms — the orthogonality input that avoids any `|F|`-blowup. -/
theorem finiteEigenCombo_spectral_normSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ) :
    ‖finiteEigenComboHs (I := I) (M := M) g F c σ‖ ^ 2 =
      ∑ i ∈ F,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ * (c i) ^ 2 := by
  classical
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
  rw [tsum_eq_sum (s := F) (f := fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        ((finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i) ^ 2) ?_]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [finiteEigenComboHs_coeff, if_pos hi]
    unfold tensorSobolevWeight
    rfl
  · intro b hb
    simp only [finiteEigenComboHs_coeff]
    rw [if_neg hb]
    ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
