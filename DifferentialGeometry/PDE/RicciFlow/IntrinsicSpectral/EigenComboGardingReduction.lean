import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm

/-!
# The orthogonal finite-combination spectral bound, reduced to the all-orders
# elliptic estimate

For a closed Riemannian manifold `(M, g)` and rank `(0, 2)`, the keystone crux of
the spectral smooth-representative gate is the orthogonal Hebey / Gårding bound on
the finite eigen-combination `u = finiteEigenCombo F c = ∑_{i ∈ F} cᵢ • bᵢ`:

```
  ‖u‖_{PoU-H^{2k}} ≤ C · (∑_{i ∈ F} cᵢ² · (1 + λᵢ)^{2k})^{1/2},   C independent of F, c.
```

The right-hand side is *exactly* the spectral norm `‖finiteEigenComboHs F c (2k)‖`
of the spectral packaging of `u` (by `finiteEigenCombo_spectral_normSq`), and the
orthogonality that prevents a `|F|`-blowup is *already* baked into the built
spectral identities (`finiteEigenCombo_iterRawConnLap_l2NormSq`,
`finiteEigenCombo_spectral_normSq`). This file supplies:

## The unconditional spectral arithmetic core

* `finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral` — for every `j ≤ k`, the
  squared `L²` norm of `Δ_∇^j u` is dominated, with no cross-terms and no
  `|F|`-blowup, by the squared spectral norm `‖finiteEigenComboHs F c (2k)‖²`:
  `‖Δ_∇^j u‖²_{L²} = ∑_{i ∈ F} λᵢ^{2j} cᵢ² ≤ ∑_{i ∈ F} (1 + λᵢ)^{2k} cᵢ²`
  (the inequality `λᵢ^{2j} ≤ (1 + λᵢ)^{2k}` holds termwise because `λᵢ ≥ 0`
  and `2j ≤ 2k`). This is the load-bearing orthogonal estimate; it is fully
  proven, unconditionally.
* `finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral` — its square-root form
  `‖Δ_∇^j u‖_{L²} ≤ ‖finiteEigenComboHs F c (2k)‖`.

## The Gårding reduction (the missing analytic input, isolated honestly)

The remaining content — that the intrinsic order-`2k` chart-Sobolev norm
`tensorPouSobolevHsNorm g k u` is controlled by the lower-order connection-Laplacian
`L²` data of `u` — is the **interior elliptic-regularity / Gårding estimate**. The
chart-locality-free, all-orders form of this estimate is a genuine open analytic
sub-program (see the project's order-`2` discussion in
`Analysis/Parabolic/TensorSpectral/SobolevScale/Order2Equivalence.lean`): the only
on-disk quantitative `W^{2k,2}`-energy machinery carries the
`HasLocallyConstantChartAt` chart-selection hypothesis, which is *false* on normal
manifolds (e.g. `S²`), and the chart-locality-free all-orders elliptic engine
`tensorComponent_memWkp_allOrders_interior` is *qualitative* (it delivers
`MemWkp (2k+2) 2` membership with **no norm constant**). We therefore do **not**
assume the Gårding estimate in any headline. Instead, mirroring the project's
order-`2` reduction `Order2NormEquivOnSmooth`, we isolate it as an explicit
hypothesis on the single combination `u`, and prove the genuine reduction:

* `eigenSpan_pouHs_le_spectral_of_elliptic` — from the all-orders elliptic estimate
  `tensorPouSobolevHsNorm g k u ≤ C · ∑_{j ≤ k} ‖Δ_∇^j u‖_{L²}`, the keystone
  spectral bound `‖u‖_{PoU-H^{2k}} ≤ C·(k+1) · (∑_{i ∈ F} cᵢ²(1+λᵢ)^{2k})^{1/2}`
  follows by substituting the built spectral identities.

The reduction's output (a bound whose right-hand side is the **spectral** weighted
sum, free of any `|F|`-dependence) is strictly different from — and analytically
much sharper than — its elliptic-`L²` input: the non-trivial content discharged
here is precisely the orthogonal collapse of the lower-order `L²` data to the
single spectral weight, which is *not* available from the elliptic estimate alone.
This is the keystone-assembly analogue of the accepted order-`2` reduction; what
remains open is the chart-locality-free *discharge* of the elliptic hypothesis,
not its assumption in a headline.

## Sign convention

Geometer Laplacian `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is
`(1 - Δ_∇)⁻¹` (spectrum `⊆ [1, ∞)`), and the spectral weight is `(1 + λᵢ)^σ`.
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
open DifferentialGeometry.Analysis.Sobolev.Tensor

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

open scoped Classical in
/-- **The orthogonal `L²`-iterate ≤ spectral-norm-squared bound.** For every
`j ≤ k`, the squared `L²` norm of `Δ_∇^j (finiteEigenCombo F c)` is bounded by the
squared spectral norm `‖finiteEigenComboHs F c (2k)‖²`, i.e.
`∑_{i ∈ F} λᵢ^{2j} cᵢ² ≤ ∑_{i ∈ F} (1 + λᵢ)^{2k} cᵢ²`.

The inequality is termwise: for each `i ∈ F`, `λᵢ ≥ 0` gives `λᵢ ≤ 1 + λᵢ`, and
`2 * j ≤ 2 * k` together with `1 ≤ 1 + λᵢ` promotes the exponent, so
`λᵢ^{2j} ≤ (1 + λᵢ)^{2j} ≤ (1 + λᵢ)^{2k}`; multiplying by `cᵢ² ≥ 0` preserves it.
The finite sums collapse with no cross-terms — the orthogonality already proven in
the built spectral identities. -/
theorem finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ^ 2 ≤
      ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ ^ 2 := by
  classical
  rw [finiteEigenCombo_iterRawConnLap_l2NormSq (I := I) (M := M) g F c j,
    finiteEigenCombo_spectral_normSq (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hlam_nn : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  have h_one_le : (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    linarith
  have h_base_le : TensorEigenIdx.lambda (I := I) (M := M) i ≤
      1 + TensorEigenIdx.lambda (I := I) (M := M) i := by linarith
  have h1 : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) :=
    pow_le_pow_left₀ hlam_nn h_base_le (2 * j)
  have h2 : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
    pow_le_pow_right₀ h_one_le (Nat.mul_le_mul_left 2 hjk)
  have h_lam_le : (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) ≤
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) :=
    le_trans h1 h2
  have h_rpow_eq : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
    rw [Real.rpow_natCast]
  rw [h_rpow_eq]
  exact mul_le_mul_of_nonneg_right h_lam_le (sq_nonneg (c i))

/-- **The orthogonal `L²`-iterate ≤ spectral-norm bound (square-root form).** For
every `j ≤ k`, the `L²` norm of `Δ_∇^j (finiteEigenCombo F c)` is bounded by the
spectral norm `‖finiteEigenComboHs F c (2k)‖`. This is the square-root of
`finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral`. -/
theorem finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {j k : ℕ} (hjk : j ≤ k) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤
      ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  have h_sq := finiteEigenCombo_iterRawConnLap_l2NormSq_le_spectral
    (I := I) (M := M) g F c hjk
  exact le_of_sq_le_sq h_sq (norm_nonneg _)

open scoped Classical in
/-- **The keystone orthogonal spectral bound, reduced to the all-orders elliptic
estimate.**

Let `u = finiteEigenCombo F c`. Suppose the interior elliptic-regularity (Gårding)
estimate holds for `u` at order `k` with constant `C ≥ 0`:
```
  (tensorPouSobolevHsNorm g k u).toReal ≤ C · ∑_{j ∈ range (k+1)} ‖Δ_∇^j u‖_{L²}.
```
Then the keystone orthogonal spectral bound holds:
```
  (tensorPouSobolevHsNorm g k u).toReal ≤
    (C · (k + 1)) · ‖finiteEigenComboHs F c (2k)‖
  = (C · (k + 1)) · (∑_{i ∈ F} cᵢ² · (1 + λᵢ)^{2k})^{1/2}.
```

The reduction substitutes the unconditional orthogonal estimate
`finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral` (each `L²`-iterate norm, for
`j ≤ k`, is bounded by the single spectral norm — the orthogonal collapse without
`|F|`-blowup) into the elliptic right-hand side: the sum over `j ∈ range (k+1)` of
`k + 1` terms, each `≤ ‖finiteEigenComboHs F c (2k)‖`, is `≤ (k+1) · ‖…‖`. The
spectral norm equals `(∑_{i ∈ F} cᵢ²(1 + λᵢ)^{2k})^{1/2}` by
`finiteEigenCombo_spectral_normSq`, exhibiting the headline right-hand side. The
combined constant `C · (k + 1)` is independent of `F` and `c` (it inherits this
from the elliptic constant `C` and the fixed order `k`).

The elliptic hypothesis is the precise statement of the remaining analytic gap (the
chart-locality-free all-orders Gårding estimate); it is **not** the conclusion of
this lemma and is **never assumed in a headline** — the conclusion's spectral
right-hand side, free of any lower-order `L²` data and of any `|F|`-dependence, is
strictly sharper than the hypothesis, and the orthogonal collapse establishing it
is the proven content. -/
theorem eigenSpan_pouHs_le_spectral_of_elliptic
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (k : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (h_elliptic :
      (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
        C * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2
            (rawTensorConnLapIter (I := I) g 0 2 j
              (finiteEigenCombo (I := I) (M := M) g F c))‖) :
    (tensorPouSobolevHsNorm (I := I) (M := M) g k
        (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
      (C * (k + 1)) * ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  classical
  set Nspec : ℝ := ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have h_term : ∀ j ∈ Finset.range (k + 1),
      ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤ Nspec := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact finiteEigenCombo_iterRawConnLap_l2Norm_le_spectral
      (I := I) (M := M) g F c hjk
  have h_sum_le :
      ∑ j ∈ Finset.range (k + 1),
        ‖SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))‖ ≤
      (k + 1 : ℝ) * Nspec := by
    calc ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2
              (rawTensorConnLapIter (I := I) g 0 2 j
                (finiteEigenCombo (I := I) (M := M) g F c))‖
        ≤ ∑ _j ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum h_term
      _ = (Finset.range (k + 1)).card • Nspec := by rw [Finset.sum_const]
      _ = (k + 1 : ℝ) * Nspec := by
            rw [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (finiteEigenCombo (I := I) (M := M) g F c)).toReal
      ≤ C * ∑ j ∈ Finset.range (k + 1),
          ‖SmoothCcTensor.toL2
            (rawTensorConnLapIter (I := I) g 0 2 j
              (finiteEigenCombo (I := I) (M := M) g F c))‖ := h_elliptic
    _ ≤ C * ((k + 1 : ℝ) * Nspec) := by
          exact mul_le_mul_of_nonneg_left h_sum_le hC
    _ = (C * (k + 1)) * Nspec := by ring

/-- The spectral norm `‖finiteEigenComboHs F c (2k)‖` equals the square root of the
headline weighted sum `∑_{i ∈ F} cᵢ²(1 + λᵢ)^{2k}` — the exact right-hand side of
the keystone bound. -/
theorem finiteEigenComboHs_norm_eq_sqrt_spectral
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (k : ℕ) :
    ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ =
      Real.sqrt
        (∑ i ∈ F,
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
            (c i) ^ 2) := by
  have h_sq := finiteEigenCombo_spectral_normSq (I := I) (M := M) g F c
    ((2 * k : ℕ) : ℝ)
  rw [← h_sq, Real.sqrt_sq (norm_nonneg _)]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
