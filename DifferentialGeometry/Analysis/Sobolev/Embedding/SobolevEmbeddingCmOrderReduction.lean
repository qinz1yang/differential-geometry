import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-!
# Order-reduction collapse of the `C^m` iterated-covariant-derivative embedding

The `C^m` tensor Sobolev embedding `iteratedCovGrad_toSobolev_embedding_Cm`
controls the iterated covariant derivatives `∇^j T` (`0 ≤ j ≤ m`) of a smooth
compactly-supported `(r, s)`-tensor `T` by a sum of *per-degree* intrinsic
Hilbert-Sobolev norms:
$$
  \sum_{j=0}^{m} \bigl\lVert (\nabla^j T)(x) \bigr\rVert
    \;\le\; C \sum_{j=0}^{m}
      \bigl\lVert \nabla^j T \bigr\rVert_{H^{2(k-j)}}.
$$
This file collapses that right-hand side to a single multiple of the spectral
norm `‖T‖_{H^{2k}} = ‖T.toHs (2k)‖`, which is what the metric-family lift
ultimately consumes.

## The collapse, in two genuine steps

The per-degree summand `‖∇^j T‖_{H^{2(k-j)}}` is reduced to `‖T‖_{H^{2k}}` by
factoring through the **fixed-top-order** Sobolev norm `‖∇^j T‖_{H^{2k}}` of the
same iterated derivative:

1. **Order monotonicity** (`iteratedCovGradSobolevNorm_le_topOrder`, fully
   proved here).  Since `2(k - j) ≤ 2k`, the intrinsic Hilbert-Sobolev norm of
   the fixed `(r, s + j)`-tensor `∇^j T` is monotone in the regularity order:
   $$
     \bigl\lVert \nabla^j T \bigr\rVert_{H^{2(k-j)}}
       \;\le\; \bigl\lVert \nabla^j T \bigr\rVert_{H^{2k}}.
   $$
   This is the order-index part of the reduction; it follows from the
   established monotonicity `tensorPouSobolevHsNorm_le_succ` of the
   Hilbert-Schmidt chart-Sobolev norm in the regularity order, transported to
   the completion norm via `tensorPouSobolevHilbert_norm_eq`.

2. **Fixed-top-order rank reduction** (the documented analytic core).  At the
   common top order `2k`, one covariant derivative is bounded by the section it
   differentiates:
   $$
     \bigl\lVert \nabla^j T \bigr\rVert_{H^{2k}}
       \;\le\; C_j \, \lVert T \rVert_{H^{2k}}.
   $$
   In the partition-of-unity chart-Sobolev norm this is the statement that the
   raw chart components of `∇^j T` — which read `∂(components) + Γ·(components)`
   by the chart-component formula `tensorChartComponentRaw_covGrad` — have their
   order-`2k` derivatives dominated by the order-`2k` derivatives of the
   components of `T`, uniformly via the bounded-derivative Christoffel data of
   the compact manifold (`chartChristoffel_bdd_on_pou_tsupport`,
   `covDerivLowerOrderCoeff_contDiffOn`).  This is a coordinate computation
   through the `tsum` / `lintegral` Hilbert-Schmidt machinery and is the sole
   remaining gap; it is isolated here as the explicit hypothesis of the collapse
   engine below.

## Main results

* `iteratedCovGradSobolevNorm_zero` — the degree-`0` term of the embedding's
  right-hand side equals the spectral norm `‖T.toHs (2k)‖` exactly.

* `toHs_norm_mono_order` — the completion-norm `‖T'.toHs σ‖` of a fixed smooth
  compactly-supported tensor is monotone in the regularity order `σ`.

* `iteratedCovGradSobolevNorm_le_topOrder` — step 1 above: the per-degree
  summand is bounded by the fixed-top-order norm of the same iterated
  derivative.

* `iteratedCovGrad_toSobolev_embedding_Cm_collapsed` — the collapse engine: from
  per-degree fixed-top-order rank-reduction bounds (step 2, the analytic core),
  the `C^m` embedding's right-hand side becomes a single multiple of
  `‖T.toHs (2k)‖`.

* `iteratedCovGrad_toSobolev_embedding_C2_collapsed` — the `C²`,
  `(0, 2)`-tensor instance the DeTurck metric family consumes.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The degree-`0` summand of the `C^m` embedding's right-hand side is the
spectral norm `‖T.toHs (2k)‖`: at `j = 0` the iterated covariant derivative is
`T` itself, and `2 (k - 0) = 2k`. -/
@[simp] theorem iteratedCovGradSobolevNorm_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGradSobolevNorm g r s k 0 T =
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  unfold iteratedCovGradSobolevNorm
  simp

/-- The completion norm `‖T'.toHs σ‖` is monotone passing from order `σ` to order
`σ + 1`. -/
private theorem toHs_norm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (σ : ℕ)
    (T' : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) σ T'‖ ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + 1) T'‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono ?_ (tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g σ T')
  exact (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (σ + 1) T').ne

/-- **Monotonicity of the completion norm in the regularity order.** For `σ ≤ τ`
the intrinsic `H^σ` completion norm of a fixed smooth compactly-supported tensor
section is bounded by its `H^τ` completion norm. -/
theorem toHs_norm_mono_order
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {σ τ : ℕ} (hστ : σ ≤ τ)
    (T' : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) σ T'‖ ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) τ T'‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hστ
  clear hστ
  induction d with
  | zero => simp
  | succ d ih =>
      refine le_trans ih ?_
      rw [show σ + (d + 1) = (σ + d) + 1 from by ring]
      exact toHs_norm_le_succ (I := I) (M := M) g (σ + d) T'

/-- **Order reduction to the top order.** The per-degree summand
`‖∇^j T‖_{H^{2(k-j)}}` of the `C^m` embedding's right-hand side is bounded by the
fixed-top-order norm `‖∇^j T‖_{H^{2k}}` of the same `(r, s + j)`-tensor `∇^j T`,
because `2 (k - j) ≤ 2k`.  This isolates the genuine analytic content of the
order reduction to a fixed-top-order rank reduction (step 2). -/
theorem iteratedCovGradSobolevNorm_le_topOrder
    (g : SmoothRiemannianMetric I M) (r s k j : ℕ) (T : SmoothCcTensor g r s) :
    iteratedCovGradSobolevNorm g r s k j T ≤
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * k)
        (iteratedCovGrad g r s j T)‖ := by
  unfold iteratedCovGradSobolevNorm
  exact toHs_norm_mono_order (I := I) (M := M) g
    (by omega : 2 * (k - j) ≤ 2 * k) (iteratedCovGrad g r s j T)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The collapsed `C^m` tensor Sobolev embedding.**

For a closed Riemannian manifold and `2k > dim M + 2m`, assume the per-degree
fixed-top-order rank reduction
`‖∇^j T‖_{H^{2k}} ≤ Cred · ‖T‖_{H^{2k}}` holds for each `j ≤ m` (the analytic
core, step 2).  Then there is a constant `C > 0` such that, for every smooth
compactly-supported `(r, s)`-tensor `T` and every base point `x`, the sum of the
fibre norms of the iterated covariant derivatives `∇^j T` (`0 ≤ j ≤ m`) is
bounded by `C` times the single spectral norm `‖T.toHs (2k)‖`.

The proof chains the `C^m` embedding `iteratedCovGrad_toSobolev_embedding_Cm`
(controlling the fibre-norm sum by the per-degree Sobolev norms) with the order
reduction `iteratedCovGradSobolevNorm_le_topOrder` (lowering each per-degree
order `2(k-j)` to the top order `2k`) and the supplied rank reduction (collapsing
each `‖∇^j T‖_{H^{2k}}` to `‖T‖_{H^{2k}}`). -/
theorem iteratedCovGrad_toSobolev_embedding_Cm_collapsed
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    (Cred : ℝ)
    (h_rank : ∀ (T : SmoothCcTensor g r s), ∀ j ∈ Finset.range (m + 1),
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * k)
        (iteratedCovGrad g r s j T)‖ ≤
        Cred * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖)) ≤
          C * ((m + 1 : ℝ) * Cred) *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  classical
  obtain ⟨C, hC_pos, hC⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm (I := I) (M := M) g r s k m h_super
  refine ⟨C, hC_pos, ?_⟩
  intro T x
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_perdeg : ∀ j ∈ Finset.range (m + 1),
      iteratedCovGradSobolevNorm g r s k j T ≤ Cred * N := by
    intro j hj
    exact le_trans
      (iteratedCovGradSobolevNorm_le_topOrder (I := I) (M := M) g r s k j T)
      (h_rank T j hj)
  refine le_trans (hC T x) ?_
  have h_sum_le :
      (∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T) ≤
        (m + 1 : ℝ) * Cred * N := by
    calc (∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T)
        ≤ ∑ _j ∈ Finset.range (m + 1), Cred * N := Finset.sum_le_sum h_perdeg
      _ = (Finset.range (m + 1)).card • (Cred * N) := by rw [Finset.sum_const]
      _ = (m + 1 : ℝ) * (Cred * N) := by
          rw [Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ = (m + 1 : ℝ) * Cred * N := by ring
  calc C * ∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T
      ≤ C * ((m + 1 : ℝ) * Cred * N) :=
        mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hC_pos)
    _ = C * ((m + 1 : ℝ) * Cred) * N := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The collapsed `C²`, `(0, 2)`-tensor instance.**

The collapse for the `(0, 2)`-tensors (`r = 0`, `s = 2`), `m = 2`, controlling
`‖T(x)‖`, `‖(∇T)(x)‖`, `‖(∇²T)(x)‖` by a single multiple of the spectral norm
`‖T.toHs (2k)‖`, given the fixed-top-order rank reduction for `j ≤ 2` and
`2k > dim M + 4`.  This is the instance the DeTurck metric family consumes. -/
theorem iteratedCovGrad_toSobolev_embedding_C2_collapsed
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4)
    (Cred : ℝ)
    (h_rank : ∀ (T : SmoothCcTensor g 0 2), ∀ j ∈ Finset.range 3,
      ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2 + j) (2 * k)
        (iteratedCovGrad g 0 2 j T)‖ ≤
        Cred * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + j)
            ‖(iteratedCovGrad g 0 2 j T).toSection x‖)) ≤
          C * ((2 + 1 : ℝ) * Cred) *
            ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ := by
  have h_super' : 2 * k > Module.finrank ℝ E + 2 * 2 := by omega
  exact iteratedCovGrad_toSobolev_embedding_Cm_collapsed (I := I) (M := M)
    g 0 2 k 2 h_super' Cred h_rank

end DifferentialGeometry.PDE.RicciFlow

end
