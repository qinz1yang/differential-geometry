import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

/-!
# Top-separated pointwise bounds for the DLa coefficient field

This file isolates the pointwise top-order contribution in the connection-derivative half of the
DeTurck-Lie coefficient field.  The protected top derivative is kept separate from the lower-order
antidiagonal grid window, with an order-independent top coefficient.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section DLaGridBrick

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
theorem symmC0_rfns_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 :=
  rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x

/-! ### DLa top-separated tower (keeps the `A1 = covGrad (connDiffSection g₁ g₀)` head separate). -/

/-- Reshape the `connDiffSection` top-separated engine remainder
`∑_{k<j} b(j-k)·antidiagonalTupleGrid b (k+1)` into `antidiagonalTupleGridPartialSum` currency (`R`-independent
combinatorial count times `antidiagonalTupleGridPartialSum b (j+2)`).  Pure combinatorial. -/
private lemma engineRem_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j,
        b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (∑ k ∈ Finset.range j, Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        antidiagonalTupleGridPartialSum b (j + 2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hg_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
  have h1 : b (j - k) ≤ Combinatorics.antidiagonalTupleGrid b (j - k) :=
    single_le_grid_dla b hb (j - k) (by omega)
  have h2 : Combinatorics.antidiagonalTupleGrid b (j - k) *
      Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) :=
    Combinatorics.antidiagonalTupleGrid_mul_le b hb (j - k) (k + 1)
  have h3 : Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) ≤ antidiagonalTupleGridPartialSum b (j + 2) :=
    grid_le_dLaGridWin b hb (by omega)
  calc b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ Combinatorics.antidiagonalTupleGrid b (j - k) *
          Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        mul_le_mul_of_nonneg_right h1 hg_nn
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) := h2
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) * antidiagonalTupleGridPartialSum b (j + 2) :=
        mul_le_mul_of_nonneg_left h3
          (mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _) (Combinatorics.antidiagonalTupleGridCount_nonneg _))

/-- **connDiffSection top-separated jet bound in `antidiagonalTupleGridPartialSum` currency.**  The top coefficient
`Ktop = 2·Kt0` (`Kt0` = engine head `10·S 0`) is `R`-independent; the remainder is `antidiagonalTupleGridPartialSum`
(house `R`-pattern).  This is the `antidiagonalTupleGridPartialSum`-currency sibling of the head cell
`covGradConnDiffSection_perOrder_rfns_topSeparated`, in the shape the DLa 8-summand kernel triangle's
`A1` slot consumes. -/
private theorem exists_rfns_connDiffSection_topsep_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) +
          Kc j * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn,
    fun j => 2 * Kc0 j * (∑ k ∈ Finset.range j, Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)),
    fun j => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn j))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _) (Combinatorics.antidiagonalTupleGridCount_nonneg _)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have heng := hbot g₁ T htie hδ_le hδ0 hbound j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := heng.1
  have hrem := heng.2
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) := by
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
      (Hd.toSection x)
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x)
    have key :
        (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x =
          Hd.toSection x +
            (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x := by
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      abel
    rw [key]
    exact hadd
  have hrem2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 j * ((∑ k ∈ Finset.range j, Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        antidiagonalTupleGridPartialSum b (j + 2)) :=
    le_trans hrem (mul_le_mul_of_nonneg_left (engineRem_le_dLaGridWin b hb j) (hKc0_nn j))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x) := hsplit
    _ ≤ 2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x)) +
        2 * (Kc0 j * ((∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1)) * antidiagonalTupleGridPartialSum b (j + 2))) := by
          linarith [hhead, hrem2]
    _ = (2 * Kt0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) +
        (2 * Kc0 j * (∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) * Combinatorics.antidiagonalTupleGridCount (k + 1))) * antidiagonalTupleGridPartialSum b (j + 2) := by ring

/-- **Kernel top-separated bound.**  Top-separated twin of `exists_rfns_dLaKernelRaised_tgrid`:
the isolated `A1 = covGrad (connDiffSection g₁ g₀)` head is kept separate via the top-separated
connDiffSection bound (`R`-independent top coefficient `Ktop = 128·KtopA`), while the 7 lower
summands (`A2 = covGrad (connDiffSection g_bg g₀)` and the 6 quad terms) go entirely into the
`antidiagonalTupleGridPartialSum` remainder. -/
private theorem exists_rfns_dLaKernelRaised_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 3 i
              (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtopA, hKtopA_nn, KcA, hKcA_nn, hCAts⟩ :=
    exists_rfns_connDiffSection_topsep_dla (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  obtain ⟨cc, hcc_nn, hcc⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g_bg g₀)
  set CQ1 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ1_def
  set CQ2 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * cc i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ2_def
  set CQ3 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), cc l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ3_def
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hcc_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hcc_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨128 * KtopA, by positivity,
    fun i => 2 * (2 * (2 * (2 * (2 * (2 * (2 * KcA (i + 1) + 2 * cbg i) + 2 * CQ1 i)
      + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have h1 := hKcA_nn (i + 1)
      have h2 := hcbg_nn i
      have h3 := hCQ1_nn i
      have h4 := hCQ2_nn i
      have h5 := hCQ3_nn i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hW_ge1 : 1 ≤ W := one_le_dLaGridWin b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * antidiagonalTupleGridPartialSum b (i' + 2) :=
    fun i' _ => hCA g₁ T htie hδ_le hδ0 hbound i' x
  have hfix : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      cc i' * antidiagonalTupleGridPartialSum b (i' + 2) := by
    intro i' _
    refine le_trans (hcc i' x) ?_
    have h1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (i' + 2) := one_le_dLaGridWin b hb (by omega)
    nlinarith [hcc_nn i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g₁ i x b hb CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g_bg g₁ i x b hb cc CA hcc_nn hCA_nn hfix harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g_bg i x b hb CA cc hCA_nn hcc_nn harm hfix
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (F : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i F).toSection x) := by
    intro σ F
    exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ F
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      KtopA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
      KcA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    exact hCAts g₁ T htie hδ_le hδ0 hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))).toSection x) ≤
      cbg i * W := by
    refine le_trans (hcbg i x) ?_
    nlinarith [hcbg_nn i]
  set A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) with hA1_def
  set A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀) with hA2_def
  set Q11 := dLaQuadCc (I := I) (M := M) g₀ g₁ g₁ with hQ11_def
  set Qbg1 := dLaQuadCc (I := I) (M := M) g₀ g_bg g₁ with hQbg1_def
  set Q1bg := dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg with hQ1bg_def
  set P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
    with hP1_def
  set P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
    with hP2_def
  set P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11 with hP3_def
  set P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg with hP4_def
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le,
    mul_assoc (128 : ℝ) KtopA (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))]

/-! ### Piece 4 — field-level lift of the DLa top-separated bound. -/


/-- Pure-real grid split: pull the `(i'=0, l=i)` top cell out of the ccOperatorFieldComp product grid. -/
private lemma gridSplit_dla (G cΦ0 τ Wtop Wrem gridB : ℝ) (i : ℕ) (pΦ qW : ℕ → ℝ)
    (hG_nn : 0 ≤ G) (hcΦ0 : 0 ≤ cΦ0) (hpΦ_nn : ∀ i', 0 ≤ pΦ i') (hqW_nn : ∀ l, 0 ≤ qW l)
    (hΦ0 : pΦ 0 ≤ cΦ0) (hWi : qW i ≤ Wtop * τ + Wrem)
    (hfull : G * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤ gridB) :
    G * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      G * cΦ0 * Wtop * τ + (G * cΦ0 * Wrem + gridB) := by
  classical
  have hqi_le_S0 : qW i ≤ ∑ l ∈ Finset.range (i + 1 - 0), qW l :=
    Finset.single_le_sum (f := qW) (fun l _ => hqW_nn l) (by rw [Finset.mem_range]; omega)
  have hpq_le : pΦ 0 * qW i ≤
      ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l := by
    calc pΦ 0 * qW i
        ≤ pΦ 0 * ∑ l ∈ Finset.range (i + 1 - 0), qW l :=
          mul_le_mul_of_nonneg_left hqi_le_S0 (hpΦ_nn 0)
      _ ≤ ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l :=
          Finset.single_le_sum
            (f := fun i' => pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l)
            (fun i' _ => mul_nonneg (hpΦ_nn i') (Finset.sum_nonneg fun l _ => hqW_nn l))
            (by rw [Finset.mem_range]; omega)
  have hcell : G * (pΦ 0 * qW i) ≤ G * (cΦ0 * (Wtop * τ + Wrem)) := by
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    calc pΦ 0 * qW i
        ≤ cΦ0 * qW i := mul_le_mul_of_nonneg_right hΦ0 (hqW_nn i)
      _ ≤ cΦ0 * (Wtop * τ + Wrem) := mul_le_mul_of_nonneg_left hWi hcΦ0
  have hrest : G * ((∑ i' ∈ Finset.range (i + 1),
      pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l) - pΦ 0 * qW i) ≤ gridB :=
    le_trans (mul_le_mul_of_nonneg_left
      (by linarith [mul_nonneg (hpΦ_nn 0) (hqW_nn i)]) hG_nn) hfull
  calc G * ∑ i' ∈ Finset.range (i + 1), pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l
      = G * (pΦ 0 * qW i) +
          G * ((∑ i' ∈ Finset.range (i + 1),
            pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l) - pΦ 0 * qW i) := by ring
    _ ≤ G * (cΦ0 * (Wtop * τ + Wrem)) + gridB := add_le_add hcell hrest
    _ = G * cΦ0 * Wtop * τ + (G * cΦ0 * Wrem + gridB) := by ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- Shared ccOperatorFieldComp full-grid bound (`hfull` producer for both DLa extractions;
both use window shape `(i'+1)(l+3) → (i+3)`). -/
private lemma appCcGrid_le_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ)
    (pΦ cΦ qW cW : ℕ → ℝ)
    (hqW_nn : ∀ l, 0 ≤ qW l) (hcΦ_nn : ∀ i', 0 ≤ cΦ i') (hcW_nn : ∀ l, 0 ≤ cW l)
    (hΦ : ∀ i', i' ≤ i → pΦ i' ≤ cΦ i' * antidiagonalTupleGridPartialSum b (i' + 1))
    (hW : ∀ l, l ≤ i → qW l ≤ cW l * antidiagonalTupleGridPartialSum b (l + 3)) :
    diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      (diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * antidiagonalTuplePairCount (i' + 1) (l + 3)) *
        antidiagonalTupleGridPartialSum b (i + 3) := by
  classical
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l ≤
      (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * antidiagonalTuplePairCount (i' + 1) (l + 3)) *
        antidiagonalTupleGridPartialSum b (i + 3) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hi'_le : i' ≤ i := by omega
    have hA1 : pΦ i' ≤ cΦ i' * antidiagonalTupleGridPartialSum b (i' + 1) := hΦ i' hi'_le
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'), qW l) ≤
        ∑ l ∈ Finset.range (i + 1 - i'), cW l * antidiagonalTupleGridPartialSum b (l + 3) :=
      Finset.sum_le_sum fun l hl => hW l (by rw [Finset.mem_range] at hl; omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'), qW l :=
      Finset.sum_nonneg fun l _ => hqW_nn l
    have hA1_rhs_nn : 0 ≤ cΦ i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      mul_nonneg (hcΦ_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'),
        cW l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * antidiagonalTupleGridPartialSum b (i + 3) =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (cΦ i' * (cW l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * antidiagonalTupleGridPartialSum b (i + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3) ≤
        antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc cΦ i' * antidiagonalTupleGridPartialSum b (i' + 1) * (cW l * antidiagonalTupleGridPartialSum b (l + 3))
        = (cΦ i' * cW l) * (antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3)) := by ring
      _ ≤ (cΦ i' * cW l) * (antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3)) :=
          mul_le_mul_of_nonneg_left hpair (mul_nonneg (hcΦ_nn i') (hcW_nn l))
      _ = (cΦ i' * (cW l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * antidiagonalTupleGridPartialSum b (i + 3) := by ring
  calc diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
        pΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), qW l
      ≤ diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
          (cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * antidiagonalTuplePairCount (i' + 1) (l + 3)) *
            antidiagonalTupleGridPartialSum b (i + 3) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
    _ = (diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
          cΦ i' * ∑ l ∈ Finset.range (i + 1 - i'), cW l * antidiagonalTuplePairCount (i' + 1) (l + 3)) *
          antidiagonalTupleGridPartialSum b (i + 3) := by
        rw [← Finset.sum_mul, ← mul_assoc]

/-- **dLaLoweredCc top-separated.**  Raise-eq bridge into the kernel top-separation (piece 3).
`R`-independent top coefficient (`= 256·Kt0`). -/
private theorem exists_rfns_dLaLowered_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hker⟩ :=
    exists_rfns_dLaKernelRaised_topsep (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨Ktop, hKtop_nn, Kc, hKc_nn, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [dLaLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hker g₁ T htie hδ_le hδ0 hbound i x

-- The top-separated coefficient assembly requires additional elaboration budget.
/-- **dLaSymCc top-separated.**  Exported top coefficient `Ktop_sym` is a FIXED `R`-free real;
the `diagonalGridGrowthFactor i` power is explicit so the summed layer fixes one constant via
`diagonalGridGrowthFactor i ≤ diagonalGridGrowthFactor a`. -/
private theorem exists_rfns_dLaSym_topsep (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
          Ktop * diagonalGridGrowthFactor (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨KtopL, hKtopL_nn, KcL, hKcL_nn, hL⟩ :=
    exists_rfns_dLaLowered_topsep (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CL, hCL_nn, hCL⟩ := exists_rfns_dLaLowered_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set cPer : ℝ := fr ^ 5 * δ₀ ^ 2 with hcPer_def
  have hcPer_nn : 0 ≤ cPer := by rw [hcPer_def]; positivity
  set CP : ℕ → ℝ := fun _ => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) with hCP_def
  have hCP_nn : ∀ i', 0 ≤ CP i' := fun i' => by rw [hCP_def]; positivity
  set CLT : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTuplePairCount (i' + 1) (l + 3) with hCLT_def
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCP_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hCL_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨8 * KtopL * (1 + cPer),
      mul_nonneg (mul_nonneg (by norm_num) hKtopL_nn) (by positivity),
    fun i => 8 * KcL i + 8 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 8 * CLT i,
    fun i => by
      have h1 := hKcL_nn i; have h2 := hCLT_nn i; have h3 := appCcGdiag_nonneg (E := E) i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hτ_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _
  have happ_nn : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  have happ_ge1 : (1 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := by
    rw [diagonalGridGrowthFactor]
    exact one_le_pow₀ (by
      have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      linarith)
  -- perturb slotInsert Φ-per-order (`CP i'` constant, R-free), for `hfull`.
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * antidiagonalTupleGridPartialSum b (i' + 1) := by
    intro i' _
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T i' x) ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
        have hwin1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (0 + 1) := one_le_dLaGridWin b hb (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 :=
          le_trans h0 (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn; linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * antidiagonalTupleGridPartialSum b (0 + 1) :=
              le_mul_of_one_le_right (by positivity) hwin1
          _ = CP 0 * antidiagonalTupleGridPartialSum b (0 + 1) := by rw [hCP_def]
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          rfns_iCG_symmS_le_dla (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          single_le_grid_dla b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            antidiagonalTupleGridPartialSum b ((m + 1) + 1) := grid_le_dLaGridWin b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 := le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ antidiagonalTupleGridPartialSum b ((m + 1) + 1) := dLaGridWin_nonneg b hb _
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * antidiagonalTupleGridPartialSum b ((m + 1) + 1) :=
              mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 h3)) hfr3_nn
          _ ≤ CP (m + 1) * antidiagonalTupleGridPartialSum b ((m + 1) + 1) := by
              rw [hCP_def]
              refine mul_le_mul_of_nonneg_right ?_ hwin_nn
              calc fr ^ 3 = fr ^ 3 * 1 := by ring
                _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  -- perturb order-0 (`cPer`), for the top cell.
  have hPer0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + 0) x
      ((iteratedCovGrad (I := I) g₀ 4 4 0
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤ cPer := by
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T 0 x) ?_
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
        fr ^ 2 * δ ^ 2 := by
      rw [iteratedCovGrad_zero]
      exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
    have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
    rw [hcPer_def]
    calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
        ≤ fr ^ 3 * (fr ^ 2 * δ ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδsq (by positivity))
            (by positivity)
      _ = fr ^ 5 * δ₀ ^ 2 := by ring
  -- perturb top-separated.
  have hPer : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) i * cPer * KtopL *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (diagonalGridGrowthFactor (E := E) i * cPer * (KcL i * W) + CLT i * W) := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    exact gridSplit_dla (diagonalGridGrowthFactor (E := E) i) cPer
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))
      KtopL (KcL i * W) (CLT i * W) i
      (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      happ_nn hcPer_nn
      (fun i' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 (4 + i') x _)
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
      hPer0 (hL g₁ T htie hδ_le hδ0 hbound i x)
      (le_trans (appCcGrid_le_dla b hb i
        (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
              (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x))
        CP
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        CL
        (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
        hCP_nn hCL_nn hPfac (fun l _ => hCL g₁ T htie hδ_le hδ0 hbound l x))
        (le_of_eq (by rw [hCLT_def, hW_def])))
  -- G1 = dLaLoweredCc + dLaLoweredPerturbCc.
  have hG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      (2 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (2 * KcL i + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 2 * CLT i) * W := by
    refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
    have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        KtopL * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcL i * W :=
      hL g₁ T htie hδ_le hδ0 hbound i x
    have htoplift : 2 * KtopL + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KtopL ≤
        (2 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i := by
      have hkey : (0 : ℝ) ≤ KtopL * (diagonalGridGrowthFactor (E := E) i - 1) :=
        mul_nonneg hKtopL_nn (by linarith [happ_ge1])
      nlinarith [hkey, hcPer_nn, hKtopL_nn]
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
        ≤ 2 * (KtopL * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcL i * W) +
            2 * (diagonalGridGrowthFactor (E := E) i * cPer * KtopL *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
                (diagonalGridGrowthFactor (E := E) i * cPer * (KcL i * W) + CLT i * W)) := by
          linarith [hL0, hPer]
      _ = (2 * KtopL + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KtopL) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 2 * CLT i) * W := by ring
      _ ≤ (2 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 2 * CLT i) * W :=
          add_le_add (mul_le_mul_of_nonneg_right htoplift hτ_nn) (le_refl _)
  -- sym = domDomCongr(swap 0 1)(G1) + G1.
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
  rw [hperm]
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
      ≤ 2 * ((2 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 2 * CLT i) * W) +
        2 * ((2 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          (2 * KcL i + 2 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 2 * CLT i) * W) := by
        linarith [hG1]
    _ = (8 * KtopL * (1 + cPer)) * diagonalGridGrowthFactor (E := E) i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        (8 * KcL i + 8 * diagonalGridGrowthFactor (E := E) i * cPer * KcL i + 8 * CLT i) * W := by ring


-- The nested coefficient-field extraction requires additional elaboration budget.
/-- **Field pointwise top-separated bound** for `deTurckLieConnDiffDerivCoeffField`.  Exported base top
coefficient `Ktop` is `R`-free; the `diagonalGridGrowthFactor i` powers are explicit (the field carries TWO
nested ccOperatorFieldComp extractions, so `(diagonalGridGrowthFactor i)²`). -/
theorem riemannianFiberNormSq_iteratedCovGrad_deTurckLieConnDiffDerivCoeffField_topSeparated_le (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Ktop * diagonalGridGrowthFactor (E := E) i * diagonalGridGrowthFactor (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          Kc i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := exists_rfns_pairTraceOpDla_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtopS, hKtopS_nn, KcS, hKcS_nn, hSym⟩ :=
    exists_rfns_dLaSym_topsep (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := exists_rfns_dLaSym_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set Cfield : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CPT i' * ∑ l ∈ Finset.range (i + 1 - i'), (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3)
    with hCfield_def
  have hCfield_nn : ∀ i, 0 ≤ Cfield i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCPT_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (dLaPairCount_nonneg _ _))
  refine ⟨CPT 0 * fr ^ 2 * KtopS,
      mul_nonneg (mul_nonneg (hCPT_nn 0) (by positivity)) hKtopS_nn,
    fun i => diagonalGridGrowthFactor (E := E) i * CPT 0 * fr ^ 2 * KcS i + Cfield i,
    fun i => by
      have h1 := hKcS_nn i; have h2 := hCfield_nn i; have h3 := appCcGdiag_nonneg (E := E) i
      have h4 := hCPT_nn 0
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have happ_nn : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  -- X-tower reduction `rfns(∇^l X) ≤ fr²·rfns(∇^l dLaSymCc)`.
  have hXfr : ∀ l, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) := by
    intro l
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) l x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ = fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) := by ring
  -- pairTrace order-0 for the top cell.
  have hPT0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + 0) x
      ((iteratedCovGrad (I := I) g₀ 6 2 0 (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CPT 0 := by
    have h := hCPT g₁ T htie hδ_le hδ0 hbound 0 x
    rwa [show antidiagonalTupleGridPartialSum b (0 + 1) = 1 from by
          rw [antidiagonalTupleGridPartialSum, Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero],
        mul_one] at h
  -- top cell (via X-tower at `l = i` + dLaSym top-sep).
  have hWi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr ^ 2 * KtopS * diagonalGridGrowthFactor (E := E) i) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
        fr ^ 2 * KcS i * W := by
    refine le_trans (hXfr i) ?_
    have hs := hSym g₁ T htie hδ_le hδ0 hbound i x
    calc fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
        ≤ fr ^ 2 * (KtopS * diagonalGridGrowthFactor (E := E) i *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + KcS i * W) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (fr ^ 2 * KtopS * diagonalGridGrowthFactor (E := E) i) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) + fr ^ 2 * KcS i * W := by
          ring
  -- field ↔ ccOperatorFieldComp lift.
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [deTurckLieDLaCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iteratedCovGrad_smul_dla]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_dla (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) x) ?_
  refine le_trans (gridSplit_dla (diagonalGridGrowthFactor (E := E) i) (CPT 0)
    (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))
    (fr ^ 2 * KtopS * diagonalGridGrowthFactor (E := E) i) (fr ^ 2 * KcS i * W) (Cfield i * W) i
    (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
      ((iteratedCovGrad (I := I) g₀ 6 2 i' (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x))
    (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 6 l
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x))
    happ_nn (hCPT_nn 0)
    (fun i' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (2 + i') x _)
    (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
    hPT0 hWi
    (le_trans (appCcGrid_le_dla b hb i
      (fun i' => riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i' (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x))
      CPT
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x))
      (fun l => fr * (fr * CX l))
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
      hCPT_nn (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      (fun i' _ => hCPT g₁ T htie hδ_le hδ0 hbound i' x)
      (fun l _ => le_trans (hXfr l)
        (by
          have := hCX g₁ T htie hδ_le hδ0 hbound l x
          calc fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)
              ≤ fr ^ 2 * (CX l * antidiagonalTupleGridPartialSum b (l + 3)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by ring)))
      (le_of_eq (by rw [hCfield_def, hW_def])))) ?_
  exact le_of_eq (by ring)

/-! ### Summation helpers (copied verbatim from `DLaTopSeparated`). -/

end DLaGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
