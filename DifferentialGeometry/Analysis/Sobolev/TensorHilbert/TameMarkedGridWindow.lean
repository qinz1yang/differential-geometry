import DifferentialGeometry.Analysis.Sobolev.MarkedTupleGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.TameGridProd
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GagliardoNirenbergTwoAnchor

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def HasMarkedGridWindow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) (u : ℕ) (K : ℕ → ℝ) : Prop :=
  ∀ (i : ℕ) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
      K i * Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u i

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma mkWnn (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (u i : ℕ) :
    (0 : ℝ) ≤ Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u i :=
  Combinatorics.markGrid_nn _ (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x) u i

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma mkW1 (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (x : M) (i : ℕ) :
    (1 : ℝ) ≤ Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) 0 i :=
  Combinatorics.one_le_markGrid0 _ (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x) i

omit [SigmaCompactSpace M] in
theorem markedGridWindow_operatorFieldComposition_bound (g₀ : SmoothRiemannianMetric I M) {p a b : ℕ} (u v : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    (P : SmoothCcTensor g₀ 0 2) {KΦ KW : ℕ → ℝ}
    (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : ∀ (i' : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
          ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) ≤
        KΦ i' * Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u i')
    (hW : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
          ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
        KW l * Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) v l)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + n) x
        ((iteratedCovGrad (I := I) g₀ p b n
          (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)).toSection x) ≤
      operatorFieldCompositionGridConstant (E := E) 0 0 KΦ KW n *
        Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (u + v) n := by
  classical
  set bP : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hbP_def
  have hbP : ∀ j, 0 ≤ bP j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hmkn : 0 ≤ Combinatorics.markGrid bP (u + v) n :=
    Combinatorics.markGrid_nn bP hbP _ _
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ n p a b Φ W x) ?_
  rw [operatorFieldCompositionGridConstant, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) n)
  have hterm : ∀ i' ∈ Finset.range (n + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
          ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
        ∑ l ∈ Finset.range (n + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
            ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
      ∑ l ∈ Finset.range (n + 1),
        (KΦ i' * KW l *
          Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 0) (l + 0)) *
          Combinatorics.markGrid bP (u + v) n := by
    intro i' hi'
    have hi'n : i' ≤ n := by rw [Finset.mem_range] at hi'; omega
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun l hl => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun l _ _ => ?_))
    swap
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hKΦ i') (hKW l))
        (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)) hmkn
    · have hln : l ≤ n - i' := by
        rw [Finset.mem_range] at hl; omega
      have hmul := Combinatorics.markGrid_mul bP hbP u v i' l
      have hmono := Combinatorics.markGrid_mono bP hbP (u + v)
        (show i' + l ≤ n by omega)
      have hwc_nn : 0 ≤ Combinatorics.antidiagonalTupleGridWindowMulConst i' l :=
        Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _
      have hprod :
          riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
              ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x) ≤
          (KΦ i' * Combinatorics.markGrid bP u i') *
            (KW l * Combinatorics.markGrid bP v l) :=
        mul_le_mul (hΦ i' x) (hW l x) (riemannianFiberNormSq_nonneg _ _ _ _ _)
          (mul_nonneg (hKΦ i') (Combinatorics.markGrid_nn bP hbP _ _))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
              ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x)
          ≤ (KΦ i' * Combinatorics.markGrid bP u i') *
              (KW l * Combinatorics.markGrid bP v l) := hprod
        _ = KΦ i' * KW l *
              (Combinatorics.markGrid bP u i' * Combinatorics.markGrid bP v l) := by ring
        _ ≤ KΦ i' * KW l *
              (Combinatorics.antidiagonalTupleGridWindowMulConst i' l *
                Combinatorics.markGrid bP (u + v) (i' + l)) :=
            mul_le_mul_of_nonneg_left hmul (mul_nonneg (hKΦ i') (hKW l))
        _ ≤ KΦ i' * KW l *
              (Combinatorics.antidiagonalTupleGridWindowMulConst i' l *
                Combinatorics.markGrid bP (u + v) n) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hKΦ i') (hKW l))
            exact mul_le_mul_of_nonneg_left hmono hwc_nn
        _ = (KΦ i' * KW l *
              Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 0) (l + 0)) *
              Combinatorics.markGrid bP (u + v) n := by
            simp only [Nat.add_zero]; ring
  calc ∑ i' ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + i') x
            ((iteratedCovGrad (I := I) g₀ a b i' Φ).toSection x) *
          ∑ l ∈ Finset.range (n + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
              ((iteratedCovGrad (I := I) g₀ p a l W).toSection x)
      ≤ ∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (KΦ i' * KW l *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 0) (l + 0)) *
            Combinatorics.markGrid bP (u + v) n :=
        Finset.sum_le_sum hterm
    _ = (∑ i' ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          KΦ i' * KW l *
            Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 0) (l + 0)) *
          Combinatorics.markGrid bP (u + v) n := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i' _ => by rw [Finset.sum_mul])

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_of_pointwise_bound (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {S : ℕ → ℝ} (hS : ∀ i, 0 ≤ S i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤ S i) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P X 0 S := by
  intro i x
  exact le_trans (hX i x)
    (le_mul_of_one_le_right (hS i) (mkW1 (I := I) (M := M) g₀ P x i))

omit [BoundarylessManifold I M] [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ}
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        K i * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P X 0 K := hX

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasMarkedGridWindow_base (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P P 0 (fun _ => 1) := by
  intro i x
  set b : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ j, 0 ≤ b j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hgoal : b i ≤ Combinatorics.markGrid b 0 i := by
    match i with
    | 0 =>
        rw [Combinatorics.markGrid_zero, Combinatorics.antidiagonalTupleGridWindow,
          Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero]
        exact hP0 x
    | (k + 1) =>
        refine le_trans ?_ (Combinatorics.antidiagonalTupleGrid_le_window b hb
          (k := k + 1) (w := k + 1 + 1) (by omega))
        have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (k + 1)
          (by omega)
        rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one, Nat.zero_add] at h
  rw [one_mul]
  exact hgoal

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_covariantDerivative_base (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (covGrad (I := I) (M := M) g₀ 0 2 P) 1
      (fun _ => 1) := by
  intro i x
  set b : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ j, 0 ≤ b j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i P x, one_mul]
  have h := Combinatorics.markOne_of_term b hb (j := i) (c := i) (k := 0) (by omega)
  rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasMarkedGridWindow_of_top_order_decomposition (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {Ktop : ℝ} (hKtop : 0 ≤ Ktop)
    {Kc : ℕ → ℝ} (hKc : ∀ i, 0 ≤ Kc i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        Ktop * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (i + 1) +
          Kc i * ∑ k ∈ Finset.range i,
            covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (i - k) *
              Combinatorics.antidiagonalTupleGrid
                (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (k + 1)) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P X 1 (fun i => Ktop + Kc i * i) := by
  intro i x
  classical
  set b : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ j, 0 ≤ b j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  set W : ℝ := Combinatorics.markGrid b 1 i with hW_def
  have hWnn : 0 ≤ W := Combinatorics.markGrid_nn b hb 1 i
  have htop : b (i + 1) ≤ W := by
    have h := Combinatorics.markOne_of_term b hb (j := i) (c := i) (k := 0) (by omega)
    rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  have hres : ∀ k ∈ Finset.range i,
      b (i - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤ W := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hidx : i - k - 1 + 1 = i - k := by omega
    have h := Combinatorics.markOne_of_term b hb (j := i) (c := i - k - 1) (k := k + 1)
      (by omega)
    rwa [hidx] at h
  have hsum : (∑ k ∈ Finset.range i,
      b (i - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) ≤ (i : ℝ) * W := by
    calc (∑ k ∈ Finset.range i, b (i - k) * Combinatorics.antidiagonalTupleGrid b (k + 1))
        ≤ ∑ _k ∈ Finset.range i, W := Finset.sum_le_sum hres
      _ = (i : ℝ) * W := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans (hX i x) ?_
  have h1 : Ktop * b (i + 1) ≤ Ktop * W := mul_le_mul_of_nonneg_left htop hKtop
  have h2 : Kc i * (∑ k ∈ Finset.range i,
      b (i - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) ≤
      Kc i * ((i : ℝ) * W) := mul_le_mul_of_nonneg_left hsum (hKc i)
  have hgoal : Ktop * W + Kc i * ((i : ℝ) * W) = (Ktop + Kc i * i) * W := by ring
  linarith only [h1, h2, hgoal.le, hgoal.ge]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasMarkedGridWindow_of_antidiagonalTupleGrid_bound (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1)
    {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ} (hK : ∀ i, 0 ≤ K i)
    (hX : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) ≤
        K i * Combinatorics.antidiagonalTupleGrid
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P X 1
      (fun i => K i * Combinatorics.antidiagonalTupleGridCount (i + 1)) := by
  intro i x
  set b : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  have hb : ∀ j, 0 ≤ b j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  refine le_trans (hX i x) ?_
  have hstep := Combinatorics.atgLeMark1 b hb (hP0 x) i
  calc K i * Combinatorics.antidiagonalTupleGrid b (i + 1)
      ≤ K i * (Combinatorics.antidiagonalTupleGridCount (i + 1) *
          Combinatorics.markGrid b 1 i) := mul_le_mul_of_nonneg_left hstep (hK i)
    _ = (K i * Combinatorics.antidiagonalTupleGridCount (i + 1)) *
          Combinatorics.markGrid b 1 i := by ring

omit [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_operatorFieldComp (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {p a b : ℕ} (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    {u v : ℕ} {KΦ KW : ℕ → ℝ} (hKΦ : ∀ i, 0 ≤ KΦ i) (hKW : ∀ l, 0 ≤ KW l)
    (hΦ : HasMarkedGridWindow (I := I) (M := M) g₀ P Φ u KΦ)
    (hW : HasMarkedGridWindow (I := I) (M := M) g₀ P W v KW) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)
      (u + v) (operatorFieldCompositionGridConstant (E := E) 0 0 KΦ KW) := by
  intro n x
  exact markedGridWindow_operatorFieldComposition_bound (I := I) (M := M) g₀ u v Φ W P hKΦ hKW hΦ hW n x

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_mono (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K K' : ℕ → ℝ}
    (hKK : ∀ i, K i ≤ K' i) (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P X u K' := by
  intro i x
  exact le_trans (hX i x)
    (mul_le_mul_of_nonneg_right (hKK i) (mkWnn (I := I) (M := M) g₀ P x u i))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M]
    [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_congr (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X Y : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (hXY : Y = X)
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P Y u K := by
  rw [hXY]; exact hX

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_add (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u KX)
    (hY : HasMarkedGridWindow (I := I) (M := M) g₀ P Y u KY) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (X + Y) u (fun i => 2 * KX i + 2 * KY i) := by
  intro i x
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (X + Y)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
          ((iteratedCovGrad (I := I) g₀ r c i Y).toSection x) := by
    rw [iteratedCovGrad_add (I := I) g₀ r c i X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r (c + i) x _ _
  refine hsplit.trans ?_
  have h1 := hX i x
  have h2 := hY i x
  nlinarith [h1, h2, mkWnn (I := I) (M := M) g₀ P x u i]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_smul (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (t : ℝ)
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (t • X) u (fun i => t ^ 2 * K i) := by
  intro i x
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i (t • X)).toSection x) =
      t ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ r (c + i) x
        ((iteratedCovGrad (I := I) g₀ r c i X).toSection x) := by
    rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g₀ r c i t X,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ r (c + i) x t _]
  rw [heq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) (sq_nonneg t)

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_neg (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (-X) u K := by
  have hneg : (-X) = (-1 : ℝ) • X := by rw [neg_smul, one_smul]
  rw [hneg]
  refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P (fun i => ?_)
    (hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (-1 : ℝ) hX)
  norm_num

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hasMarkedGridWindow_sub (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X Y : SmoothCcTensor g₀ r c} {KX KY : ℕ → ℝ}
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u KX)
    (hY : HasMarkedGridWindow (I := I) (M := M) g₀ P Y u KY) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (X - Y) u (fun i => 2 * KX i + 2 * KY i) := by
  have h := hasMarkedGridWindow_add (I := I) (M := M) g₀ P hX (hasMarkedGridWindow_neg (I := I) (M := M) g₀ P hY)
  rwa [← sub_eq_add_neg] at h

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasMarkedGridWindow_reindex (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (ρ : Equiv.Perm (Fin r))
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P
      (reindexCoeffGen (I := I) (M := M) g₀ r c X ρ) u K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r c X ρ i x]
  exact hX i x

omit [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_domainReindex (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P
      (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X) u K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r c σ X
    (rsDomDomCongrSection (I := I) (M := M) g₀ r c σ X)
    (fun y d => by rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x]
  exact hX i x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_covariantDomainReindex (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {c u : ℕ} {X : SmoothCcTensor g₀ 0 c} {K : ℕ → ℝ} (σ : Equiv.Perm (Fin c))
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (domDomCongrSection (I := I) g₀ σ X) u K := by
  intro i x
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ X i x]
  exact hX i x

omit [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_slotExtend (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ}
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (slotExtend (I := I) (M := M) g₀ r c X) u
      (fun i => (Module.finrank ℝ E : ℝ) * K i) := by
  intro i x
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r c X i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hX i x) hfr

omit [SigmaCompactSpace M] in
theorem hasMarkedGridWindow_slotExtendIter (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {r c u : ℕ} {X : SmoothCcTensor g₀ r c} {K : ℕ → ℝ} (w : ℕ)
    (hX : HasMarkedGridWindow (I := I) (M := M) g₀ P X u K) :
    HasMarkedGridWindow (I := I) (M := M) g₀ P (slotExtendIter (I := I) (M := M) g₀ r c w X) u
      (fun i => (Module.finrank ℝ E : ℝ) ^ w * K i) := by
  induction w with
  | zero =>
      have hzero : slotExtendIter (I := I) (M := M) g₀ r c 0 X = X := by
        rfl
      rw [hzero]
      simpa only [pow_zero, one_mul] using hX
  | succ w ih =>
      have hrec : slotExtendIter (I := I) (M := M) g₀ r c (w + 1) X =
          slotExtend (I := I) (M := M) g₀ (r + w) (c + w)
            (slotExtendIter (I := I) (M := M) g₀ r c w X) := rfl
      have h := hasMarkedGridWindow_slotExtend (I := I) (M := M) g₀ P ih
      rw [← hrec] at h
      refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P (fun i => ?_) h
      simp only [pow_succ]
      ring_nf
      exact le_of_eq rfl

theorem exists_markedGridWindow_highOrder_integral_bound (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (m c₁ c₂ k n : ℕ) (e : Fin n → ℕ), 2 ≤ c₁ → 2 ≤ c₂ → 1 ≤ k → n ≤ k →
          (∑ q, e q) = k → (∀ q, e q ≠ 1) → c₁ + c₂ + k = m + 1 →
          (∫ x, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ *
                covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
                ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K m * (1 + Λ₁ ^ 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2 := by
  classical
  obtain ⟨K, hK0, hK⟩ := Integral.Connection.gnProdJet (I := I) (M := M) g₀ 0 2
  refine ⟨K, hK0, ?_⟩
  intro P Λ₀ Λ₁ hΛ₀0 hΛ₀1 hΛ₁0 hsup0 hsup1 m c₁ c₂ k n e hc₁ hc₂ hk1 hnk he hne hsum
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin (n + 2) → ℕ, cc = Fin.cons c₁ (Fin.cons c₂ e) := ⟨_, rfl⟩
  have hcc0 : cc 0 = c₁ := by rw [hcc]; simp
  have hcc1 : cc (Fin.succ 0) = c₂ := by rw [hcc]; simp
  have hccne1 : ∀ j : Fin (n + 2), cc j ≠ 1 := by
    intro j
    rw [hcc]
    induction j using Fin.cases with
    | zero => simp only [Fin.cons_zero]; omega
    | succ i =>
        simp only [Fin.cons_succ]
        induction i using Fin.cases with
        | zero => simp only [Fin.cons_zero]; omega
        | succ q => simp only [Fin.cons_succ]; exact hne q
  have hccsum : ∑ j : Fin (n + 2), cc j = c₁ + c₂ + k := by
    simp only [hcc, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [he]; omega
  obtain ⟨t, htdef⟩ : ∃ t : Finset (Fin (n + 2)),
      t = Finset.univ.filter (fun j => cc j ≠ 0) := ⟨_, rfl⟩
  have hmemt : ∀ j : Fin (n + 2), j ∈ t ↔ cc j ≠ 0 := by
    intro j; rw [htdef]; simp
  have hc2t : ∀ j ∈ t, 2 ≤ cc j := by
    intro j hj
    have h0 := (hmemt j).mp hj
    have h1 := hccne1 j
    omega
  have hc0t : ∀ j : Fin (n + 2), j ∉ t → cc j = 0 := by
    intro j hj
    by_contra h
    exact hj ((hmemt j).mpr h)
  have hQ2 : 2 ≤ t.card := by
    have hsub : ({0, Fin.succ 0} : Finset (Fin (n + 2))) ⊆ t := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact (hmemt _).mpr (by rw [hcc0]; omega)
      · exact (hmemt _).mpr (by rw [hcc1]; omega)
    have hcard : ({0, Fin.succ 0} : Finset (Fin (n + 2))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    calc (2 : ℕ) = ({0, Fin.succ 0} : Finset (Fin (n + 2))).card := hcard.symm
      _ ≤ t.card := Finset.card_le_card hsub
  have hsumt : ∑ j ∈ t, cc j = m + 1 := by
    rw [Finset.sum_subset (Finset.subset_univ t) (fun j _ hj => hc0t j hj), hccsum]
    exact hsum
  have hint : ∀ x : M,
      covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
          ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
        ∏ j : Fin (n + 2), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + cc j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (cc j) P).toSection x) := by
    intro x
    change _ = ∏ j : Fin (n + 2), covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (cc j)
    simp only [hcc, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring
  have hmain := hK P hΛ₀0 hΛ₀1 hΛ₁0 hsup0 hsup1 m (n + 2) cc t hc2t hc0t hQ2 hsumt
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint)]
  refine hmain.trans ?_
  have h1 : Λ₁ ^ 2 ≤ 1 + Λ₁ ^ 2 := by nlinarith [sq_nonneg Λ₁]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (hK0 m)) (sq_nonneg _)

private lemma leTame {c R K L J : ℝ} (hcKL : c ≤ K * L) (hKL0 : 0 ≤ K * L)
    (hR0 : 0 ≤ R) (hRJ : R ≤ J) : c * R ≤ K * L * J := by
  calc c * R ≤ K * L * R := mul_le_mul_of_nonneg_right hcKL hR0
    _ ≤ K * L * J := mul_le_mul_of_nonneg_left hRJ hKL0

theorem markedGridWindow_monomial_bound (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ (m c₁ c₂ k n : ℕ) (e : Fin n → ℕ), 1 ≤ c₁ → 1 ≤ c₂ → n ≤ k →
          (∑ q, e q) = k → c₁ + c₂ + k ≤ m + 1 →
          (∫ x, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ *
                covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
                ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            K m * (1 + Λ₁ ^ 2) *
              (1 + ∑ j ∈ Finset.range (m + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KU, hKU_nn, hU⟩ := gridIntUnit (I := I) (M := M) g₀ 0 2
  obtain ⟨KP, hKP_nn, hPull⟩ := gridIntPull (I := I) (M := M) g₀
  obtain ⟨KG, hKG_nn, hGrad⟩ := gridIntGrad (I := I) (M := M) g₀
  obtain ⟨KH, hKH_nn, hHigh⟩ := exists_markedGridWindow_highOrder_integral_bound (I := I) (M := M) g₀
  refine ⟨fun m => (∑ s ∈ Finset.range (m + 1), KU s) + KP m + KG m + KH m,
    fun m => by
      have h1 : (0 : ℝ) ≤ ∑ s ∈ Finset.range (m + 1), KU s :=
        Finset.sum_nonneg (fun s _ => hKU_nn s)
      have := hKP_nn m; have := hKG_nn m; have := hKH_nn m; linarith, ?_⟩
  intro P Λ₀ Λ₁ hΛ₀0 hΛ₀1 hΛ₁0 hsup hcap m c₁ c₂ k n e hc₁ hc₂ hnk he hsum
  set Kmon : ℝ := (∑ s ∈ Finset.range (m + 1), KU s) + KP m + KG m + KH m with hKmon_def
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (m + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hJS_def
  have hKUsum_nn : (0 : ℝ) ≤ ∑ s ∈ Finset.range (m + 1), KU s :=
    Finset.sum_nonneg (fun s _ => hKU_nn s)
  have hKmon_nn : (0 : ℝ) ≤ Kmon := by
    have := hKP_nn m; have := hKG_nn m; have := hKH_nn m
    simp only [hKmon_def]; linarith
  have hL1 : (1 : ℝ) ≤ 1 + Λ₁ ^ 2 := by nlinarith [sq_nonneg Λ₁]
  have hKL0 : (0 : ℝ) ≤ Kmon * (1 + Λ₁ ^ 2) := mul_nonneg hKmon_nn (by linarith)
  have hjet : ∀ s : ℕ, s ≤ m →
      ‖iteratedCovGrad (I := I) g₀ 0 2 s P‖ ^ 2 ≤ JS := by
    intro s hs
    have hmem : s ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem
    simp only [hJS_def]; linarith
  by_cases hlt : c₁ + c₂ + k ≤ m
  · set f : Fin (n + 2) → ℕ := Fin.cons c₁ (Fin.cons c₂ e) with hf_def
    have hfsum : (∑ q, f q) = c₁ + c₂ + k := by
      rw [hf_def, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [he]
      omega
    have hpt : ∀ x : M,
        covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
            ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
          ∏ q : Fin (n + 2), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + f q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (f q) P).toSection x) := by
      intro x
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
      rfl
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hres := hU P hΛ₀0 hΛ₀1 hsup (c₁ + c₂ + k) (by omega) (n + 2) (by omega) f hfsum
    refine le_trans hres (leTame ?_ hKL0 (sq_nonneg _) (hjet _ (by omega)))
    have hmem : c₁ + c₂ + k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := KU) (fun s _ => hKU_nn s) hmem
    have := hKP_nn m; have := hKG_nn m; have := hKH_nn m
    have hK : KU (c₁ + c₂ + k) ≤ Kmon := by simp only [hKmon_def]; linarith
    nlinarith [hK, hKmon_nn, hL1]
  · have htop : c₁ + c₂ + k = m + 1 := by omega
    have hm1 : 1 ≤ m := by omega
    by_cases h1 : c₁ = 1
    · subst h1
      set f : Fin (n + 1) → ℕ := Fin.cons c₂ e with hf_def
      have hfsum : (∑ q, f q) = m := by
        rw [hf_def, Fin.sum_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [he]; omega
      have hpt : ∀ x : M,
          covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
              ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
              ∏ q : Fin (n + 1), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + f q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (f q) P).toSection x) := by
        intro x
        rw [Fin.prod_univ_succ, mul_assoc]
        rfl
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have hres := hPull P hΛ₀0 hΛ₀1 hsup hcap m hm1 (n + 1) (by omega) f hfsum
      refine le_trans hres ?_
      have hrw : Λ₁ ^ 2 * (KP m * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2) =
          (Λ₁ ^ 2 * KP m) * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2 := by ring
      rw [hrw]
      refine leTame ?_ hKL0 (sq_nonneg _) (hjet m (le_refl _))
      have hKP : KP m ≤ Kmon := by
        have := hKG_nn m; have := hKH_nn m; simp only [hKmon_def]; linarith
      nlinarith [hKP, hKP_nn m, hKmon_nn, sq_nonneg Λ₁]
    · by_cases h2 : c₂ = 1
      · subst h2
        set f : Fin (n + 1) → ℕ := Fin.cons c₁ e with hf_def
        have hfsum : (∑ q, f q) = m := by
          rw [hf_def, Fin.sum_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]
          rw [he]; omega
        have hpt : ∀ x : M,
            covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 *
                ∏ q : Fin n, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
                ∏ q : Fin (n + 1), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + f q) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (f q) P).toSection x) := by
          intro x
          have hring : ∀ A B C : ℝ, A * B * C = B * (A * C) := by intros; ring
          rw [Fin.prod_univ_succ, hring]
          rfl
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
        have hres := hPull P hΛ₀0 hΛ₀1 hsup hcap m hm1 (n + 1) (by omega) f hfsum
        refine le_trans hres ?_
        have hrw : Λ₁ ^ 2 * (KP m * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2) =
            (Λ₁ ^ 2 * KP m) * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2 := by ring
        rw [hrw]
        refine leTame ?_ hKL0 (sq_nonneg _) (hjet m (le_refl _))
        have hKP : KP m ≤ Kmon := by
          have := hKG_nn m; have := hKH_nn m; simp only [hKmon_def]; linarith
        nlinarith [hKP, hKP_nn m, hKmon_nn, sq_nonneg Λ₁]
      · have hc₁2 : 2 ≤ c₁ := by omega
        have hc₂2 : 2 ≤ c₂ := by omega
        by_cases hk0 : k = 0
        · subst hk0
          have hn0 : n = 0 := by omega
          subst hn0
          have hpt : ∀ x : M,
              covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ * covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
                  ∏ q : Fin 0, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₁) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 c₁ P).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + c₂) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 c₂ P).toSection x) := by
            intro x
            rw [Fin.prod_univ_zero, mul_one]
            rfl
          rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
          have hres := hGrad P hΛ₁0 hcap m c₁ c₂ (by omega) (by omega) (by omega)
          refine le_trans hres ?_
          refine leTame ?_ hKL0 (sq_nonneg _) (hjet m (le_refl _))
          have hKG : KG m ≤ Kmon := by
            have := hKP_nn m; have := hKH_nn m; simp only [hKmon_def]; linarith
          nlinarith [hKG, hKG_nn m, hKmon_nn, sq_nonneg Λ₁]
        · have hk1 : 1 ≤ k := by omega
          by_cases hone : ∃ q : Fin n, e q = 1
          · obtain ⟨q₀, hq₀⟩ := hone
            have hnpos : 0 < n := by
              rcases Nat.eq_zero_or_pos n with h | h
              · exact absurd (q₀.isLt) (by omega)
              · exact h
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            set e' : Fin n' → ℕ := fun q => e (q₀.succAbove q) with he'_def
            have he'sum : (∑ q, e' q) = k - 1 := by
              have hs := Fin.sum_univ_succAbove e q₀
              rw [he, hq₀] at hs
              simp only [he'_def]
              omega
            set f : Fin (n' + 2) → ℕ := Fin.cons c₁ (Fin.cons c₂ e') with hf_def
            have hfsum : (∑ q, f q) = m := by
              rw [hf_def, Fin.sum_univ_succ, Fin.cons_zero]
              simp only [Fin.cons_succ]
              rw [Fin.sum_univ_succ, Fin.cons_zero]
              simp only [Fin.cons_succ]
              rw [he'sum]
              omega
            have hpt : ∀ x : M,
                covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₁ *
                    covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x c₂ *
                    ∏ q : Fin (n' + 1), covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) =
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) *
                    ∏ q : Fin (n' + 2),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + f q) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (f q) P).toSection x) := by
              intro x
              have hsplit := Fin.prod_univ_succAbove
                (fun q => covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q)) q₀
              have hring : ∀ A B C D : ℝ, A * B * (C * D) = C * (A * (B * D)) := by
                intros; ring
              rw [hsplit, hq₀, Fin.prod_univ_succ, Fin.prod_univ_succ, hring]
              rfl
            rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
            have hres := hPull P hΛ₀0 hΛ₀1 hsup hcap m hm1 (n' + 2) (by omega) f hfsum
            refine le_trans hres ?_
            have hrw : Λ₁ ^ 2 * (KP m * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2) =
                (Λ₁ ^ 2 * KP m) * ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ ^ 2 := by ring
            rw [hrw]
            refine leTame ?_ hKL0 (sq_nonneg _) (hjet m (le_refl _))
            have hKP : KP m ≤ Kmon := by
              have := hKG_nn m; have := hKH_nn m; simp only [hKmon_def]; linarith
            nlinarith [hKP, hKP_nn m, hKmon_nn, sq_nonneg Λ₁]
          · simp only [not_exists] at hone
            have hres := hHigh P hΛ₀0 hΛ₀1 hΛ₁0 hsup hcap m c₁ c₂ k n e
              hc₁2 hc₂2 hk1 hnk he hone htop
            refine le_trans hres ?_
            refine leTame ?_ hKL0 (sq_nonneg _) (hjet m (le_refl _))
            have hKH : KH m ≤ Kmon := by
              have := hKP_nn m; have := hKG_nn m; simp only [hKmon_def]; linarith
            nlinarith [hKH, hKH_nn m, hKmon_nn, sq_nonneg Λ₁]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M]
    [SigmaCompactSpace M] in
private lemma contGB (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (j : ℕ) : Continuous (fun x : M => covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x j) := by
  have hc : Continuous (fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    have h := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine h.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  exact hc

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M]
    [SigmaCompactSpace M] in
private lemma contGrid (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (k : ℕ) : Continuous (fun x : M =>
      Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) k) := by
  classical
  have heq : (fun x : M =>
        Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) k)
      = fun x : M => ∑ n' ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
            ∏ q : Fin n', covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (e q) := rfl
  rw [heq]
  exact continuous_finsetSum _ (fun n' _ => continuous_finsetSum _ (fun e _ =>
    continuous_finsetProd _ (fun q _ => contGB (I := I) (M := M) g₀ P (e q))))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M]
    [SigmaCompactSpace M] in
private lemma contMk (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (u w : ℕ) : Continuous (fun x : M =>
      Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u w) := by
  classical
  induction u generalizing w with
  | zero =>
      have heq : (fun x : M =>
            Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) 0 w)
          = fun x : M => ∑ k ∈ Finset.range (w + 1),
              Combinatorics.antidiagonalTupleGrid
                (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) k := rfl
      rw [heq]
      exact continuous_finsetSum _ (fun k _ => contGrid (I := I) (M := M) g₀ P k)
  | succ u ih =>
      have heq : (fun x : M =>
            Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (u + 1) w)
          = fun x : M => ∑ c ∈ Finset.range (w + 1),
              covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (c + 1) *
                Combinatorics.markGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) u (w - c) := rfl
      rw [heq]
      exact continuous_finsetSum _ (fun c _ =>
        (contGB (I := I) (M := M) g₀ P (c + 1)).mul (ih (w - c)))

theorem markedGridWindow_zeroOrder_jet_bound (g₀ : SmoothRiemannianMetric I M) :
    ∃ K0 : ℕ → ℝ, (∀ n, 0 ≤ K0 n) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1) →
        ∀ {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
          HasMarkedGridWindow (I := I) (M := M) g₀ P X 0 K →
          ∀ n : ℕ,
            ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
              K n * K0 n *
                (1 + ∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_covariant_jet_bound (I := I) (M := M) g₀ (Λ₀ := (1 : ℝ)) zero_le_one
  refine ⟨fun n => ∑ k ∈ Finset.range (n + 1), Kint k,
    fun n => Finset.sum_nonneg (fun k _ => hKint_nn k), ?_⟩
  intro P hP0 r c X K hK hX n
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have h := hint P hsup r c n 1 X (K n) (hK n)
    (fun x => by simpa using hX n x)
  refine h.trans ?_
  have hKK : 0 ≤ K n * ∑ k ∈ Finset.range (n + 1), Kint k :=
    mul_nonneg (hK n) (Finset.sum_nonneg (fun k _ => hKint_nn k))
  refine mul_le_mul_of_nonneg_left ?_ hKK
  have hmono : (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
      ∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega))
      (fun j _ _ => sq_nonneg _)
  linarith

theorem markedGridWindow_jet_bound (g₀ : SmoothRiemannianMetric I M) :
    ∃ K0 : ℕ → ℝ, (∀ n, 0 ≤ K0 n) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) {Λ₀ Λ₁ : ℝ}, 0 ≤ Λ₀ → Λ₀ ≤ 1 → 0 ≤ Λ₁ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2) →
        ∀ {r c : ℕ} (X : SmoothCcTensor g₀ r c) {K : ℕ → ℝ}, (∀ i, 0 ≤ K i) →
          HasMarkedGridWindow (I := I) (M := M) g₀ P X 2 K →
          ∀ n : ℕ,
            ‖iteratedCovGrad (I := I) g₀ r c n X‖ ^ 2 ≤
              K n * (K0 n * (1 + Λ₁ ^ 2)) *
                (1 + ∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kmon, hKmon_nn, hmon⟩ := markedGridWindow_monomial_bound (I := I) (M := M) g₀
  set CT : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 2),
    Combinatorics.antidiagonalTupleGridCount k with hCT_def
  have hCT_nn : ∀ n, 0 ≤ CT n := fun n =>
    Finset.sum_nonneg (fun k _ => Combinatorics.antidiagonalTupleGridCount_nonneg k)
  refine ⟨fun n => ((n : ℝ) + 1) * (((n : ℝ) + 1) * (CT n * Kmon (n + 1))), fun n => by
    have := hCT_nn n; have := hKmon_nn (n + 1); positivity, ?_⟩
  intro P Λ₀ Λ₁ hΛ₀0 hΛ₀1 hΛ₁0 hsup hcap r c X K hK hX n
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  have : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set b : M → ℕ → ℝ := fun x => covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hb_def
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (n + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hJS_def
  set Cmon : ℝ := Kmon (n + 1) * (1 + Λ₁ ^ 2) * JS with hCmon_def
  have hJS_nn : 0 ≤ JS := by
    have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range (n + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simp only [hJS_def]; linarith
  have hL1 : (0 : ℝ) ≤ 1 + Λ₁ ^ 2 := by nlinarith [sq_nonneg Λ₁]
  have hCmon_nn : 0 ≤ Cmon := by
    have h1 := hKmon_nn (n + 1)
    simp only [hCmon_def]
    exact mul_nonneg (mul_nonneg h1 hL1) hJS_nn
  have hint : ∀ f : M → ℝ, Continuous f → MeasureTheory.Integrable f μ := by
    intro f hf
    rw [hμ]
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : ∀ cc dd k : ℕ, cc + dd + k ≤ n →
      (∫ x, b x (cc + 1) * b x (dd + 1) *
          Combinatorics.antidiagonalTupleGrid (b x) k ∂μ) ≤
        Combinatorics.antidiagonalTupleGridCount k * Cmon := by
    intro cc dd k hk
    have hexp : (fun x : M => b x (cc + 1) * b x (dd + 1) *
          Combinatorics.antidiagonalTupleGrid (b x) k)
        = fun x : M => ∑ n' ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
              b x (cc + 1) * b x (dd + 1) * ∏ q : Fin n', b x (e q) := by
      funext x
      rw [show Combinatorics.antidiagonalTupleGrid (b x) k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
                ∏ q : Fin n', b x (e q) from rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
    have hIT : ∀ n' ∈ Finset.range (k + 1), MeasureTheory.Integrable
        (fun x : M => ∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
          b x (cc + 1) * b x (dd + 1) * ∏ q : Fin n', b x (e q)) μ := by
      intro n' _
      refine hint _ (continuous_finsetSum _ (fun e _ => ?_))
      exact ((contGB (I := I) (M := M) g₀ P (cc + 1)).mul
        (contGB (I := I) (M := M) g₀ P (dd + 1))).mul
        (continuous_finsetProd _ (fun q _ => contGB (I := I) (M := M) g₀ P (e q)))
    rw [hexp, MeasureTheory.integral_finsetSum _ hIT]
    have hstep : ∀ n' ∈ Finset.range (k + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
            b x (cc + 1) * b x (dd + 1) * ∏ q : Fin n', b x (e q) ∂μ) ≤
          ((Finset.Nat.antidiagonalTuple n' k).card : ℝ) * Cmon := by
      intro n' hn'
      rw [Finset.mem_range] at hn'
      have hIT2 : ∀ e ∈ Finset.Nat.antidiagonalTuple n' k, MeasureTheory.Integrable
          (fun x : M => b x (cc + 1) * b x (dd + 1) * ∏ q : Fin n', b x (e q)) μ := by
        intro e _
        refine hint _ ?_
        exact ((contGB (I := I) (M := M) g₀ P (cc + 1)).mul
          (contGB (I := I) (M := M) g₀ P (dd + 1))).mul
          (continuous_finsetProd _ (fun q _ => contGB (I := I) (M := M) g₀ P (e q)))
      rw [MeasureTheory.integral_finsetSum _ hIT2]
      calc (∑ e ∈ Finset.Nat.antidiagonalTuple n' k,
            ∫ x, b x (cc + 1) * b x (dd + 1) * ∏ q : Fin n', b x (e q) ∂μ)
          ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n' k, Cmon := by
            refine Finset.sum_le_sum (fun e he => ?_)
            exact hmon P hΛ₀0 hΛ₀1 hΛ₁0 hsup hcap (n + 1) (cc + 1) (dd + 1) k n' e
              (by omega) (by omega) (by omega)
              (Finset.Nat.mem_antidiagonalTuple.mp he) (by omega)
        _ = ((Finset.Nat.antidiagonalTuple n' k).card : ℝ) * Cmon := by
            rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Combinatorics.antidiagonalTupleGridCount, Finset.sum_mul]
  have h2 : ∀ cc dd w : ℕ, cc + dd + w ≤ n + 1 →
      (∫ x, b x (cc + 1) * b x (dd + 1) *
          Combinatorics.antidiagonalTupleGridWindow (b x) w ∂μ) ≤ CT n * Cmon := by
    intro cc dd w hw
    have hexp : (fun x : M => b x (cc + 1) * b x (dd + 1) *
          Combinatorics.antidiagonalTupleGridWindow (b x) w)
        = fun x : M => ∑ k ∈ Finset.range w,
            b x (cc + 1) * b x (dd + 1) *
              Combinatorics.antidiagonalTupleGrid (b x) k := by
      funext x
      rw [Combinatorics.antidiagonalTupleGridWindow, Finset.mul_sum]
    have hIT : ∀ k ∈ Finset.range w, MeasureTheory.Integrable
        (fun x : M => b x (cc + 1) * b x (dd + 1) *
          Combinatorics.antidiagonalTupleGrid (b x) k) μ := by
      intro k _
      refine hint _ ?_
      exact ((contGB (I := I) (M := M) g₀ P (cc + 1)).mul
        (contGB (I := I) (M := M) g₀ P (dd + 1))).mul
        (contGrid (I := I) (M := M) g₀ P k)
    rw [hexp, MeasureTheory.integral_finsetSum _ hIT]
    calc (∑ k ∈ Finset.range w, ∫ x, b x (cc + 1) * b x (dd + 1) *
            Combinatorics.antidiagonalTupleGrid (b x) k ∂μ)
        ≤ ∑ k ∈ Finset.range w,
            Combinatorics.antidiagonalTupleGridCount k * Cmon := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [Finset.mem_range] at hk
          exact h3 cc dd k (by omega)
      _ = (∑ k ∈ Finset.range w, Combinatorics.antidiagonalTupleGridCount k) * Cmon := by
          rw [Finset.sum_mul]
      _ ≤ CT n * Cmon := by
          refine mul_le_mul_of_nonneg_right ?_ hCmon_nn
          simp only [hCT_def]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => Finset.mem_range.mpr (by rw [Finset.mem_range] at hz; omega))
            (fun k _ _ => Combinatorics.antidiagonalTupleGridCount_nonneg k)
  have h1 : ∀ cc w : ℕ, cc + w ≤ n →
      (∫ x, b x (cc + 1) * Combinatorics.markGrid (b x) 1 w ∂μ) ≤
        ((n : ℝ) + 1) * (CT n * Cmon) := by
    intro cc w hw
    have hcwin : ∀ v : ℕ, Continuous (fun x : M =>
        Combinatorics.antidiagonalTupleGridWindow (b x) v) := by
      intro v
      have heq : (fun x : M => Combinatorics.antidiagonalTupleGridWindow (b x) v)
          = fun x : M => ∑ k ∈ Finset.range v,
              Combinatorics.antidiagonalTupleGrid (b x) k := rfl
      rw [heq]
      exact continuous_finsetSum _ (fun k _ => contGrid (I := I) (M := M) g₀ P k)
    have hexp : (fun x : M => b x (cc + 1) * Combinatorics.markGrid (b x) 1 w)
        = fun x : M => ∑ d ∈ Finset.range (w + 1),
            b x (cc + 1) * b x (d + 1) *
              Combinatorics.antidiagonalTupleGridWindow (b x) (w - d + 1) := by
      funext x
      rw [Combinatorics.markGrid_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Combinatorics.markGrid_zero, ← mul_assoc]
    have hIT : ∀ d ∈ Finset.range (w + 1), MeasureTheory.Integrable
        (fun x : M => b x (cc + 1) * b x (d + 1) *
          Combinatorics.antidiagonalTupleGridWindow (b x) (w - d + 1)) μ := by
      intro d _
      refine hint _ ?_
      exact ((contGB (I := I) (M := M) g₀ P (cc + 1)).mul
        (contGB (I := I) (M := M) g₀ P (d + 1))).mul (hcwin (w - d + 1))
    rw [hexp, MeasureTheory.integral_finsetSum _ hIT]
    calc (∑ d ∈ Finset.range (w + 1), ∫ x, b x (cc + 1) * b x (d + 1) *
            Combinatorics.antidiagonalTupleGridWindow (b x) (w - d + 1) ∂μ)
        ≤ ∑ _d ∈ Finset.range (w + 1), CT n * Cmon := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          rw [Finset.mem_range] at hd
          exact h2 cc d (w - d + 1) (by omega)
      _ = ((w : ℝ) + 1) * (CT n * Cmon) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((n : ℝ) + 1) * (CT n * Cmon) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hCT_nn n) hCmon_nn)
          have hwn : (w : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : w ≤ n)
          linarith
  have h0 : (∫ x, Combinatorics.markGrid (b x) 2 n ∂μ) ≤
      ((n : ℝ) + 1) * (((n : ℝ) + 1) * (CT n * Cmon)) := by
    have hexp : (fun x : M => Combinatorics.markGrid (b x) 2 n)
        = fun x : M => ∑ cc ∈ Finset.range (n + 1),
            b x (cc + 1) * Combinatorics.markGrid (b x) 1 (n - cc) := rfl
    have hIT : ∀ cc ∈ Finset.range (n + 1), MeasureTheory.Integrable
        (fun x : M => b x (cc + 1) *
          Combinatorics.markGrid (b x) 1 (n - cc)) μ := by
      intro cc _
      refine hint _ ?_
      exact (contGB (I := I) (M := M) g₀ P (cc + 1)).mul
        (contMk (I := I) (M := M) g₀ P 1 (n - cc))
    rw [hexp, MeasureTheory.integral_finsetSum _ hIT]
    calc (∑ cc ∈ Finset.range (n + 1),
          ∫ x, b x (cc + 1) * Combinatorics.markGrid (b x) 1 (n - cc) ∂μ)
        ≤ ∑ _cc ∈ Finset.range (n + 1), ((n : ℝ) + 1) * (CT n * Cmon) := by
          refine Finset.sum_le_sum (fun cc hcc => ?_)
          rw [Finset.mem_range] at hcc
          exact h1 cc (n - cc) (by omega)
      _ = ((n : ℝ) + 1) * (((n : ℝ) + 1) * (CT n * Cmon)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hwinInt : MeasureTheory.Integrable
      (fun x => K n * Combinatorics.markGrid (b x) 2 n) μ :=
    hint _ ((contMk (I := I) (M := M) g₀ P 2 n).const_mul (K n))
  have hL2 := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ r (c + n) (iteratedCovGrad (I := I) g₀ r c n X)
    (fun x => K n * Combinatorics.markGrid (b x) 2 n) hwinInt (fun x => hX n x)
  refine hL2.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hstep : K n * (∫ x, Combinatorics.markGrid (b x) 2 n ∂μ) ≤
      K n * (((n : ℝ) + 1) * (((n : ℝ) + 1) * (CT n * Cmon))) :=
    mul_le_mul_of_nonneg_left h0 (hK n)
  refine hstep.trans (le_of_eq ?_)
  simp only [hCmon_def, hJS_def]
  ring

end DifferentialGeometry.Integral.Connection

end
