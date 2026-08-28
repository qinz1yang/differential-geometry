import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.MoserTameBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SelfLowCapWindows
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.TameLieCorrJets

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.RicciDeTurckLowOrder
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
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

private lemma norm_sub_sq_le_two_sq
    {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ≤ a + b) :
    x ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

private lemma half_sq_three_term_le
    {x y q : ℝ} (hq : 0 ≤ q)
    (hx : x ≤ 2 * y + 2 * q) (hy : y ≤ 2 * q + 2 * q) :
    (1 / 2 : ℝ) ^ 2 * x ≤ 3 * q := by
  nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma sieSplit (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    slotInsertEndoCc (I := I) (M := M) g₀ s
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁) =
      slotInsertEndoCc (I := I) (M := M) g₀ s (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) := by
  have h := CurvatureCoefficientDifferenceJetTower.metricComparisonEndomorphismField_diff_split
    (I := I) (M := M) g₀ g₁
  have hsub : metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ =
      metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ -
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ := by
    rw [h]; abel
  rw [hsub, slotInsertEndoCc_sub]
  abel

private theorem endoAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  choose Sid hSid_nn hSid using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀
      (s + 1) ((s + 1) + i)
      (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 2 * (fr ^ s * Cb i) + 2 * Sid i, fun i => by
    have h1 : (0 : ℝ) ≤ fr ^ s * Cb i := mul_nonneg (pow_nonneg hfr_nn s) (hCb_nn i)
    have h2 := hSid_nn i
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hbnn := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := le_trans zero_le_one hone
  rw [sieSplit (I := I) (M := M) g₀ g₁ s, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
      iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x) =
      (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g₀ s
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x +
        (iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g₀ s
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) ≤
      (fr ^ s * Cb i) * Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ s
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) i x
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ i x
    have hgrideq : (∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) i := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) i ≤
        Combinatorics.antidiagonalTupleGridWindow (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _ hbnn (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x)
        ≤ fr ^ s * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) := h1
      _ ≤ fr ^ s * (Cb i * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) i) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn s)
      _ ≤ fr ^ s * (Cb i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgw (hCb_nn i))
            (pow_nonneg hfr_nn s)
      _ = (fr ^ s * Cb i) * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by ring
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      Sid i * Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) :=
    le_trans (hSid i x) (le_mul_of_one_le_right (hSid_nn i) hone)
  nlinarith [hA, hB, hWnn]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma clSplit (g₀ : SmoothRiemannianMetric I M) :
    ∃ Z : SmoothCcTensor g₀ 3 3, ∀ g₁ : SmoothRiemannianMetric I M,
      connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3 (permCoeff (I := I) (M := M) g₀ connectionDifferenceLowOrderPermutation)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) Z) :=
  ⟨_, fun _ => rfl⟩

private theorem clAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 3 i
              (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Z, hZ⟩ := clSplit (I := I) (M := M) g₀
  obtain ⟨Ce, hCe_nn, hCe⟩ := endoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 2
  choose SZ hSZ_nn hSZ using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
      (iteratedCovGrad (I := I) g₀ 3 3 i Z))
  choose SL hSL_nn hSL using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (3 + i)
      (iteratedCovGrad (I := I) g₀ 3 3 i (permCoeff (I := I) (M := M) g₀ connectionDifferenceLowOrderPermutation)))
  set Kin : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 Ce SZ with hKin_def
  have hKin_nn : ∀ i, 0 ≤ Kin i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hCe_nn hSZ_nn i
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 SL Kin,
    fun i => operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSL_nn hKin_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hconst : ∀ (c : ℕ) (S : ℕ → ℝ), (∀ j, 0 ≤ S j) →
      ∀ (X : SmoothCcTensor g₀ 3 c), (∀ (j : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (c + j) y
          ((iteratedCovGrad (I := I) g₀ 3 c j X).toSection y) ≤ S j) →
      ∀ (j : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (c + j) y
            ((iteratedCovGrad (I := I) g₀ 3 c j X).toSection y) ≤
          S j * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (j + 0 + 1) := by
    intro c S hS X hX j y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (j + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hX j y) (le_mul_of_one_le_right (hS j) hy)
  have hEw : ∀ (j : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + j) y
          ((iteratedCovGrad (I := I) g₀ 3 3 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection y) ≤
        Ce j * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (j + 0 + 1) := by
    intro j y
    have h := hCe g₁ P htie hδ_le hδ0 hδ j y
    have hidx : j + 0 + 1 = j + 1 := by omega
    rw [hidx]
    exact h
  have hinner := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 3) (a := 3) (b := 3) 0 0
    (slotInsertEndoCc (I := I) (M := M) g₀ 2
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) Z P hCe_nn hSZ_nn hEw
    (hconst 3 SZ hSZ_nn Z (fun j y => hSZ j y))
  have hinner' : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) Z)).toSection y) ≤
        Kin l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 0 + 1) := by
    intro l y
    have h := hinner l y
    have hidx : l + 0 + 0 + 1 = l + 0 + 1 := by omega
    rw [hidx] at h
    exact h
  have houter := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 3) (a := 3) (b := 3) 0 0
    (permCoeff (I := I) (M := M) g₀ connectionDifferenceLowOrderPermutation)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) Z) P hSL_nn hKin_nn
    (hconst 3 SL hSL_nn (permCoeff (I := I) (M := M) g₀ connectionDifferenceLowOrderPermutation) (fun j y => hSL j y))
    hinner' i x
  rw [hZ g₁]
  have hidx : i + 0 + 0 + 1 = i + 1 := by omega
  rw [hidx] at houter
  exact houter

theorem exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_capWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P
          (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Ccl, hCcl_nn, hcl⟩ := clAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ce1, hCe1_nn, hce1⟩ := endoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 1
  choose SA hSA_nn hSA using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
      (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ ricciConnectionDifferenceDerivativeCyclicPermutation)))
  choose SM hSM_nn hSM using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (2 + i)
      (iteratedCovGrad (I := I) g₀ 6 2 i (movingMetricPairTraceOperator (I := I) (M := M) g₀ g₀)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KCov : ℕ → ℝ := fun i => Ccl (i + 1) * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hKCov_def
  have hKCov_nn : ∀ i, 0 ≤ KCov i := fun i =>
    mul_nonneg (hCcl_nn (i + 1)) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  set KDag : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SA KCov with hKDag_def
  have hKDag_nn : ∀ i, 0 ≤ KDag i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSA_nn hKCov_nn i
  set KG : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KDag (fun _ => Λ) with hKG_def
  have hKG_nn : ∀ i, 0 ≤ KG i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKDag_nn (fun _ => hΛ0) i
  set KX : ℕ → ℝ := fun i => fr ^ 2 * KG i with hKX_def
  have hKX_nn : ∀ i, 0 ≤ KX i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKG_nn i)
  set KRK : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SM KX with hKRK_def
  have hKRK_nn : ∀ i, 0 ≤ KRK i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSM_nn hKX_nn i
  set KE1 : ℕ → ℝ := fun i => Ce1 i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hKE1_def
  have hKE1_nn : ∀ i, 0 ≤ KE1 i := fun i =>
    mul_nonneg (hCe1_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  set KMo : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KRK KE1 with hKMo_def
  have hKMo_nn : ∀ i, 0 ≤ KMo i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKRK_nn hKE1_nn i
  refine ⟨fun i => 2 * KMo i + 2 * KMo i, fun i => by have := hKMo_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hA : HasCapWin (I := I) (M := M) g₀ P
      (permCoeff (I := I) (M := M) g₀ ricciConnectionDifferenceDerivativeCyclicPermutation) SA :=
    capOfBnd (I := I) (M := M) g₀ P _ hSA_nn (fun i x => hSA i x)
  have hM : HasCapWin (I := I) (M := M) g₀ P
      (movingMetricPairTraceOperator (I := I) (M := M) g₀ g₀) SM :=
    capOfBnd (I := I) (M := M) g₀ P _ hSM_nn (fun i x => hSM i x)
  have hCov : HasCapWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 3 3 (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)) KCov := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _
      (fun i => hCcl_nn (i + 1)) (fun i y => ?_)
    rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 3 3 i
      (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁) y]
    refine le_trans (hcl g₁ P htie hδ_le hδ0 hδ (i + 1) y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCcl_nn (i + 1))
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
  have hDag : HasCapWin (I := I) (M := M) g₀ P
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁) KDag :=
    capApp (I := I) (M := M) g₀ P _ _ hSA_nn hKCov_nn hA hCov
  have hDP : HasCapWin (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 0 2 P) (fun _ => Λ) :=
    capOfDP (I := I) (M := M) g₀ P hΛ1 hP1
  have hG : HasCapWin (I := I) (M := M) g₀ P
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
        (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
        (covGrad (I := I) (M := M) g₀ 0 2 P)) KG :=
    capApp (I := I) (M := M) g₀ P _ _ hKDag_nn (fun _ => hΛ0) hDag hDP
  have hE1 : HasCapWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) KE1 := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCe1_nn (fun i y => ?_)
    refine le_trans (hce1 g₁ P htie hδ_le hδ0 hδ i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCe1_nn i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
  have hMono : ∀ σ : Equiv.Perm (Fin 4),
      HasCapWin (I := I) (M := M) g₀ P
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g₀ g₁
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) KMo := by
    intro σ
    have hRK : HasCapWin (I := I) (M := M) g₀ P
        (decompositionKernelContractionMonomialField (I := I) (M := M) g₀ g₀
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) KRK := by
      refine capCongr (I := I) (M := M) g₀ P
        (decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp (I := I) (M := M) g₀ g₀
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) ?_
      exact capApp (I := I) (M := M) g₀ P _ _ hSM_nn hKX_nn hM
        (capDdc (I := I) (M := M) g₀ P movingMetricPairTracePermutation
          (capIter (I := I) (M := M) g₀ P 2
            (capDdc0 (I := I) (M := M) g₀ P _ hG)))
    exact capApp (I := I) (M := M) g₀ P _ _ hKRK_nn hKE1_nn hRK hE1
  exact capSub (I := I) (M := M) g₀ P (hMono ricciConnectionDifferenceDerivativeCyclicPermutation) (hMono ricciConnectionDifferenceDerivativeFirstPairSwap)

private theorem ptAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i
              (pureTrace (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  choose SΦ hSΦ_nn hSΦ using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀
      (s + 2) (s + i)
      (iteratedCovGrad (I := I) g₀ (s + 2) s i (cometricDoubleTraceField (I := I) g₀ s)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KW : ℕ → ℝ := fun q => fr ^ (s + 1) * Cb q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q =>
    mul_nonneg (pow_nonneg hfr_nn (s + 1)) (hCb_nn q)
  refine ⟨fun i => 2 * SΦ i + 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SΦ KW i,
    fun i => by
      have h1 := hSΦ_nn i
      have h2 := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSΦ_nn hKW_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  have hbnn := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := le_trans zero_le_one hone
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') y
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection y) ≤
        SΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hSΦ i' y) (le_mul_of_one_le_right (hSΦ_nn i') hy)
  have hWw : ∀ (q : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + q) y
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) q
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection y) ≤
        KW q * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) := by
    intro q y
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ (s + 1)
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) q y
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ q y
    have hgrideq : (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) y
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection y)) =
        Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q ≤
        Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + q) y
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) q
              (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection y)
        ≤ fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) y
            ((iteratedCovGrad (I := I) g₀ 1 1 q
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ (s + 1) * (Cb q * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn (s + 1))
      _ ≤ fr ^ (s + 1) * (Cb q * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgw (hCb_nn q))
            (pow_nonneg hfr_nn (s + 1))
      _ = KW q * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) := by rw [hKW_def]; ring
  have hB := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := s + 2) (a := s + 2) (b := s) 0 0
    (cometricDoubleTraceField (I := I) g₀ s)
    (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) P hSΦ_nn hKW_nn hΦw hWw i x
  rw [pureTrace_split (I := I) (M := M) g₀ g₁ s, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ (s + 2) s i
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))) +
      iteratedCovGrad (I := I) g₀ (s + 2) s i
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) =
      (iteratedCovGrad (I := I) g₀ (s + 2) s i
          (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
            (cometricDoubleTraceField (I := I) g₀ s)
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x +
        (iteratedCovGrad (I := I) g₀ (s + 2) s i
          (cometricDoubleTraceField (I := I) g₀ s)).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 2) (s + i) x _ _) ?_
  have hidx : i + 0 + 0 + 1 = i + 1 := by omega
  rw [hidx] at hB
  have hA := hSΦ i x
  have hAw : SΦ i ≤ SΦ i * Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) :=
    le_mul_of_one_le_right (hSΦ_nn i) hone
  nlinarith [hA, hAw, hB, hWnn]

private theorem pairCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨C2, hC2_nn, h2⟩ := ptAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨C4, hC4_nn, h4⟩ := ptAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 4
  set K2 : ℕ → ℝ := fun i => C2 i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hK2_def
  set K4 : ℕ → ℝ := fun i => C4 i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hK4_def
  have hK2_nn : ∀ i, 0 ≤ K2 i := fun i => mul_nonneg (hC2_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  have hK4_nn : ∀ i, 0 ≤ K4 i := fun i => mul_nonneg (hC4_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 K2 K4,
    fun i => operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hK2_nn hK4_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hpt : ∀ (s : ℕ) (C : ℕ → ℝ), (∀ i, 0 ≤ C i) →
      (∀ (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i
              (pureTrace (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) →
      HasCapWin (I := I) (M := M) g₀ P (pureTrace (I := I) (M := M) g₀ g₁ s)
        (fun i => C i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1)) := by
    intro s C hC hbd
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hC (fun i y => ?_)
    refine le_trans (hbd i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hC i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
  have hP2 := hpt 2 C2 hC2_nn (fun i x => h2 g₁ P htie hδ_le hδ0 hδ i x)
  have hP4 := hpt 4 C4 hC4_nn (fun i x => h4 g₁ P htie hδ_le hδ0 hδ i x)
  have hpair : cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (pureTrace (I := I) (M := M) g₀ g₁ 2) (pureTrace (I := I) (M := M) g₀ g₁ 4) := rfl
  exact capCongr (I := I) (M := M) g₀ P hpair
    (capApp (I := I) (M := M) g₀ P _ _ hK2_nn hK4_nn hP2 hP4)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma curvSmul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (t : ℝ) :
    riemannCurvatureCoefficientField (I := I) (M := M) g₀ (t • T) = t • riemannCurvatureCoefficientField (I := I) (M := M) g₀ T := by
  change
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
          (riemannLoweredContractionA (I := I) (M := M) g₀) (t • T) +
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
          (riemannLoweredContractionB (I := I) (M := M) g₀) (t • T) =
      t •
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g₀) T +
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g₀) T)
  rw [operatorFieldComposition_smul_right, operatorFieldComposition_smul_right, smul_add]

private theorem curvCap (g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (riemannCurvatureCoefficientField (I := I) (M := M) g₀ P) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  choose S1 hS1_nn hS1 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (riemannLoweredContractionA (I := I) (M := M) g₀)))
  choose S2 hS2_nn hS2 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (riemannLoweredContractionB (I := I) (M := M) g₀)))
  set F1 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 S1 (fun _ => Λ) with hF1_def
  set F2 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 S2 (fun _ => Λ) with hF2_def
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hS1_nn (fun _ => hΛ0) i
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hS2_nn (fun _ => hΛ0) i
  refine ⟨fun i => 2 * F1 i + 2 * F2 i, fun i => by
    have := hF1_nn i; have := hF2_nn i; linarith, ?_⟩
  intro P hP0 hP1
  have hPcap : HasCapWin (I := I) (M := M) g₀ P P (fun _ => Λ) :=
    capOfP (I := I) (M := M) g₀ P hΛ1 hP0 hP1
  have hW1 : HasCapWin (I := I) (M := M) g₀ P (riemannLoweredContractionA (I := I) (M := M) g₀) S1 :=
    capOfBnd (I := I) (M := M) g₀ P _ hS1_nn (fun i x => hS1 i x)
  have hW2 : HasCapWin (I := I) (M := M) g₀ P (riemannLoweredContractionB (I := I) (M := M) g₀) S2 :=
    capOfBnd (I := I) (M := M) g₀ P _ hS2_nn (fun i x => hS2 i x)
  have h1 := capApp (I := I) (M := M) g₀ P
    (riemannLoweredContractionA (I := I) (M := M) g₀) P hS1_nn (fun _ => hΛ0) hW1 hPcap
  have h2 := capApp (I := I) (M := M) g₀ P
    (riemannLoweredContractionB (I := I) (M := M) g₀) P hS2_nn (fun _ => hΛ0) hW2 hPcap
  exact capCongr (I := I) (M := M) g₀ P (rfl : riemannCurvatureCoefficientField (I := I) (M := M) g₀ P = _)
    (capAdd (I := I) (M := M) g₀ P h1 h2)

open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower in
private theorem revEndoAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀ : δ₀ < 1) (s : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (q : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + q) x
            ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) q
              (slotInsertEndoCc (I := I) (M := M) g₀ s
                (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀))).toSection x) ≤
          C q * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) := by
  classical
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set d0 : ℝ := max δ₀ 0 with hd0_def
  have hd0_nn : (0 : ℝ) ≤ d0 := le_max_right _ _
  refine ⟨fun q => fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2), fun q => by positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ q x
  have hbnn := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hbnn (by omega)
  have hWnn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) := le_trans zero_le_one hone
  have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ s
    (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀) q x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
      ((iteratedCovGrad (I := I) g₀ 1 1 q
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀))).toSection x) ≤
      2 * cid + 2 * ((fr * d0) ^ 2 + Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1)) := by
    rw [fullRev0_eq (I := I) (M := M) g₀ g₁,
      omRecover_add (I := I) (M := M) g₀ g₁ P htie, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 1 q
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 1 q
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 1 q
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 q
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P))).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + q) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
        ((iteratedCovGrad (I := I) g₀ 1 1 q
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x) ≤ cid := by
      match q with
      | 0 => rw [iteratedCovGrad_zero]; exact hcid x
      | (m + 1) =>
          have hz : (iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x = 0 := by
            rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ m]
            simp
          rw [hz, riemannianFiberNormSq_zero]
          exact hcid_nn
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
        ((iteratedCovGrad (I := I) g₀ 1 1 q
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))).toSection x) ≤
        (fr * d0) ^ 2 + Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) := by
      rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
        (symmS (I := I) (M := M) g₀ P) q x]
      match q with
      | 0 =>
          have hz := riemannianFiberNormSq_symmS_zero_le_fibreSmall (I := I) (M := M) g₀ hd0_nn P
            (le_trans hδ_le (le_max_left _ _)) hδ0 hδ x
          have hred : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (0 + 2 + 0) x
                ((iteratedCovGrad (I := I) g₀ 0 (0 + 2) 0
                  (symmS (I := I) (M := M) g₀ P)).toSection x) =
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((symmS (I := I) (M := M) g₀ P).toSection x) := rfl
          rw [hred]
          linarith [hz, hWnn]
      | (m + 1) =>
          refine le_trans
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_iteratedCovGrad_symmS_pointwise
                (I := I) (M := M) g₀ P (m + 1) x) ?_
          have hgb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1) P).toSection x) =
              covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (m + 1) := rfl
          have hsg := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) hbnn 0 (m + 1) (by omega)
          rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one, zero_add] at hsg
          have hle : covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x (m + 1) ≤
              Combinatorics.antidiagonalTupleGridWindow
                (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (m + 1 + 1) :=
            le_trans hsg
              (Combinatorics.antidiagonalTupleGrid_le_window _ hbnn (by omega))
          have hnn : (0 : ℝ) ≤ (fr * d0) ^ 2 := by positivity
          rw [hgb]
          linarith [hle, hnn]
    linarith [hA, hB]
  have hstep : fr ^ s * (2 * cid + 2 * ((fr * d0) ^ 2 +
      Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1))) ≤
      fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2) *
        Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) := by
    have hfs : (0 : ℝ) ≤ fr ^ s := pow_nonneg hfr_nn s
    have hd : (0 : ℝ) ≤ (fr * d0) ^ 2 := by positivity
    set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (q + 1) with hW_def
    have hprod : (0 : ℝ) ≤ (2 * cid + 2 * (fr * d0) ^ 2) * (W - 1) :=
      mul_nonneg (by linarith) (by linarith [hone])
    have hinner : 2 * cid + 2 * ((fr * d0) ^ 2 + W) ≤
        (2 * cid + 2 * (fr * d0) ^ 2 + 2) * W := by nlinarith [hprod]
    calc fr ^ s * (2 * cid + 2 * ((fr * d0) ^ 2 + W))
        ≤ fr ^ s * ((2 * cid + 2 * (fr * d0) ^ 2 + 2) * W) :=
          mul_le_mul_of_nonneg_left hinner hfs
      _ = fr ^ s * (2 * cid + 2 * (fr * d0) ^ 2 + 2) * W := by ring
  refine le_trans h1 (le_trans ?_ hstep)
  exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn s)

private theorem omegaCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Ce, hCe_nn, hce⟩ := revEndoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  set KE : ℕ → ℝ := fun i => Ce i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hKE_def
  set KC : ℕ → ℝ := fun i => Ccd i * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hKC_def
  have hKE_nn : ∀ i, 0 ≤ KE i := fun i => mul_nonneg (hCe_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  have hKC_nn : ∀ i, 0 ≤ KC i := fun i => mul_nonneg (hCcd_nn i) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 KE KC,
    fun i => operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKE_nn hKC_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hEndo : HasCapWin (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀)) KE := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCe_nn (fun i y => ?_)
    refine le_trans (hce g₁ P htie hδ_le hδ0 hδ i y) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCe_nn i)
    exact Combinatorics.antidiagonalTupleGridWindow_mono _
      (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
  have hCL : HasCapWin (I := I) (M := M) g₀ P
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) KC := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _ hCcd_nn (fun i y => ?_)
    rw [metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ g₁ i y]
    exact hcd g₁ P htie hδ_le hδ0 hδ i y
  exact capCongr (I := I) (M := M) g₀ P
    (rfl : connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁ = _)
    (capApp (I := I) (M := M) g₀ P _ _ hKE_nn hKC_nn hEndo
      (capDdc0 (I := I) (M := M) g₀ P (finRotate 3) hCL))

private theorem lrQuadCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ P (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨Kom, hKom_nn, wom⟩ := omegaCap (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨Ccd, hCcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun i => (fr ^ 2 * Ccd i) * antidiagonalTupleGridWindowShiftConstant Λ (i + 1) with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    mul_nonneg (mul_nonneg (pow_nonneg hfr_nn 2) (hCcd_nn i)) (antidiagonalTupleGridWindowShiftConstant_nonneg hΛ0 _)
  set KJ : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KA Kom with hKJ_def
  have hKJ_nn : ∀ i, 0 ≤ KJ i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKA_nn hKom_nn i
  refine ⟨fun i => 94 * KJ i, fun i => by have := hKJ_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hArm : HasCapWin (I := I) (M := M) g₀ P
      (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g₀ g₁) KA := by
    refine capOfArm (I := I) (M := M) g₀ P hΛ1 hP0 hP1 _
      (fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hCcd_nn i)) (fun i y => ?_)
    refine le_trans (deTurckLieCovariantDerivativeArmTwoCoefficient_l2 (I := I) (M := M) g₀ g₁ i y) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcd g₁ P htie hδ_le hδ0 hδ i y) (pow_nonneg hfr_nn 2)
  have hOm := wom g₁ P htie hδ_le hδ0 hδ hP0 hP1
  have hQB : HasCapWin (I := I) (M := M) g₀ P (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g₀ g₁) KJ :=
    capCongr (I := I) (M := M) g₀ P (rfl : connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g₀ g₁ = _)
      (capApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm hOm)
  have hQA : HasCapWin (I := I) (M := M) g₀ P (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g₀ g₁) KJ :=
    capCongr (I := I) (M := M) g₀ P (rfl : connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g₀ g₁ = _)
      (capApp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm
        (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 3) 1) hOm))
  have hsum := capAdd (I := I) (M := M) g₀ P
    (capAdd (I := I) (M := M) g₀ P
      (capAdd (I := I) (M := M) g₀ P
        (capAdd (I := I) (M := M) g₀ P
          (capAdd (I := I) (M := M) g₀ P
            (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 1) hQB) hQB)
          (capDdc0 (I := I) (M := M) g₀ P lrPermA hQA))
        (capDdc0 (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 2) hQA))
      (capDdc0 (I := I) (M := M) g₀ P lrPermB hQA))
    (capDdc0 (I := I) (M := M) g₀ P lrPermC hQA)
  refine capCongr (I := I) (M := M) g₀ P (rfl : connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁ = _) ?_
  refine capMono (I := I) (M := M) g₀ P (fun i => ?_) hsum
  exact le_of_eq (by ring)

theorem lieCovCap (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀
          (convexPerturbation (I := I) g₀ T 0 s) x 0 ≤ Λ)
        (_hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀
          (convexPerturbation (I := I) g₀ T 0 s) x 1 ≤ Λ),
        HasCapWin (I := I) (M := M) g₀ (convexPerturbation (I := I) g₀ T 0 s)
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) g₀ -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g₀ T hδg hδZ
              lieDecompositionQ lieDecompositionEps s) K := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  obtain ⟨KP, hKP_nn, wP⟩ := pairCap (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨KC, hKC_nn, wC⟩ := curvCap (I := I) (M := M) g₀ hΛ1
  obtain ⟨KQ, hKQ_nn, wQ⟩ := lrQuadCap (I := I) (M := M) g₀ hδ₀ hΛ1
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KR : ℕ → ℝ := fun i => 2 * ((1 / 2 : ℝ) ^ 2 * KC i) + 2 * KQ i with hKR_def
  have hKR_nn : ∀ i, 0 ≤ KR i := fun i => by
    have h1 := hKC_nn i; have h2 := hKQ_nn i
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
    simp only [hKR_def]; nlinarith [h1, h2, h3]
  set KE : ℕ → ℝ := fun i => fr ^ 2 * KR i with hKE_def
  have hKE_nn : ∀ i, 0 ≤ KE i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKR_nn i)
  refine ⟨fun i => (-1 : ℝ) ^ 2 * operatorFieldCompositionGridConstant (E := E) 0 0 KP KE i,
    fun i => by
      have := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKP_nn hKE_nn i
      nlinarith [this], ?_⟩
  intro T hTsymm δ hδ_le hδ0 hδg hδZ s hs hP0 hP1
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w :=
    fun y v w => metricPerturbationPath_inner_of_mem (I := I) g₀ T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcurv : ((-(s / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ T =
      ((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P := by
    rw [hPeq, curvSmul (I := I) (M := M) g₀ T s, smul_smul]
    congr 1
    ring
  have hCw : HasCapWin (I := I) (M := M) g₀ P
      (((-(s / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ T)
      (fun i => (1 / 2 : ℝ) ^ 2 * KC i) := by
    refine capCongr (I := I) (M := M) g₀ P hcurv ?_
    refine capMono (I := I) (M := M) g₀ P (fun i => ?_)
      (capSmul (I := I) (M := M) g₀ P ((-(1 / 2) : ℝ)) (wC P hP0 hP1))
    have := hKC_nn i
    nlinarith [this]
  have hQw : HasCapWin (I := I) (M := M) g₀ P
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)) KQ :=
    wQ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP hP0 hP1
  have hR4 : HasCapWin (I := I) (M := M) g₀ P
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g₀ T hδg hδZ s) KR := by
    refine capCongr (I := I) (M := M) g₀ P
      (deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g₀ T hδg hδZ s) ?_
    exact capSub (I := I) (M := M) g₀ P hCw hQw
  have hExt : HasCapWin (I := I) (M := M) g₀ P
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g₀ T hδg hδZ s))) KE :=
    capDdc (I := I) (M := M) g₀ P deTurckLieCovariantDerivativePairTracePermutation
      (capIter (I := I) (M := M) g₀ P 2 hR4)
  have hPw : HasCapWin (I := I) (M := M) g₀ P
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)) KP :=
    wP (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP hP0 hP1
  refine capCongr (I := I) (M := M) g₀ P
    (lieCov_residual (I := I) (M := M) g₀ T hδ_lt hδg hδZ hTsymm hs) ?_
  exact capSmul (I := I) (M := M) g₀ P (-1 : ℝ)
    (capApp (I := I) (M := M) g₀ P _ _ hKP_nn hKE_nn hPw hExt)

theorem pairMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ g₁) 0 K := by
  classical
  obtain ⟨C2, hC2_nn, h2⟩ := ptAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨C4, hC4_nn, h4⟩ := ptAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 4
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 C2 C4,
    fun i => operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hC2_nn hC4_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hP2 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (pureTrace (I := I) (M := M) g₀ g₁ 2) 0 C2 :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i x => h2 g₁ P htie hδ_le hδ0 hδ i x)
  have hP4 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (pureTrace (I := I) (M := M) g₀ g₁ 4) 0 C4 :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i x => h4 g₁ P htie hδ_le hδ0 hδ i x)
  have hpair : cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (pureTrace (I := I) (M := M) g₀ g₁ 2)
        (pureTrace (I := I) (M := M) g₀ g₁ 4) := by
    unfold cometricDoublePairTraceCoefficient
    rfl
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P hpair ?_
  exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
    hC2_nn hC4_nn hP2 hP4

theorem curvMark (g₀ : SmoothRiemannianMetric I M) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1) →
        HasMarkedGridWindow (I := I) (M := M) g₀ P (riemannCurvatureCoefficientField (I := I) (M := M) g₀ P) 0 K := by
  classical
  choose S1 hS1_nn hS1 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (riemannLoweredContractionA (I := I) (M := M) g₀)))
  choose S2 hS2_nn hS2 using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + i)
      (iteratedCovGrad (I := I) g₀ 2 4 i (riemannLoweredContractionB (I := I) (M := M) g₀)))
  set F1 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 S1 (fun _ => 1) with hF1_def
  set F2 : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 S2 (fun _ => 1) with hF2_def
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hS1_nn (fun _ => zero_le_one) i
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hS2_nn (fun _ => zero_le_one) i
  refine ⟨fun i => 2 * F1 i + 2 * F2 i, fun i => by
    have := hF1_nn i; have := hF2_nn i; linarith, ?_⟩
  intro P hP0
  have hPw : HasMarkedGridWindow (I := I) (M := M) g₀ P P 0 (fun _ => 1) :=
    hasMarkedGridWindow_base (I := I) (M := M) g₀ P hP0
  have hW1 : HasMarkedGridWindow (I := I) (M := M) g₀ P (riemannLoweredContractionA (I := I) (M := M) g₀) 0 S1 :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hS1_nn (fun i x => hS1 i x)
  have hW2 : HasMarkedGridWindow (I := I) (M := M) g₀ P (riemannLoweredContractionB (I := I) (M := M) g₀) 0 S2 :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hS2_nn (fun i x => hS2 i x)
  have h1 := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P (riemannLoweredContractionA (I := I) (M := M) g₀) P
    hS1_nn (fun _ => zero_le_one) hW1 hPw
  have h2 := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P (riemannLoweredContractionB (I := I) (M := M) g₀) P
    hS2_nn (fun _ => zero_le_one) hW2 hPw
  have hcurv : riemannCurvatureCoefficientField (I := I) (M := M) g₀ P =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
          (riemannLoweredContractionA (I := I) (M := M) g₀) P +
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
          (riemannLoweredContractionB (I := I) (M := M) g₀) P := by
    unfold riemannCurvatureCoefficientField
    rfl
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P hcurv ?_
  rw [hF1_def, hF2_def]
  exact hasMarkedGridWindow_add (I := I) (M := M) g₀ P h1 h2

theorem omegaMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁) 1 K := by
  classical
  obtain ⟨Ce, hCe_nn, hce⟩ := revEndoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 2
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connectionDifferenceMark (I := I) (M := M) g₀ hδ₀
  refine ⟨operatorFieldCompositionGridConstant (E := E) 0 0 Ce Kcd,
    fun i => operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hCe_nn hKcd_nn i, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hEndo : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀)) 0 Ce :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i y => hce g₁ P htie hδ_le hδ0 hδ i y)
  have hCL : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) 1 Kcd := by
    intro i y
    rw [metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ g₁ i y]
    exact hcd g₁ P htie hδ_le hδ0 hδ i y
  have homega : connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 3
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (metricComparisonEndomorphismField (I := I) (M := M) g₁ g₀))
        (domDomCongrSection (I := I) (M := M) g₀ (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) := by
    unfold connectionDifferenceMetricLoweredTensor endoSlotZeroCcTensor
    rfl
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P homega ?_
  exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
    hCe_nn hKcd_nn hEndo
    (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P (finRotate 3) hCL)

theorem lrQuadMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        HasMarkedGridWindow (I := I) (M := M) g₀ P (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁) 2 K := by
  classical
  obtain ⟨Kom, hKom_nn, wom⟩ := omegaMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := connectionDifferenceMark (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KA : ℕ → ℝ := fun i => fr ^ 2 * Kcd i with hKA_def
  have hKA_nn : ∀ i, 0 ≤ KA i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKcd_nn i)
  set KJ : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KA Kom with hKJ_def
  have hKJ_nn : ∀ i, 0 ≤ KJ i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKA_nn hKom_nn i
  refine ⟨fun i => 94 * KJ i, fun i => by have := hKJ_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ
  have hArm : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g₀ g₁) 1 KA := by
    intro i y
    refine le_trans (deTurckLieCovariantDerivativeArmTwoCoefficient_l2 (I := I) (M := M) g₀ g₁ i y) ?_
    rw [hKA_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcd g₁ P htie hδ_le hδ0 hδ i y) (pow_nonneg hfr_nn 2)
  have hOm := wom g₁ P htie hδ_le hδ0 hδ
  have hQB : HasMarkedGridWindow (I := I) (M := M) g₀ P (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g₀ g₁) 2 KJ := by
    have hpaired : connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g₀ g₁)
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁) := by
      unfold connectionDifferenceQuadraticPairedTensor
        deTurckLieCovariantDerivativeArmTwoCoefficient
      rfl
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P hpaired ?_
    rw [hKJ_def]
    exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _
      hKA_nn hKom_nn hArm hOm
  have hQA : HasMarkedGridWindow (I := I) (M := M) g₀ P (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g₀ g₁) 2 KJ := by
    have hcomposed : connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g₀ g₁)
          (domDomCongrSection (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g₀ g₁)) := by
      unfold connectionDifferenceQuadraticComposedTensor
        deTurckLieCovariantDerivativeArmTwoCoefficient
      rfl
    refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P hcomposed ?_
    rw [hKJ_def]
    exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKA_nn hKom_nn hArm
      (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 3) 1) hOm)
  have hsum := hasMarkedGridWindow_add (I := I) (M := M) g₀ P
    (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
      (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
        (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
          (hasMarkedGridWindow_add (I := I) (M := M) g₀ P
            (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 1) hQB) hQB)
          (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P lrPermA hQA))
        (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P (Equiv.swap (0 : Fin 4) 2) hQA))
      (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P lrPermB hQA))
    (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P lrPermC hQA)
  refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P (rfl : connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁ = _) ?_
  refine hasMarkedGridWindow_mono (I := I) (M := M) g₀ P (fun i => ?_) hsum
  exact le_of_eq (by ring)

open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma extSub (g₀ : SmoothRiemannianMetric I M) (X Y : SmoothCcTensor g₀ 0 4) :
    slotExtendIter (I := I) (M := M) g₀ 0 4 2 (X - Y) =
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 X -
        slotExtendIter (I := I) (M := M) g₀ 0 4 2 Y := by
  have hrec : ∀ Z : SmoothCcTensor g₀ 0 4,
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 Z =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Z) :=
    fun _ => rfl
  rw [hrec, hrec, hrec,
    DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower.slotExtend_sub_cc,
    DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower.slotExtend_sub_cc]

open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower in
theorem lieCovJet (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w =
            ccTensorBilin (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((convexPerturbation (I := I) g₀ T 0 s).toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) g₀ -
              deTurckLieTopOrderPairingFamily (I := I) (M := M) g₀ T hδg hδZ
                lieDecompositionQ lieDecompositionEps s)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j)
                (convexPerturbation (I := I) g₀ T 0 s)‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T 0 s)‖ ^ 2) := by
  classical
  obtain ⟨KP, hKP_nn, wP⟩ := pairMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨KC, hKC_nn, wC⟩ := curvMark (I := I) (M := M) g₀
  obtain ⟨KQ, hKQ_nn, wQ⟩ := lrQuadMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0A, hK0A_nn, hjet0⟩ := markedGridWindow_zeroOrder_jet_bound (I := I) (M := M) g₀
  obtain ⟨K0B, hK0B_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KEA : ℕ → ℝ := fun i => fr ^ 2 * ((-(1 / 2 : ℝ)) ^ 2 * KC i) with hKEA_def
  have hKEA_nn : ∀ i, 0 ≤ KEA i := fun i => by
    have := hKC_nn i
    simp only [hKEA_def]
    positivity
  set KEB : ℕ → ℝ := fun i => fr ^ 2 * KQ i with hKEB_def
  have hKEB_nn : ∀ i, 0 ≤ KEB i := fun i =>
    mul_nonneg (pow_nonneg hfr_nn 2) (hKQ_nn i)
  set KAr : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KP KEA with hKAr_def
  have hKAr_nn : ∀ i, 0 ≤ KAr i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKP_nn hKEA_nn i
  set KBr : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KP KEB with hKBr_def
  have hKBr_nn : ∀ i, 0 ≤ KBr i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKP_nn hKEB_nn i
  refine ⟨fun i => 2 * (KBr i * K0B i) + 2 * (KAr i * K0A i),
    fun i => 2 * (KBr i * K0B i) * cg,
    fun i => by
      have h1 : (0 : ℝ) ≤ KBr i * K0B i := mul_nonneg (hKBr_nn i) (hK0B_nn i)
      have h2 : (0 : ℝ) ≤ KAr i * K0A i := mul_nonneg (hKAr_nn i) (hK0A_nn i)
      linarith,
    fun i => by
      have h1 : (0 : ℝ) ≤ KBr i * K0B i := mul_nonneg (hKBr_nn i) (hK0B_nn i)
      positivity, ?_⟩
  intro T hTsymm δ hδ_le hδ0 hδg hδZ s hs hP0 i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w :=
    fun y v w => metricPerturbationPath_inner_of_mem (I := I) g₀ T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcurv : ((-(s / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ T =
      ((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P := by
    rw [hPeq, curvSmul (I := I) (M := M) g₀ T s, smul_smul]
    congr 1
    ring
  have hAw : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P) 0
      (fun i => (-(1 / 2 : ℝ)) ^ 2 * KC i) :=
    hasMarkedGridWindow_smul (I := I) (M := M) g₀ P ((-(1 / 2) : ℝ)) (wC P (fun x => hP0 x))
  have hBw : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)) 2 KQ :=
    wQ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP
  have hPw : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)) 0 KP :=
    wP (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) P htie hδ_le hδ0 hδP
  have hArmA : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P)))) 0 KAr := by
    simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKP_nn hKEA_nn hPw
      (hasMarkedGridWindow_domainReindex (I := I) (M := M) g₀ P deTurckLieCovariantDerivativePairTracePermutation
        (hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 2 hAw))
  have hArmB : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))))) 2 KBr := by
    simpa using hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKP_nn hKEB_nn hPw
      (hasMarkedGridWindow_domainReindex (I := I) (M := M) g₀ P deTurckLieCovariantDerivativePairTracePermutation
        (hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 2 hBw))
  have hres :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) g₀ -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g₀ T hδg hδZ
          lieDecompositionQ lieDecompositionEps s =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)))) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P))) := by
    have hres0 :
        deTurckLieCovariantDerivativeArmField (I := I) (M := M) g₀
            (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s) g₀ -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g₀ T hδg hδZ
            lieDecompositionQ lieDecompositionEps s =
          (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g₀ T hδg hδZ s))) :=
      lieCov_residual (I := I) (M := M) g₀ T hδ_lt hδg hδZ hTsymm hs
    rw [hres0, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g₀ T hδg hδZ s, hcurv,
      extSub (I := I) (M := M) g₀,
      DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower.rsDomDomCongrSection_sub_cc,
      ccOperatorFieldComp_sub_right, neg_smul, one_smul, neg_sub]
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hJS_def
  have hJS_nn : 0 ≤ JS := by
    have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simp only [hJS_def]; linarith
  have hbA := hjet0 P hP0 _ hKAr_nn hArmA i
  have hbB := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap _ hKBr_nn hArmB i
  rw [hres, iteratedCovGrad_sub]
  have hnA : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P))))‖ := norm_nonneg _
  have hnB : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)))))‖ := norm_nonneg _
  have htri := norm_sub_le
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))))))
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P)))))
  have hsq : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))))) -
      iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P))))‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)))))‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P))))‖ ^ 2 := by
    exact norm_sub_sq_le_two_sq (norm_nonneg _) hnB hnA htri
  refine hsq.trans ?_
  have hAfin : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (((-(1 / 2) : ℝ)) • riemannCurvatureCoefficientField (I := I) (M := M) g₀ P))))‖ ^ 2 ≤
      2 * (KAr i * K0A i) * JS := by
    have h := mul_le_mul_of_nonneg_left hbA (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i _‖ ^ 2
        ≤ 2 * (KAr i * K0A i * JS) := h
      _ = 2 * (KAr i * K0A i) * JS := by ring
  have hBfin : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T 0 hδg hδZ s)))))‖ ^ 2 ≤
      (2 * (KBr i * K0B i) + 2 * (KBr i * K0B i) * cg * H3) * JS := by
    have h := mul_le_mul_of_nonneg_left hbB (by norm_num : (0 : ℝ) ≤ 2)
    refine h.trans (le_of_eq ?_)
    rw [hΛ₁sq]
    ring
  have hgoal : 2 * (KAr i * K0A i) * JS +
      (2 * (KBr i * K0B i) + 2 * (KBr i * K0B i) * cg * H3) * JS =
      (2 * (KBr i * K0B i) + 2 * (KAr i * K0A i) +
        2 * (KBr i * K0B i) * cg * H3) * JS := by ring
  linarith [hAfin, hBfin, hgoal.le, hgoal.ge]

open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma sieZero (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    covGrad (I := I) (M := M) g₀ (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ s
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ (s + 1) (s + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ s
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ s
    (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero (I := I) (M := M) g₀ Y x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))]
  rw [show slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma permRe (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (Φ : SmoothCcTensor g₀ d d) (ρ : Equiv.Perm (Fin d)) :
    ccOperatorFieldComp (I := I) (M := M) g₀ d d d Φ
        (permCoeff (I := I) (M := M) g₀ ρ) =
      reindexCoeffGen (I := I) (M := M) g₀ d d Φ ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply, reindexCoeffGen_toSection,
    reindexCoeffFibGen_apply]
  change (show Tensor0SSpace d I x →L[ℝ] Tensor0SSpace d I x from Φ.toSection x)
      (slotPermCLM (I := I) ρ x D) = _
  rw [slotPermCLM_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma clZ (g₀ g₁ : SmoothRiemannianMetric I M) :
    connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3 (permCoeff (I := I) (M := M) g₀ connectionDifferenceLowOrderPermutation)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))
          ((1 / 2 : ℝ) •
            (permCoeff (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) +
              permCoeff (I := I) (M := M) g₀ (finRotate 3) -
              permCoeff (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)))) := rfl

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma iteratedCovGradSm (g₀ : SmoothRiemannianMetric I M) (r c j : ℕ) (k : ℝ)
    (X : SmoothCcTensor g₀ r c) :
    iteratedCovGrad (I := I) g₀ r c j (k • X) =
      k • iteratedCovGrad (I := I) g₀ r c j X := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower in
omit [SigmaCompactSpace M] in
private theorem clExact (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
              (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 3 * (fr ^ 2 * Cb (i + 1)), fun i => by
    have := hCb_nn (i + 1)
    have : (0 : ℝ) ≤ fr ^ 2 * Cb (i + 1) := mul_nonneg (by positivity) (hCb_nn (i + 1))
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ i x
  set E₁ : SmoothCcTensor g₀ 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 2
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁) with hE₁_def
  set Zc : SmoothCcTensor g₀ 3 3 :=
    (1 / 2 : ℝ) • (permCoeff (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g₀ (finRotate 3) -
      permCoeff (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)) with hZc_def
  set Y : SmoothCcTensor g₀ 3 3 := ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 3 E₁ Zc with hY_def
  have hiso : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
        (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) Y).toSection x) := by
    refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 3
      connectionDifferenceLowOrderPermutation Y (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁) (fun y d => ?_) (i + 1) x
    rw [clZ (I := I) (M := M) g₀ g₁, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
    change Tensor0SSpace.toModel
        (slotPermCLM (I := I) connectionDifferenceLowOrderPermutation y
          ((show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 3 I y from Y.toSection y) d)) = _
    rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  have hYsplit : Y = (1 / 2 : ℝ) •
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (0 : Fin 3) 2) +
        reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (finRotate 3) -
        reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (1 : Fin 3) 2)) := by
    rw [hY_def, hZc_def, operatorFieldComposition_smul_right, operatorFieldComposition_sub_right, operatorFieldComposition_add_right,
      permRe, permRe, permRe]
  set q : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) E₁).toSection x) with hq_def
  have hq_nn : 0 ≤ q := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hre : ∀ ρ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
          (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ ρ)).toSection x) = q :=
    fun ρ => riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 3 E₁ ρ (i + 1) x
  have hYq : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1) Y).toSection x) ≤ 3 * q := by
    have hA := hre (Equiv.swap (0 : Fin 3) 2)
    have hB := hre (finRotate 3)
    have hC := hre (Equiv.swap (1 : Fin 3) 2)
    set DA : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (0 : Fin 3) 2)) with hDA_def
    set DB : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (finRotate 3)) with hDB_def
    set DC : SmoothCcTensor g₀ 3 (3 + (i + 1)) := iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
      (reindexCoeffGen (I := I) (M := M) g₀ 3 3 E₁ (Equiv.swap (1 : Fin 3) 2)) with hDC_def
    rw [hYsplit, iteratedCovGradSm, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul, iteratedCovGrad_sub, iteratedCovGrad_add]
    rw [show ((DA + DB - DC).toSection x) =
        (DA.toSection x + DB.toSection x) - DC.toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      (DA.toSection x + DB.toSection x) (DC.toSection x)
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
      (DA.toSection x) (DB.toSection x)
    rw [hC] at hsub
    rw [hA, hB] at hadd
    exact half_sq_three_term_le hq_nn hsub hadd
  have hE : q ≤ (fr ^ 2 * Cb (i + 1)) * Combinatorics.antidiagonalTupleGrid
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
    have hzero : iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) = 0 :=
      DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower.iteratedCovGrad_zero_of_covGrad_zero
        (I := I) (M := M) g₀ 3 3 _
        (sieZero (I := I) (M := M) g₀ 2) i
    have hsplit : iteratedCovGrad (I := I) g₀ 3 3 (i + 1) E₁ =
        iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) := by
      rw [hE₁_def, sieSplit (I := I) (M := M) g₀ g₁ 2, iteratedCovGrad_add, hzero, add_zero]
    rw [hq_def, hsplit]
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) (i + 1) x
    have h2 := hCb g₁ P htie hδ_le hδ0 hδ (i + 1) x
    have hgrideq : (∑ n ∈ Finset.range (i + 1 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n (i + 1),
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := rfl
    rw [hgrideq] at h2
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 3 3 (i + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x)
        ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (i + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) := h1
      _ ≤ fr ^ 2 * (Cb (i + 1) * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
      _ = (fr ^ 2 * Cb (i + 1)) * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
          simp only [mul_assoc]
  rw [hiso]
  calc
    _ ≤ 3 * q := hYq
    _ ≤ 3 * ((fr ^ 2 * Cb (i + 1)) *
        Combinatorics.antidiagonalTupleGrid
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1)) :=
      mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 3 by norm_num)
    _ = (3 * (fr ^ 2 * Cb (i + 1))) *
        Combinatorics.antidiagonalTupleGrid
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (i + 1) := by
      simp only [mul_assoc]

omit [SigmaCompactSpace M] in
private theorem clCovMk (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (covGrad (I := I) (M := M) g₀ 3 3 (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)) 1 K := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := clExact (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => C i * Combinatorics.antidiagonalTupleGridCount (i + 1), fun i =>
    mul_nonneg (hC_nn i) (Combinatorics.antidiagonalTupleGridCount_nonneg _), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  refine hasMarkedGridWindow_of_antidiagonalTupleGrid_bound (I := I) (M := M) g₀ P hP0 _ hC_nn (fun i x => ?_)
  rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 3 3 i
    (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁) x]
  exact hC g₁ P htie hδ_le hδ0 hδ i x

theorem exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_markWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P) 2 K := by
  classical
  obtain ⟨KCov, hKCov_nn, hcov⟩ := clCovMk (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ce1, hCe1_nn, hce1⟩ := endoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ 1
  choose SA hSA_nn hSA using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (4 + i)
      (iteratedCovGrad (I := I) g₀ 4 4 i (permCoeff (I := I) (M := M) g₀ ricciConnectionDifferenceDerivativeCyclicPermutation)))
  choose SM hSM_nn hSM using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (2 + i)
      (iteratedCovGrad (I := I) g₀ 6 2 i (movingMetricPairTraceOperator (I := I) (M := M) g₀ g₀)))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KDag : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SA KCov with hKDag_def
  have hKDag_nn : ∀ i, 0 ≤ KDag i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSA_nn hKCov_nn i
  set KG : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KDag (fun _ => 1) with hKG_def
  have hKG_nn : ∀ i, 0 ≤ KG i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKDag_nn (fun _ => zero_le_one) i
  set KX : ℕ → ℝ := fun i => fr ^ 2 * KG i with hKX_def
  have hKX_nn : ∀ i, 0 ≤ KX i := fun i => mul_nonneg (pow_nonneg hfr_nn 2) (hKG_nn i)
  set KRK : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 SM KX with hKRK_def
  have hKRK_nn : ∀ i, 0 ≤ KRK i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSM_nn hKX_nn i
  set KMo : ℕ → ℝ := operatorFieldCompositionGridConstant (E := E) 0 0 KRK Ce1 with hKMo_def
  have hKMo_nn : ∀ i, 0 ≤ KMo i := fun i =>
    operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKRK_nn hCe1_nn i
  refine ⟨fun i => 2 * KMo i + 2 * KMo i, fun i => by have := hKMo_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hA : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (permCoeff (I := I) (M := M) g₀ ricciConnectionDifferenceDerivativeCyclicPermutation) 0 SA :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hSA_nn (fun i x => hSA i x)
  have hM : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (movingMetricPairTraceOperator (I := I) (M := M) g₀ g₀) 0 SM :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hSM_nn (fun i x => hSM i x)
  have hCov : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 3 3 (connectionDifferenceLowOrderOperator (I := I) (M := M) g₀ g₁)) 1 KCov :=
    hcov g₁ P htie hδ_le hδ0 hδ hP0
  have hDag : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁) 1 KDag :=
    hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hSA_nn hKCov_nn hA hCov
  have hDP : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (covGrad (I := I) (M := M) g₀ 0 2 P) 1 (fun _ => 1) :=
    hasMarkedGridWindow_covariantDerivative_base (I := I) (M := M) g₀ P
  have hG : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
        (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
        (covGrad (I := I) (M := M) g₀ 0 2 P)) 2 KG :=
    hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKDag_nn (fun _ => zero_le_one) hDag hDP
  have hE1 : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) 0 Ce1 :=
    hasMarkedGridWindow_of_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ P _ (fun i y => hce1 g₁ P htie hδ_le hδ0 hδ i y)
  have hMono : ∀ σ : Equiv.Perm (Fin 4),
      HasMarkedGridWindow (I := I) (M := M) g₀ P
        (ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g₀ g₁
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) 2 KMo := by
    intro σ
    have hRK : HasMarkedGridWindow (I := I) (M := M) g₀ P
        (decompositionKernelContractionMonomialField (I := I) (M := M) g₀ g₀
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) 2 KRK := by
      refine hasMarkedGridWindow_congr (I := I) (M := M) g₀ P
        (decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp (I := I) (M := M) g₀ g₀
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
            (ricciConnectionDerivativeCoefficient (I := I) (M := M) g₀ g₁)
            (covGrad (I := I) (M := M) g₀ 0 2 P)) σ) ?_
      exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hSM_nn hKX_nn hM
        (hasMarkedGridWindow_domainReindex (I := I) (M := M) g₀ P movingMetricPairTracePermutation
          (hasMarkedGridWindow_slotExtendIter (I := I) (M := M) g₀ P 2
            (hasMarkedGridWindow_covariantDomainReindex (I := I) (M := M) g₀ P _ hG)))
    exact hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P _ _ hKRK_nn hCe1_nn hRK hE1
  exact hasMarkedGridWindow_sub (I := I) (M := M) g₀ P (hMono ricciConnectionDifferenceDerivativeCyclicPermutation) (hMono ricciConnectionDifferenceDerivativeFirstPairSwap)

theorem exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_covariantJetNormSq_bound (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (P.toSection x) ≤ 1)
        (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KA, hKA_nn, hDA⟩ := exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KA i * K0' i, fun i => KA i * K0' i * cg,
    fun i => mul_nonneg (hKA_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKA_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 i
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2 with hH3_def
  have hH3_nn : 0 ≤ H3 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set Λ₁ : ℝ := Real.sqrt (cg * H3) with hΛ₁_def
  have hΛ₁0 : 0 ≤ Λ₁ := Real.sqrt_nonneg _
  have hΛ₁sq : Λ₁ ^ 2 = cg * H3 := Real.sq_sqrt (mul_nonneg hcg_nn hH3_nn)
  have hcap : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x) ≤ Λ₁ ^ 2 := by
    intro x
    rw [hΛ₁sq]
    exact hcg P x
  have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x; rw [one_pow]; exact hP0 x
  have hgb : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1 := by
    intro x
    simpa [covariantJetFiberNormSqGrid] using hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P) hKA_nn
    (hDA g₁ P htie hδ_le hδ0 hδ hgb) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

end DifferentialGeometry.Integral.Connection

end
