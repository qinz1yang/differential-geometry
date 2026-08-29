import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnectionDifferenceOrderOneRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDifferenceRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound

noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma l1IteratedCovGradSmul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma l1RiemannianFiberNormSqNeg (g : SmoothRiemannianMetric I M) {r s : ℕ} (l : ℕ) (x : M)
    (X : SmoothCcTensor g r s) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l (-X)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + l) x
        ((iteratedCovGrad (I := I) g r s l X).toSection x) := by
  have hneg : (-X) = (-1 : ℝ) • X := by rw [neg_smul, one_smul]
  rw [hneg, l1IteratedCovGradSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
  norm_num

theorem pureAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kp : ℕ → ℝ, (∀ l, 0 ≤ Kp l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 2 l
              (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kp l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  set Φ : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + i)
      (iteratedCovGrad (I := I) g₀ 4 2 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set KW : ℕ → ℝ := fun q => fr ^ 3 * C_base q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := fun q => mul_nonneg (pow_nonneg hfr_nn 3) (hC_base_nn q)
  refine ⟨fun l => 2 * SΦ l + 2 * operatorFieldCompositionGridConstant (E := E) 0 0 SΦ KW l,
    fun l => by
      have h1 := hSΦ_nn l
      have h2 := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hSΦ_nn hKW_nn l
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  set bP : ℕ → ℝ := covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x with hbP_def
  have hbP_nn : ∀ j, 0 ≤ bP j := covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hone : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow bP (l + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow bP hbP_nn (by omega)
  set W : SmoothCcTensor g₀ 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 3 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) with hW_def
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i' Φ).toSection y) ≤
        SΦ i' * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have hy : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) :=
      Combinatorics.one_le_antidiagonalTupleGridWindow _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
    exact le_trans (hSΦ i' y) (le_mul_of_one_le_right (hSΦ_nn i') hy)
  have hWw : ∀ (q : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) y
          ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection y) ≤
        KW q * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) := by
    intro q y
    have h1 := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 3
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) q y
    have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q y
    have hgrideq : (∑ m ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m q,
          ∏ k : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e k) y
            ((iteratedCovGrad (I := I) g₀ 0 2 (e k) P).toSection y)) =
        Combinatorics.antidiagonalTupleGrid (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q := rfl
    rw [hgrideq] at h2
    have hgw : Combinatorics.antidiagonalTupleGrid
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q ≤
        Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) :=
      Combinatorics.antidiagonalTupleGrid_le_window _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) (by omega)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) y
            ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection y)
        ≤ fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) y
            ((iteratedCovGrad (I := I) g₀ 1 1 q
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection y) := h1
      _ ≤ fr ^ 3 * (C_base q * Combinatorics.antidiagonalTupleGrid
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) q) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hfr_nn 3)
      _ ≤ fr ^ 3 * (C_base q * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgw (hC_base_nn q)) (pow_nonneg hfr_nn 3)
      _ = KW q * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (q + 0 + 1) := by rw [hKW_def]; ring
  have hB := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 4) (a := 4) (b := 2) 0 0 Φ W P
    hSΦ_nn hKW_nn hΦw hWw l x
  have hid : cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁ =
      Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 Φ W := by
    have h := cometricDoubleTraceCoefficient_eq_doubleTrace_add_ccOperatorFieldComp (I := I) g₀ g₁
    simpa only [Φ, W] using h
  rw [hid, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ 4 2 l Φ +
        iteratedCovGrad (I := I) g₀ 4 2 l (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 4 2 l Φ).toSection x +
        (iteratedCovGrad (I := I) g₀ 4 2 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x
      from by rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 (2 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 4 2 l Φ).toSection x) ≤ SΦ l := hSΦ l x
  have hAw : SΦ l ≤ SΦ l * Combinatorics.antidiagonalTupleGridWindow bP (l + 1) :=
    le_mul_of_one_le_right (hSΦ_nn l) hone
  have hBw : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 4 2 l
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x) ≤
      operatorFieldCompositionGridConstant (E := E) 0 0 SΦ KW l *
        Combinatorics.antidiagonalTupleGridWindow bP (l + 1) := by
    have hidx : l + 0 + 0 + 1 = l + 1 := by omega
    rw [hbP_def]
    rw [hidx] at hB
    exact hB
  nlinarith only [hA, hAw, hBw]

theorem fourTrAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kft : ℕ → ℝ, (∀ n, 0 ≤ Kft n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          Kft n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 1) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  have h := hC g₁ P htie hδ_le hδ0 hδ n x
  have hwin : (∑ k ∈ Finset.range (n + 1),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
      Combinatorics.antidiagonalTupleGridWindow
        (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 1) := rfl
  rwa [hwin] at h

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem dltcEqPure (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁) σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  rfl

theorem dltcAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kp : ℕ → ℝ, (∀ l, 0 ≤ Kp l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 4 2 l
              (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ)).toSection x) ≤
          Kp l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  obtain ⟨Kp, hKp_nn, hp⟩ := pureAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨Kp, hKp_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ σ l x
  rw [dltcEqPure (I := I) (M := M) g₀ g₁ σ,
    riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g₀ g₁) σ l x]
  exact hp g₁ P htie hδ_le hδ0 hδ l x

theorem exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_antidiagonalTupleGridWindow_bound (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kr : ℕ → ℝ, (∀ n, 0 ≤ Kr n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          Kr n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kft, hKft_nn, hft⟩ := fourTrAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kker, hKker_nn, hker⟩ := ricciKerAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun n => operatorFieldCompositionGridConstant (E := E) 0 1 Kft Kker n,
    fun n => operatorFieldCompositionGridConstant_nonneg (E := E) hKft_nn hKker_nn n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection y) ≤
        Kft i' * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have h := hft g₁ P htie hδ_le hδ0 hδ i' y
    have hidx : i' + 0 + 1 = i' + 1 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 4 l
            (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁)).toSection y) ≤
        Kker l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 1 + 1) := by
    intro l y
    have h := hker g₁ P htie hδ_le hδ0 hδ l y
    have hidx : l + 1 + 1 = l + 2 := by omega
    rw [hidx]
    exact h
  have hfold := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 3) (a := 4) (b := 2) 0 1
    (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
    (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g₀ g₁) P
    hKft_nn hKker_nn hΦw hWw n x
  rw [linearizedRicciConnectionDifferenceOrder1CoeffField_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
  have hidx : n + 0 + 1 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  exact hfold

omit [SigmaCompactSpace M] in
theorem sfEndoAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ksf : ℕ → ℝ, (∀ l, 0 ≤ Ksf l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Ksf l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ :=
    CurvatureCoefficientDifferenceJetTower.exists_riemannianFiberNormSq_iteratedCovGrad_sharpFlatEndoCc_tgrid
      (I := I) (M := M) g₀ hδ₀
  refine ⟨S, hS_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ l x
  refine le_trans (hS g₁ P htie hδ_le hδ0 hδ l x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hS_nn l)
  exact Combinatorics.antidiagonalTupleGrid_le_window _
    (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x) (by omega)

theorem kappaAntidiagonalTupleGridWindow (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} :
    ∃ Kκ : ℕ → ℝ, (∀ l, 0 ≤ Kκ l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
                (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
                  (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) ≤
          Kκ l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (l + 2) := by
  classical
  obtain ⟨Kmcd, hKmcd_nn, hmcd⟩ := metricConnectionDifferenceLoweredCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨Kmcd, hKmcd_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup l x
  have hraise : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 2 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l
          (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)) l x]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      lieArm1RhoSlot0 (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) l x
  have hsign : deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg =
      -metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg := by
    rw [metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa (I := I) (M := M) g₀ g₁ g_bg, neg_neg]
  rw [hraise, hsign,
    l1RiemannianFiberNormSqNeg (I := I) (M := M) g₀ l x (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g_bg)]
  have h := hmcd g₁ P htie hδ_le hδ0 hδ hsup l x
  have hbase : (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) =
      covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x := rfl
  rwa [hbase] at h

theorem psiBAntidiagonalTupleGridWindow (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} :
    ∃ Kψ : ℕ → ℝ, (∀ n, 0 ≤ Kψ n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kψ n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kκ, hKκ_nn, hκ⟩ := kappaAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨Ksf, hKsf_nn, hsf⟩ := sfEndoAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun n => operatorFieldCompositionGridConstant (E := E) 1 0 Kκ Ksf n,
    fun n => operatorFieldCompositionGridConstant_nonneg (E := E) hKκ_nn hKsf_nn n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 1 2 i'
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
                (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))).toSection y) ≤
        Kκ i' * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 1 + 1) := by
    intro i' y
    have h := hκ g₁ P htie hδ_le hδ0 hδ hsup i' y
    have hidx : i' + 1 + 1 = i' + 2 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection y) ≤
        Ksf l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 0 + 1) := by
    intro l y
    have h := hsf g₁ P htie hδ_le hδ0 hδ l y
    have hidx : l + 0 + 1 = l + 1 := by omega
    rw [hidx]
    exact h
  have hfold := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 1) (a := 1) (b := 2) 1 0
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
    (sharpFlatEndoCc (I := I) g₀ g₁) P hKκ_nn hKsf_nn hΦw hWw n x
  have hidx : n + 1 + 0 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  have hdef : deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)))
        (sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  rw [hdef]
  exact hfold

omit [NeZero (Module.finrank ℝ E)] in
theorem fixCdAntidiagonalTupleGridWindow (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Kfx : ℕ → ℝ, (∀ n, 0 ≤ Kfx n) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)).toSection x) ≤
          Kfx n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  choose Kfx hKfx_nn hKfx using fun n =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 1 (2 + n)
        (iteratedCovGrad (I := I) g₀ 1 2 n
          (lieArm1FixCd (I := I) (M := M) g₀ g_bg))
  refine ⟨Kfx, hKfx_nn, ?_⟩
  intro P n x
  have hb : ∀ j, 0 ≤ covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x j :=
    covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x
  have hW1 : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow
      (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow _ hb (by omega)
  exact (hKfx n x).trans (by
    have := hKfx_nn n
    nlinarith)

theorem bgCcAntidiagonalTupleGridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kbg : ℕ → ℝ, (∀ n, 0 ≤ Kbg n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n
              (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kbg n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kfx, hKfx_nn, hfx⟩ := fixCdAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg
  refine ⟨fun n => 2 * Kcd n + 2 * Kfx n,
    fun n => by have := hKcd_nn n; have := hKfx_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ n x
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) with hW_def
  have hcd' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 1 2 n
        (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤ Kcd n * W := by
    have h := hcd g₁ P htie hδ_le hδ0 hδ n x
    rw [hW_def]
    change riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
      Kcd n * Combinatorics.antidiagonalTupleGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) (n + 2)
    exact h
  have hfx' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 1 2 n
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)).toSection x) ≤ Kfx n * W := by
    simpa only [W] using hfx P n x
  rw [lieArm1_connectionDifferenceBackground_decomp (I := I) (M := M) g₀ g₁ g_bg,
    iteratedCovGrad_add, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply]
  refine le_trans
    (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + n) x _ _) ?_
  calc
    2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (lieArm1FixCd (I := I) (M := M) g₀ g_bg)).toSection x)
        ≤ 2 * (Kcd n * W) + 2 * (Kfx n * W) := by linarith
    _ = (2 * Kcd n + 2 * Kfx n) * W := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem bgCcEqConn (g₀ g₁ : SmoothRiemannianMetric I M) :
    deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g₀ = connectionDifferenceSection (I := I) g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

theorem pieceAntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (Kψ : ℕ → ℝ) (hKψ_nn : ∀ l, 0 ≤ Kψ l) :
    ∃ Kpc : ℕ → ℝ, (∀ n, 0 ≤ Kpc n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (Ψ : SmoothCcTensor g₀ 1 2),
        (∀ (l : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y) ≤
          Kψ l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2)) →
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ)).toSection x) ≤
          Kpc n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kp, hKp_nn, hp⟩ := dltcAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun n => operatorFieldCompositionGridConstant (E := E) 0 1 Kp (fun l => fr * (fr * Kψ l)) n,
    fun n => operatorFieldCompositionGridConstant_nonneg (E := E) hKp_nn
      (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKψ_nn l))) n, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ Ψ hΨ σ' ρ n x
  have hΦw : ∀ (i' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') y
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')).toSection y) ≤
        Kp i' * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (i' + 0 + 1) := by
    intro i' y
    have h := hp g₁ P htie hδ_le hδ0 hδ σ' i' y
    have hidx : i' + 0 + 1 = i' + 1 := by omega
    rw [hidx]
    exact h
  have hWw : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) y
          ((iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3
              (slotExtend (I := I) (M := M) g₀ 1 2 Ψ))).toSection y) ≤
        fr * (fr * Kψ l) * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 1 + 1) := by
    intro l y
    have hidx : l + 1 + 1 = l + 2 := by omega
    rw [hidx]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 Ψ) l y) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2 Ψ l y) hfr_nn) ?_
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
            ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y))
        ≤ fr * (fr * (Kψ l * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hΨ l y) hfr_nn) hfr_nn
      _ = fr * (fr * Kψ l) * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2) := by ring
  have hfold := operatorFieldComposition_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ (p := 3) (a := 4) (b := 2) 0 1
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
    (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)) P
    hKp_nn (fun l => mul_nonneg hfr_nn (mul_nonneg hfr_nn (hKψ_nn l))) hΦw hWw n x
  have hidx : n + 0 + 1 + 1 = n + 2 := by omega
  rw [hidx] at hfold
  have hdef : lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ =
      reindexCoeffGen (I := I) (M := M) g₀ 3 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2 (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ')
          (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2 Ψ)))
        ρ := rfl
  rw [hdef, riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 2 _ ρ n x]
  exact hfold

theorem lieA1AntidiagonalTupleGridWindowBackground (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} :
    ∃ Kl : ℕ → ℝ, (∀ n, 0 ≤ Kl n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          Kl n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kcd, hKcd_nn, hcd⟩ := riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_antidiagonalTupleGridWindow_rf (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kbg, hKbg_nn, hbg⟩ := bgCcAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨Kψ, hKψ_nn, hψ⟩ := psiBAntidiagonalTupleGridWindow (I := I) (M := M) g₀ g_bg hδ₀
  set KΨ : ℕ → ℝ := fun l => Kcd l + Kbg l + Kψ l with hKΨ_def
  have hKΨ_nn : ∀ l, 0 ≤ KΨ l := fun l => by
    have := hKcd_nn l
    have := hKbg_nn l
    have := hKψ_nn l
    simp only [hKΨ_def]
    linarith
  obtain ⟨Kpc, hKpc_nn, hpc⟩ := pieceAntidiagonalTupleGridWindow (I := I) (M := M) g₀ hδ₀ KΨ hKΨ_nn
  refine ⟨fun n => 1138 * Kpc n, fun n => by have := hKpc_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set bW : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) with hbW_def
  have hbW_nn : 0 ≤ bW :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg _
      (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P x) _
  have hΨcd : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l (connectionDifferenceSection (I := I) g₁ g₀)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    have h := hcd g₁ P htie hδ_le hδ0 hδ l y
    have hbase : (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection y)) =
        covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y := rfl
    rw [hbase] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Combinatorics.antidiagonalTupleGridWindow_nonneg _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) _)
    have := hKbg_nn l
    have := hKψ_nn l
    simp only [hKΨ_def]
    linarith
  have hΨpsi : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    refine le_trans (hψ g₁ P htie hδ_le hδ0 hδ hsup l y) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Combinatorics.antidiagonalTupleGridWindow_nonneg _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) _)
    have := hKcd_nn l
    have := hKbg_nn l
    simp only [hKΨ_def]
    linarith
  have hΨbg : ∀ (l : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2) := by
    intro l y
    refine le_trans (hbg g₁ P htie hδ_le hδ0 hδ l y) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Combinatorics.antidiagonalTupleGridWindow_nonneg _
        (covariantJetFiberNormSqGrid_nonneg (I := I) (M := M) g₀ P y) _)
    have := hKcd_nn l
    have := hKψ_nn l
    simp only [hKΨ_def]
    linarith
  set F : SmoothCcTensor g₀ 3 2 → ℝ := fun X =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n X).toSection x) with hF_def
  have hFnn : ∀ X, 0 ≤ F X := fun X => riemannianFiberNormSq_nonneg _ _ _ _ _
  have hFadd : ∀ X Y : SmoothCcTensor g₀ 3 2, F (X + Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    simp only [hF_def]
    rw [iteratedCovGrad_add (I := I) g₀ 3 2 n X Y, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (2 + n) x _ _
  have hFneg : ∀ X : SmoothCcTensor g₀ 3 2, F (-X) = F X := by
    intro X
    simp only [hF_def]
    exact l1RiemannianFiberNormSqNeg (I := I) (M := M) g₀ n x X
  have hFsub : ∀ X Y : SmoothCcTensor g₀ 3 2, F (X - Y) ≤ 2 * F X + 2 * F Y := by
    intro X Y
    have h := hFadd X (-Y)
    rw [hFneg Y] at h
    rwa [sub_eq_add_neg]
  have hpiece : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
      (Ψ : SmoothCcTensor g₀ 1 2),
      (∀ (l : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) y
          ((iteratedCovGrad (I := I) g₀ 1 2 l Ψ).toSection y) ≤
        KΨ l * Combinatorics.antidiagonalTupleGridWindow
          (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P y) (l + 2)) →
      F (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ Ψ) ≤ Kpc n * bW := by
    intro σ' ρ Ψ hΨ
    exact hpc g₁ P htie hδ_le hδ0 hδ Ψ hΨ σ' ρ n x
  set A : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) with hA_def
  set B1 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hB1_def
  set B2 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg) with hB2_def
  set B3 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hB3_def
  set B4 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀) with hB4_def
  set B5 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
      (connectionDifferenceSection (I := I) g₁ g₀) with hB5_def
  set B6 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hB6_def
  set C1 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hC1_def
  set C2 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g₀ g₁ g_bg) with hC2_def
  set C3 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hC3_def
  set C4 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀) with hC4_def
  set C5 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connectionDifferenceSection (I := I) g₁ g₀) with hC5_def
  set C6 : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
      (connectionDifferenceSection (I := I) g₁ g₀) with hC6_def
  set D : SmoothCcTensor g₀ 3 2 :=
    lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
      (connectionDifferenceSection (I := I) g₁ g₀) with hD_def
  have hAb : F A ≤ Kpc n * bW := hpiece _ _ _ hΨbg
  have hB1b : F B1 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB2b : F B2 ≤ Kpc n * bW := hpiece _ _ _ hΨpsi
  have hB3b : F B3 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB4b : F B4 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB5b : F B5 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hB6b : F B6 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC1b : F C1 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC2b : F C2 ≤ Kpc n * bW := hpiece _ _ _ hΨpsi
  have hC3b : F C3 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC4b : F C4 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC5b : F C5 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hC6b : F C6 ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have hDb : F D ≤ Kpc n * bW := hpiece _ _ _ hΨcd
  have e1 := hFadd B1 B2
  have e2 := hFsub (B1 + B2) B3
  have e3 := hFsub (B1 + B2 - B3) B4
  have e4 := hFsub (B1 + B2 - B3 - B4) B5
  have e5 := hFsub (B1 + B2 - B3 - B4 - B5) B6
  have f1 := hFadd C1 C2
  have f2 := hFsub (C1 + C2) C3
  have f3 := hFsub (C1 + C2 - C3) C4
  have f4 := hFsub (C1 + C2 - C3 - C4) C5
  have f5 := hFsub (C1 + C2 - C3 - C4 - C5) C6
  have g1 := hFadd A (B1 + B2 - B3 - B4 - B5 - B6)
  have g2 := hFadd (A + (B1 + B2 - B3 - B4 - B5 - B6))
    (C1 + C2 - C3 - C4 - C5 - C6)
  have g3 := hFadd (A + (B1 + B2 - B3 - B4 - B5 - B6) +
    (C1 + C2 - C3 - C4 - C5 - C6)) D
  have hsum : F (A + (B1 + B2 - B3 - B4 - B5 - B6) +
      (C1 + C2 - C3 - C4 - C5 - C6) + D) ≤ 1138 * (Kpc n * bW) := by
    linarith [hAb, hB1b, hB2b, hB3b, hB4b, hB5b, hB6b,
      hC1b, hC2b, hC3b, hC4b, hC5b, hC6b, hDb]
  have hexp : deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg =
      A + (B1 + B2 - B3 - B4 - B5 - B6) + (C1 + C2 - C3 - C4 - C5 - C6) + D :=
    deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg
  change F (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg) ≤ _
  rw [hexp]
  refine hsum.trans ?_
  rw [hbW_def]
  exact le_of_eq (by ring)

theorem lieA1AntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ Kl : ℕ → ℝ, (∀ n, 0 ≤ Kl n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          Kl n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) :=
  lieA1AntidiagonalTupleGridWindowBackground (I := I) (M := M) g₀ g₀ hδ₀

theorem low1AntidiagonalTupleGridWindowBackground (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    {Λ₀ : ℝ} :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              ((-2 : ℝ) • linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g₀ g₁ +
                deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          K n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) := by
  classical
  obtain ⟨Kr, hKr_nn, hr⟩ := exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_antidiagonalTupleGridWindow_bound (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kl, hKl_nn, hl⟩ := lieA1AntidiagonalTupleGridWindowBackground (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun n => 8 * Kr n + 2 * Kl n,
    fun n => by have := hKr_nn n; have := hKl_nn n; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hsup n x
  set R : SmoothCcTensor g₀ 3 2 :=
    linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g₀ g₁ with hR_def
  set L : SmoothCcTensor g₀ 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg with hL_def
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow
    (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) with hW_def
  have hRb : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x) ≤ Kr n * W :=
    hr g₁ P htie hδ_le hδ0 hδ n x
  have hLb : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n L).toSection x) ≤ Kl n * W :=
    hl g₁ P htie hδ_le hδ0 hδ hsup n x
  have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 2 n ((-2 : ℝ) • R)).toSection x) =
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x) := by
    rw [l1IteratedCovGradSmul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
    norm_num
  rw [iteratedCovGrad_add (I := I) g₀ 3 2 n ((-2 : ℝ) • R) L,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (2 + n) x _ _) ?_
  rw [hsm]
  calc 2 * (4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 2 n R).toSection x)) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 2 n L).toSection x)
      ≤ 2 * (4 * (Kr n * W)) + 2 * (Kl n * W) := by linarith [hRb, hLb]
    _ = (8 * Kr n + 2 * Kl n) * W := by ring

theorem low1AntidiagonalTupleGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) {Λ₀ : ℝ} :
    ∃ K : ℕ → ℝ, (∀ n, 0 ≤ K n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hsup : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          (P.toSection y) ≤ Λ₀ ^ 2)
        (n : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 3 2 n
              ((-2 : ℝ) • linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g₀ g₁ +
                deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          K n * Combinatorics.antidiagonalTupleGridWindow
            (covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x) (n + 2) :=
  low1AntidiagonalTupleGridWindowBackground (I := I) (M := M) g₀ g₀ hδ₀

end DifferentialGeometry.Integral.Connection

end
