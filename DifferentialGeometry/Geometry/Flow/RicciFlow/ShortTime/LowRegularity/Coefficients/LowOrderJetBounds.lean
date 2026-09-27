import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.MoserTameBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.ConnectionDifference.OrderOne.KernelRadiusFreeBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.GridWindow.SelfLowCap
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.InsertionDifferenceWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.SelfBounds

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open RicciDeTurckLowOrder

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

section Integrand

theorem firstOrderKernel_jet_bound_background
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T
              (0 : SmoothCcTensor g 0 2) hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  have hΛ₀0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * (1 / 3) :=
    mul_nonneg (Nat.cast_nonneg _) h30
  obtain ⟨Kw, hKw_nn, hw⟩ := low1AntidiagonalTupleGridWindowBackground (I := I) (M := M) g g_bg h31
  obtain ⟨Kint, hKint_nn, hint⟩ := antidiagonalTupleGridWindow_bound_to_covariant_jet_bound (I := I) (M := M) g hΛ₀0
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1),
      Kw q * (∑ k ∈ Finset.range (q + 2), Kint k),
    fun i => Finset.sum_nonneg (fun q _ => mul_nonneg (hKw_nn q)
      (Finset.sum_nonneg (fun k _ => hKint_nn k))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    have hsT : ccTensor02Symm (I := I) (M := M) g T = T := by
      simpa only [ccTensor02Symm] using
        ccTensor02Symm_eq_self (I := I) (M := M) g T hT
    rwa [hsT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    metricPerturbationPath_isControlledMetricPerturbation (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  have heq : ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T
        (0 : SmoothCcTensor g 0 2) hδg hδZ s =
      (-2 : ℝ) • linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδg hδZ s) +
        deTurckLieFirstOrderCoeff (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g_bg := rfl
  have hq : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g 3 2 q
        (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T
          (0 : SmoothCcTensor g 0 2) hδg hδZ s)‖ ^ 2 ≤
      Kw q * (∑ k ∈ Finset.range (q + 2), Kint k) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T 0 s)‖ ^ 2) := by
    intro q
    refine hint (convexPerturbation (I := I) g T 0 s) hPsup 3 2 q 2 _ (Kw q)
      (hKw_nn q) ?_
    intro x
    rw [heq]
    exact hw (metricPerturbationPath (I := I) g T 0 hδg hδZ s)
      (convexPerturbation (I := I) g T 0 s) htie hδ'_le hδ'0 hP hPsup q x
  have hPS : ∀ q : ℕ, q ≤ i →
      (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T 0 s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    intro q hqi
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T 0 s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      hPjet (q + 1)
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
  have hS_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold covariantJetNormSq
  calc ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g 3 2 q
          (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T
            (0 : SmoothCcTensor g 0 2) hδg hδZ s)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          Kw q * (∑ k ∈ Finset.range (q + 2), Kint k) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        refine Finset.sum_le_sum (fun q hqm => ?_)
        refine (hq q).trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hKw_nn q) (Finset.sum_nonneg (fun k _ => hKint_nn k)))
        have := hPS q (by have := Finset.mem_range.mp hqm; omega)
        linarith only [this]
    _ = (∑ q ∈ Finset.range (i + 1),
          Kw q * (∑ k ∈ Finset.range (q + 2), Kint k)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        rw [Finset.sum_mul]

theorem firstOrderKernel_jet_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T
              (0 : SmoothCcTensor g 0 2) hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
  firstOrderKernel_jet_bound_background (I := I) (M := M) g g

omit [SigmaCompactSpace M] in
theorem selfLow_split_bg
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g_bg -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s) +
          (deTurckLieEndoTermField (I := I) (M := M) g gm g_bg -
            deTurckLieEndoTermField (I := I) (M := M) g gm g) +
          (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g gm +
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [selfLow_good (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ hs]
  dsimp only
  have h := tail_base_split (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg
  have h' : lieCorrectionZeroField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg =
      (((lieCorrectionZeroInsertion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg) +
        lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckLieEndoTermField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g := by
    rw [← h]
    abel
  rw [deTurckLieCoeffField_eq_covDerivTerm_add_endoTerm]
  rw [h']
  abel

omit [SigmaCompactSpace M] in
theorem selfLow_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    pathIntegrand (I := I) (M := M) g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g gm +
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  have h := tail_base_split (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g
  rw [sub_self, zero_add] at h
  have h' : lieCorrectionZeroField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g =
      lieCorrectionZeroVectorBundle (I := I) (M := M) g (metricPerturbationPath (I := I) g T 0 hδ hδZ s) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g +
        lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        deTurckLieEndoTermField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g := by
    rw [← h]; abel
  rw [selfLow_good (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  simp only [deTurckLieCoeffField_eq_covDerivTerm_add_endoTerm, h']
  abel

private theorem ricciGoodCap (g₀ : SmoothRiemannianMetric I M)
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
          (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g₀ g₁ P) K := by
  classical
  obtain ⟨KAA, hKAA_nn, hAA⟩ := exists_ricciConnectionDifferenceQuadraticTerm_capWindow (I := I) (M := M) g₀ hδ₀ hΛ1
  obtain ⟨KDA, hKDA_nn, hDA⟩ := exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_capWindow (I := I) (M := M) g₀ hδ₀ hΛ1
  choose SSw hSSw_nn hSSw using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i (ccSlotSwapField (I := I) (M := M) g₀)))
  set KL : ℕ → ℝ := fun i => 2 * KAA i + 2 * KDA i with hKL_def
  have hKL_nn : ∀ i, 0 ≤ KL i := fun i => by
    have := hKAA_nn i; have := hKDA_nn i; simp only [hKL_def]; linarith
  refine ⟨fun i => (1 / 2 : ℝ) ^ 2 * (2 * KL i + 2 * operatorFieldCompositionGridConstant (E := E) 0 0 KL SSw i),
    fun i => by
      have h1 := hKL_nn i
      have h2 := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKL_nn hSSw_nn i
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
      nlinarith [h1, h2], ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0 hP1
  have hLow : HasCapWin (I := I) (M := M) g₀ P
      (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g₀ g₁ +
        ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P) KL :=
    capAdd (I := I) (M := M) g₀ P (hAA g₁ P htie hδ_le hδ0 hδ hP0 hP1)
      (hDA g₁ P htie hδ_le hδ0 hδ hP0 hP1)
  have hSw : HasCapWin (I := I) (M := M) g₀ P
      (ccSlotSwapField (I := I) (M := M) g₀) SSw :=
    capOfBnd (I := I) (M := M) g₀ P _ hSSw_nn (fun i x => hSSw i x)
  have happ := capApp (I := I) (M := M) g₀ P
    (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g₀ g₁ + ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P)
    (ccSlotSwapField (I := I) (M := M) g₀) hKL_nn hSSw_nn hLow hSw
  exact capSmul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
    (capAdd (I := I) (M := M) g₀ P hLow happ)

theorem selfLow_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (pathIntegrand (I := I) (M := M) g g T hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  obtain ⟨Λ₁, hΛ₁0, hΛ₁⟩ := exists_covariantDerivative_pointwise_bound_of_sobolev_ball (I := I) (M := M) hDim g a ha hR₀
  set Λ : ℝ := max 1 (max (((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2) (Λ₁ ^ 2)) with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := le_max_left _ _
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hΛA : ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 ≤ Λ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hΛB : Λ₁ ^ 2 ≤ Λ := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨K1, hK1_nn, w1⟩ := ricciGoodCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨K2, hK2_nn, w2⟩ := lieCovCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨K3, hK3_nn, w3⟩ := exists_lieCorrectionZeroVectorBundle_antidiagonalTupleGridWindow_bound (I := I) (M := M) g h31 hΛ1
  obtain ⟨K4, hK4_nn, w4⟩ := lieCorrectionZeroMixedConnectionCap (I := I) (M := M) g g h31 hΛ1
  obtain ⟨K5, hK5_nn, w5⟩ := lieCorrectionZeroRiemCap (I := I) (M := M) g h31 hΛ1
  obtain ⟨Kint, hKint_nn, hint⟩ := capJet (I := I) (M := M) g hΛ0
  set KS : ℕ → ℝ := fun i =>
    2 * (2 * (2 * (2 * ((-2 : ℝ) ^ 2 * K1 i) + 2 * K2 i) + 2 * K3 i) + 2 * K4 i) +
      2 * K5 i with hKS_def
  have hKS_nn : ∀ i, 0 ≤ KS i := by
    intro i
    have h1 := hK1_nn i; have h2 := hK2_nn i; have h3 := hK3_nn i
    have h4 := hK4_nn i; have h5 := hK5_nn i
    simp only [hKS_def]
    nlinarith [h1, h2, h3, h4, h5]
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1),
      KS q * (∑ k ∈ Finset.range (q + 1), Kint k),
    fun i => Finset.sum_nonneg (fun q _ => mul_nonneg (hKS_nn q)
      (Finset.sum_nonneg (fun k _ => hKint_nn k))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    have hsT : ccTensor02Symm (I := I) (M := M) g T = T := by
      simpa only [ccTensor02Symm] using
        ccTensor02Symm_eq_self (I := I) (M := M) g T hT
    rwa [hsT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    metricPerturbationPath_isControlledMetricPerturbation (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  set P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g P x 0 ≤ Λ := by
    intro x
    refine le_trans ?_ hΛA
    simpa [covariantJetFiberNormSqGrid] using hPsup x
  have hP1 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g P x 1 ≤ Λ := by
    intro x
    refine le_trans ?_ hΛB
    have hsq : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
    have hsm : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) =
        s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) := by
      rw [hPeq, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
        (I := I) (M := M) g 0 2 1 s T,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g 0 (2 + 1) x s _]
    have hT1 := hΛ₁ T hball x
    have hnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g 0 2 1 T).toSection x) :=
      riemannianFiberNormSq_nonneg _ _ _ _ _
    have hgb : covariantJetFiberNormSqGrid (I := I) (M := M) g P x 1 =
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g 0 2 1 P).toSection x) := rfl
    rw [hgb, hsm]
    nlinarith [hT1, hnn, hsq]
  have hwin : HasCapWin (I := I) (M := M) g P
      (pathIntegrand (I := I) (M := M) g g T hδg hδZ s) KS := by
    have e1 := capSmul (I := I) (M := M) g P (-2 : ℝ)
      (w1 (metricPerturbationPath (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1)
    have e2 := w2 T hT hδ_le hδ0 hδg hδZ hs hP0 hP1
    have e3 : HasCapWin (I := I) (M := M) g P
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g (metricPerturbationPath (I := I) g T 0 hδg hδZ s)) K3 :=
      fun n x => w3 (metricPerturbationPath (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1 n x
    have e4 := w4 (metricPerturbationPath (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1
    have e5 := w5 (metricPerturbationPath (I := I) g T 0 hδg hδZ s) P htie hδ'_le hδ'0 hP hP0 hP1
    have hsum := capAdd (I := I) (M := M) g P
      (capAdd (I := I) (M := M) g P
        (capAdd (I := I) (M := M) g P
          (capAdd (I := I) (M := M) g P e1 e2) e3) e4) e5
    refine capCongr (I := I) (M := M) g P ?_ hsum
    rw [selfLow_split (I := I) (M := M) g T hT hδ_lt hδg hδZ hs, hPeq]
  have hq : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g 2 2 q
        (pathIntegrand (I := I) (M := M) g g T hδg hδZ s)‖ ^ 2 ≤
      KS q * (∑ k ∈ Finset.range (q + 1), Kint k) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) :=
    fun q => hint P hP1 _ hKS_nn hwin q
  have hPS : ∀ q : ℕ, q ≤ i →
      (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    intro q hqi
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      hPjet (q + 1)
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
  have hS_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold covariantJetNormSq
  calc ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g 2 2 q
          (pathIntegrand (I := I) (M := M) g g T hδg hδZ s)‖ ^ 2
      ≤ ∑ q ∈ Finset.range (i + 1),
          KS q * (∑ k ∈ Finset.range (q + 1), Kint k) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        refine Finset.sum_le_sum (fun q hqm => ?_)
        refine (hq q).trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hKS_nn q) (Finset.sum_nonneg (fun k _ => hKint_nn k)))
        have := hPS q (by have := Finset.mem_range.mp hqm; omega)
        linarith only [this]
    _ = (∑ q ∈ Finset.range (i + 1),
          KS q * (∑ k ∈ Finset.range (q + 1), Kint k)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        rw [Finset.sum_mul]

private theorem ricciGoodMark (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_hP0 : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1),
        HasMarkedGridWindow (I := I) (M := M) g₀ P
          (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g₀ g₁ P) 2 K := by
  classical
  obtain ⟨KAA, hKAA_nn, hAA⟩ := exists_ricciConnectionDifferenceQuadraticTerm_markWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨KDA, hKDA_nn, hDA⟩ := exists_ricciCovariantDerivativeConnectionDifferenceLowOrder_markWindow (I := I) (M := M) g₀ hδ₀
  choose SSw hSSw_nn hSSw using
    (fun i : ℕ => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i (ccSlotSwapField (I := I) (M := M) g₀)))
  set KL : ℕ → ℝ := fun i => 2 * KAA i + 2 * KDA i with hKL_def
  have hKL_nn : ∀ i, 0 ≤ KL i := fun i => by
    have := hKAA_nn i; have := hKDA_nn i; simp only [hKL_def]; linarith
  refine ⟨fun i => (1 / 2 : ℝ) ^ 2 * (2 * KL i + 2 * operatorFieldCompositionGridConstant (E := E) 0 0 KL SSw i),
    fun i => by
      have h1 := hKL_nn i
      have h2 := operatorFieldCompositionGridConstant_nonneg (E := E) (u := 0) (v := 0) hKL_nn hSSw_nn i
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := by positivity
      nlinarith [h1, h2], ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hP0
  have hLow : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g₀ g₁ +
        ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P) 2 KL :=
    hasMarkedGridWindow_add (I := I) (M := M) g₀ P (hAA g₁ P htie hδ_le hδ0 hδ)
      (hDA g₁ P htie hδ_le hδ0 hδ hP0)
  have hSw : HasMarkedGridWindow (I := I) (M := M) g₀ P
      (ccSlotSwapField (I := I) (M := M) g₀) 0 SSw :=
    hasMarkedGridWindow_of_pointwise_bound (I := I) (M := M) g₀ P _ hSSw_nn (fun i x => hSSw i x)
  have happ := hasMarkedGridWindow_operatorFieldComp (I := I) (M := M) g₀ P
    (ricciConnectionDifferenceQuadraticTerm (I := I) (M := M) g₀ g₁ + ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g₀ g₁ P)
    (ccSlotSwapField (I := I) (M := M) g₀) hKL_nn hSSw_nn hLow hSw
  exact hasMarkedGridWindow_smul (I := I) (M := M) g₀ P (1 / 2 : ℝ)
    (hasMarkedGridWindow_add (I := I) (M := M) g₀ P hLow happ)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M] in
private lemma covariantJetNormSq_le_of_perOrder_bound (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (X : SmoothCcTensor g r c) (i : ℕ) (A B : ℕ → ℝ) {u v : ℝ}
    (hstep : ∀ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g r c q X‖ ^ 2 ≤ (A q + B q * u) * v) :
    covariantJetNormSq (I := I) (M := M) g i X ≤
      ((∑ q ∈ Finset.range (i + 1), A q) +
        (∑ q ∈ Finset.range (i + 1), B q) * u) * v := by
  unfold covariantJetNormSq
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  have hterm : ∀ q : ℕ, (A q + B q * u) * v = A q * v + B q * (u * v) :=
    fun q => by ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompactSpace M] in
private lemma jetTrans (g : SmoothRiemannianMetric I M) {r c : ℕ}
    (X : SmoothCcTensor g r c) (i : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ q, 0 ≤ A q) (hB : ∀ q, 0 ≤ B q)
    (P T : SmoothCcTensor g 0 2)
    (hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2)
    (hX : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g r c q X‖ ^ 2 ≤
      (A q + B q * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)) :
    covariantJetNormSq (I := I) (M := M) g i X ≤
      ((∑ q ∈ Finset.range (i + 1), A q) +
        (∑ q ∈ Finset.range (i + 1), B q) *
          ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  refine covariantJetNormSq_le_of_perOrder_bound (I := I) (M := M) g X i A B (fun q hq => ?_)
  have hqi : q ≤ i := by have := Finset.mem_range.mp hq; omega
  refine le_trans (hX q) ?_
  have hHP_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hHT_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hH3 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) ≤
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => hPk (1 + j))
  have hbud : (1 + ∑ j ∈ Finset.range (q + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
      1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    have h1 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
        ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => hPk j)
    have h2 : (∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ => sq_nonneg _)
    linarith
  have hbud_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (q + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (q + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  refine mul_le_mul (by nlinarith [hB q]) hbud hbud_nn ?_
  nlinarith [hA q, hB q, hHT_nn]

theorem lieBackgroundJet
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g T x v w =
            ccTensorBilin (I := I) g T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((convexPerturbation (I := I) g T 0 s).toSection x) ≤ 1)
        (i : ℕ),
        covariantJetNormSq (I := I) (M := M) g i
            ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g_bg -
              deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδg hδZ
                lieDecompositionQ lieDecompositionEps s) +
              (deTurckLieEndoTermField (I := I) (M := M) g
                  (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g_bg -
                deTurckLieEndoTermField (I := I) (M := M) g
                  (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g)) ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Ac, Bc, hAc_nn, hBc_nn, hcov⟩ :=
    lieCovJet (I := I) (M := M) hDim g hδ₀
  obtain ⟨Ca, hCa_nn, hCa⟩ := palatiniCovDerivTermDiff_pointwise_gridWindow (I := I) (M := M) g g_bg hδ₀
  obtain ⟨Cb, hCb_nn, hCb⟩ := palatiniEndoTermDiff_pointwise_gridWindow (I := I) (M := M) g g_bg hδ₀
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_covariant_jet_bound (I := I) (M := M) g (Λ₀ := 1) zero_le_one
  set Aa : ℕ → ℝ := fun q => Ca q * ∑ k ∈ Finset.range (q + 2), Kint k with hAa_def
  set Ab : ℕ → ℝ := fun q => Cb q * ∑ k ∈ Finset.range (q + 2), Kint k with hAb_def
  have hAa_nn : ∀ q, 0 ≤ Aa q := fun q =>
    mul_nonneg (hCa_nn q) (Finset.sum_nonneg fun k _ => hKint_nn k)
  have hAb_nn : ∀ q, 0 ≤ Ab q := fun q =>
    mul_nonneg (hCb_nn q) (Finset.sum_nonneg fun k _ => hKint_nn k)
  refine ⟨fun i => 4 * (∑ q ∈ Finset.range (i + 1), Ac q) +
      4 * (∑ q ∈ Finset.range (i + 1), Aa q) +
      2 * (∑ q ∈ Finset.range (i + 1), Ab q),
    fun i => 4 * (∑ q ∈ Finset.range (i + 1), Bc q),
    fun i => by
      have h1 : 0 ≤ ∑ q ∈ Finset.range (i + 1), Ac q :=
        Finset.sum_nonneg fun q _ => hAc_nn q
      have h2 : 0 ≤ ∑ q ∈ Finset.range (i + 1), Aa q :=
        Finset.sum_nonneg fun q _ => hAa_nn q
      have h3 : 0 ≤ ∑ q ∈ Finset.range (i + 1), Ab q :=
        Finset.sum_nonneg fun q _ => hAb_nn q
      linarith,
    fun i => mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun q _ => hBc_nn q), ?_⟩
  intro T hT δ hδ_le hδ0 hδg hδZ s hs hP0 i
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδg hδZ s with hgm_def
  set P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain (lt_of_le_of_lt hδ_le hδ₀)
      (lt_of_le_of_lt hδ_le hδ₀) hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    rw [hgm_def, hP_def]
    exact metricPerturbationPath_inner_of_mem (I := I) g T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rw [hP_def]
    rwa [heq] at hraw
  have hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    intro k
    rw [hPeq, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g 0 2 k s T, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 k T‖, hsq]
  have hP0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x
    simpa only [one_pow, hP_def] using hP0 x
  let Xc : SmoothCcTensor g 2 2 :=
    deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g -
      deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδg hδZ lieDecompositionQ lieDecompositionEps s
  let Xa : SmoothCcTensor g 2 2 :=
    deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g_bg -
      deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g
  let Xb : SmoothCcTensor g 2 2 :=
    deTurckLieEndoTermField (I := I) (M := M) g gm g_bg -
      deTurckLieEndoTermField (I := I) (M := M) g gm g
  have hcovL : covariantJetNormSq (I := I) (M := M) g i Xc ≤
      ((∑ q ∈ Finset.range (i + 1), Ac q) +
          (∑ q ∈ Finset.range (i + 1), Bc q) *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    apply jetTrans (I := I) (M := M) g Xc i Ac Bc hAc_nn hBc_nn P T hPk
    intro q
    simpa only [Xc, gm] using
      hcov T hT hδ_le hδ0 hδg hδZ hs hP0 q
  have haStep : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 2 2 q Xa‖ ^ 2 ≤
        (Aa q + 0 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) *
          (1 + ∑ j ∈ Finset.range (q + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
    intro q
    have hpt := hCa gm P htie hδ_le hδ0 hδP q
    have hraw := hint P hP0' 2 2 q 2
      (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g_bg -
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g)
      (Ca q) (hCa_nn q) hpt
    have hxa : Xa =
        deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g_bg -
          deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g gm g := by
      dsimp only [Xa]
      congr 1
    rw [hxa]
    simpa only [hAa_def, zero_mul, add_zero] using hraw
  have hbStep : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 2 2 q Xb‖ ^ 2 ≤
        (Ab q + 0 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) *
          (1 + ∑ j ∈ Finset.range (q + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
    intro q
    have hpt := hCb gm P htie hδ_le hδ0 hδP q
    have hraw := hint P hP0' 2 2 q 2
      (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g)
      (Cb q) (hCb_nn q) hpt
    have hxb : Xb =
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g := by
      simp only [Xb, DifferentialGeometry.Integral.Connection.deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion]
    rw [hxb]
    simpa only [hAb_def, zero_mul, add_zero] using hraw
  have haL : covariantJetNormSq (I := I) (M := M) g i Xa ≤
      (∑ q ∈ Finset.range (i + 1), Aa q) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    simpa only [Finset.sum_const_zero, zero_mul, add_zero] using
      (jetTrans (I := I) (M := M) g Xa i Aa (fun _ => 0) hAa_nn
        (fun _ => le_rfl) P T hPk haStep)
  have hbL : covariantJetNormSq (I := I) (M := M) g i Xb ≤
      (∑ q ∈ Finset.range (i + 1), Ab q) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    simpa only [Finset.sum_const_zero, zero_mul, add_zero] using
      (jetTrans (I := I) (M := M) g Xb i Ab (fun _ => 0) hAb_nn
        (fun _ => le_rfl) P T hPk hbStep)
  have hrw :
      (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g_bg -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδg hδZ lieDecompositionQ lieDecompositionEps s) +
        (deTurckLieEndoTermField (I := I) (M := M) g gm g_bg -
          deTurckLieEndoTermField (I := I) (M := M) g gm g) =
      (Xc + Xa) + Xb := by
    dsimp only [Xc, Xa, Xb]
    abel
  rw [hrw]
  have j1 := covariantJetNormSq_add_le (I := I) (M := M) g i Xc Xa
  have j2 := covariantJetNormSq_add_le (I := I) (M := M) g i (Xc + Xa) Xb
  have hfin :
      ((4 * (∑ q ∈ Finset.range (i + 1), Ac q) +
          4 * (∑ q ∈ Finset.range (i + 1), Aa q) +
          2 * (∑ q ∈ Finset.range (i + 1), Ab q)) +
        (4 * (∑ q ∈ Finset.range (i + 1), Bc q)) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) =
      4 * (((∑ q ∈ Finset.range (i + 1), Ac q) +
          (∑ q ∈ Finset.range (i + 1), Bc q) *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
      4 * ((∑ q ∈ Finset.range (i + 1), Aa q) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) +
      2 * ((∑ q ∈ Finset.range (i + 1), Ab q) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) := by
    ring
  rw [hfin]
  linarith [j1, j2, hcovL, haL, hbL]

theorem insBackgroundJet
    (g g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K0 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (_hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          ((convexPerturbation (I := I) g T 0 s).toSection x) ≤ 1)
        (i : ℕ),
        covariantJetNormSq (I := I) (M := M) g i
            (lieCorrectionZeroInsertion (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g_bg -
              lieCorrectionZeroInsertion (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδg hδZ s) g) ≤
          K0 i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := lieCorrectionZeroInsDiffAntidiagonalTupleGridWindow (I := I) (M := M) g g_bg hδ₀
  obtain ⟨Kint, hKint_nn, hint⟩ :=
    antidiagonalTupleGridWindow_bound_to_covariant_jet_bound (I := I) (M := M) g (Λ₀ := 1) zero_le_one
  set A : ℕ → ℝ := fun q =>
    C q * ∑ k ∈ Finset.range (q + 2), Kint k with hA_def
  have hA_nn : ∀ q, 0 ≤ A q := fun q =>
    mul_nonneg (hC_nn q) (Finset.sum_nonneg fun k _ => hKint_nn k)
  refine ⟨fun i => ∑ q ∈ Finset.range (i + 1), A q,
    fun i => Finset.sum_nonneg (fun q _ => hA_nn q), ?_⟩
  intro T δ hδ_le hδ0 hδg hδZ s hs hP0 i
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδg hδZ s with hgm_def
  set P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hsmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain (lt_of_le_of_lt hδ_le hδ₀)
      (lt_of_le_of_lt hδ_le hδ₀) hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w + ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    rw [hgm_def, hP_def]
    exact metricPerturbationPath_inner_of_mem (I := I) g T 0 hδg hδZ hsmem y v w
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδg hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rw [hP_def]
    rwa [heq] at hraw
  have hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    intro k
    rw [hPeq, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g 0 2 k s T,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 k T‖, hsq]
  have hP0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (P.toSection x) ≤ (1 : ℝ) ^ 2 := by
    intro x
    simpa only [one_pow, hP_def] using hP0 x
  let X : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
      lieCorrectionZeroInsertion (I := I) (M := M) g gm g
  have hstep : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 2 2 q X‖ ^ 2 ≤
        (A q + 0 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) P‖ ^ 2) *
          (1 + ∑ j ∈ Finset.range (q + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
    intro q
    have hpt := hC gm P htie hδ_le hδ0 hδP q
    have hraw := hint P hP0' 2 2 q 2 X (C q) (hC_nn q) hpt
    simpa only [hA_def, zero_mul, add_zero] using hraw
  simpa only [X, Finset.sum_const_zero, zero_mul, add_zero] using
    (jetTrans (I := I) (M := M) g X i A (fun _ => 0) hA_nn
      (fun _ => le_rfl) P T hPk hstep)

private theorem ricciGoodJet (hDim : Module.finrank ℝ E = 3)
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
            (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g₀ g₁ P)‖ ^ 2 ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + j) P‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨KG, hKG_nn, wG⟩ := ricciGoodMark (I := I) (M := M) g₀ hδ₀
  obtain ⟨K0', hK0'_nn, hjet⟩ := markedGridWindow_jet_bound (I := I) (M := M) g₀
  obtain ⟨cg, hcg_nn, hcg⟩ := gradCapLin (I := I) (M := M) hDim g₀
  refine ⟨fun i => KG i * K0' i, fun i => KG i * K0' i * cg,
    fun i => mul_nonneg (hKG_nn i) (hK0'_nn i),
    fun i => mul_nonneg (mul_nonneg (hKG_nn i) (hK0'_nn i)) hcg_nn, ?_⟩
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
  have hP0g : ∀ x : M, covariantJetFiberNormSqGrid (I := I) (M := M) g₀ P x 0 ≤ 1 := by
    intro x; simpa [covariantJetFiberNormSqGrid] using hP0 x
  have hres := hjet P (Λ₀ := 1) zero_le_one (le_refl _) hΛ₁0 hsup hcap
    (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g₀ g₁ P) hKG_nn
    (wG g₁ P htie hδ_le hδ0 hδ hP0g) i
  refine hres.trans (le_of_eq ?_)
  rw [hΛ₁sq]
  ring

theorem selfLowJetQBackground
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (pathIntegrand (I := I) (M := M) g g_bg T hδg hδZ s) ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  have h30 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h31 : (1 / 3 : ℝ) < 1 := by norm_num
  obtain ⟨A1, B1, hA1_nn, hB1_nn, w1⟩ := ricciGoodJet (I := I) (M := M) hDim g h31
  obtain ⟨A2, B2, hA2_nn, hB2_nn, w2⟩ := lieBackgroundJet (I := I) (M := M) hDim g g_bg h31
  obtain ⟨A3, hA3_nn, w3⟩ := insBackgroundJet (I := I) (M := M) g g_bg h31
  obtain ⟨A4, B4, hA4_nn, hB4_nn, w4⟩ := exists_lieCorrectionZeroVectorBundle_iteratedCovGrad_norm_sq_bound (I := I) (M := M) hDim g h31
  obtain ⟨A5, B5, hA5_nn, hB5_nn, w5⟩ :=
    lieCorrectionZeroMixedConnectionJetBackground (I := I) (M := M) hDim g g_bg h31
  obtain ⟨A6, hA6_nn, w6⟩ := lieCorrectionZeroRiemJet (I := I) (M := M) g h31
  refine ⟨fun i => 128 * (∑ q ∈ Finset.range (i + 1), A1 q) +
      32 * A2 i + 16 * A3 i +
      8 * (∑ q ∈ Finset.range (i + 1), A4 q) +
      4 * (∑ q ∈ Finset.range (i + 1), A5 q) +
      2 * (∑ q ∈ Finset.range (i + 1), A6 q),
    fun i => 128 * (∑ q ∈ Finset.range (i + 1), B1 q) +
      32 * B2 i +
      8 * (∑ q ∈ Finset.range (i + 1), B4 q) +
      4 * (∑ q ∈ Finset.range (i + 1), B5 q),
    fun i => by
      have s1 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A1 q :=
        Finset.sum_nonneg (fun q _ => hA1_nn q)
      have s2 : (0 : ℝ) ≤ A2 i := hA2_nn i
      have s3 : (0 : ℝ) ≤ A3 i := hA3_nn i
      have s4 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A4 q :=
        Finset.sum_nonneg (fun q _ => hA4_nn q)
      have s5 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A5 q :=
        Finset.sum_nonneg (fun q _ => hA5_nn q)
      have s6 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), A6 q :=
        Finset.sum_nonneg (fun q _ => hA6_nn q)
      linarith,
    fun i => by
      have s1 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B1 q :=
        Finset.sum_nonneg (fun q _ => hB1_nn q)
      have s2 : (0 : ℝ) ≤ B2 i := hB2_nn i
      have s4 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B4 q :=
        Finset.sum_nonneg (fun q _ => hB4_nn q)
      have s5 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), B5 q :=
        Finset.sum_nonneg (fun q _ => hB5_nn q)
      linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le h31
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hTsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (T.toSection x) ≤ ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_ccTensor02Symm_zero_le_fibreSmall
      (I := I) (M := M) g h30 T hδ_le hδ0 hδg x
    have hsT : ccTensor02Symm (I := I) (M := M) g T = T := by
      simpa only [ccTensor02Symm] using
        ccTensor02Symm_eq_self (I := I) (M := M) g T hT
    rwa [hsT] at h
  obtain ⟨⟨δ', hδ'0, hδ'_le, hP⟩, htie, hPsup, hPjet⟩ :=
    metricPerturbationPath_isControlledMetricPerturbation (I := I) (M := M) g T hδ0 hδ_le hδ_lt hδg hδZ hTsup hs
  set gm : SmoothRiemannianMetric I M := metricPerturbationPath (I := I) g T 0 hδg hδZ s with hgm_def
  set P : SmoothCcTensor g 0 2 := convexPerturbation (I := I) g T 0 s with hP_def
  have hPeq : P = s • T := by
    rw [hP_def, convexPerturbation, smul_zero, zero_add]
  have hone : ((Module.finrank ℝ E : ℝ) * (1 / 3)) ^ 2 = 1 := by
    rw [hDim]; norm_num
  have hP0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 x
      (P.toSection x) ≤ 1 := by
    intro x
    have h := hPsup x
    rwa [hone] at h
  have hPk : ∀ k : ℕ, ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    intro k
    rw [hPeq, DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
      (I := I) (M := M) g 0 2 k s T, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 k T‖, hsq]
  set H3 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 with hH3_def
  set JS : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 with hJS_def
  have e1 : covariantJetNormSq (I := I) (M := M) g i
      ((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) ≤
      4 * (((∑ q ∈ Finset.range (i + 1), A1 q) +
        (∑ q ∈ Finset.range (i + 1), B1 q) * H3) * JS) := by
    rw [covariantJetNormSq_smul (I := I) (M := M) g i (-2 : ℝ)
      (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P)]
    have h := jetTrans (I := I) (M := M) g
      (symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) i A1 B1 hA1_nn hB1_nn P T hPk
      (fun q => w1 gm P htie hδ'_le hδ'0 hP hP0 q)
    have hnn : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
    nlinarith [h, hnn]
  let L : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g_bg -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδg hδZ
          lieDecompositionQ lieDecompositionEps s) +
      (deTurckLieEndoTermField (I := I) (M := M) g gm g_bg -
        deTurckLieEndoTermField (I := I) (M := M) g gm g)
  let X : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
      lieCorrectionZeroInsertion (I := I) (M := M) g gm g
  have e2 : covariantJetNormSq (I := I) (M := M) g i
      L ≤
      (A2 i + B2 i * H3) * JS := by
    simpa only [L, hgm_def, hH3_def, hJS_def] using
      w2 T hT hδ_le hδ0 hδg hδZ hs hP0 i
  have e3 : covariantJetNormSq (I := I) (M := M) g i
      X ≤ A3 i * JS := by
    simpa only [X, hgm_def, hJS_def] using
      w3 T hδ_le hδ0 hδg hδZ hs hP0 i
  have e4 : covariantJetNormSq (I := I) (M := M) g i (lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) ≤
      ((∑ q ∈ Finset.range (i + 1), A4 q) +
        (∑ q ∈ Finset.range (i + 1), B4 q) * H3) * JS :=
    jetTrans (I := I) (M := M) g _ i A4 B4 hA4_nn hB4_nn P T hPk
      (fun q => w4 gm P htie hδ'_le hδ'0 hP hP0 q)
  have e5 : covariantJetNormSq (I := I) (M := M) g i
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg) ≤
      ((∑ q ∈ Finset.range (i + 1), A5 q) +
        (∑ q ∈ Finset.range (i + 1), B5 q) * H3) * JS :=
    jetTrans (I := I) (M := M) g _ i A5 B5 hA5_nn hB5_nn P T hPk
      (fun q => w5 gm P htie hδ'_le hδ'0 hP hP0 q)
  have e6 : covariantJetNormSq (I := I) (M := M) g i (lieCorrectionZeroRiemann (I := I) (M := M) g gm) ≤
      ((∑ q ∈ Finset.range (i + 1), A6 q) +
        (∑ q ∈ Finset.range (i + 1), (0 : ℝ)) * H3) * JS := by
    refine jetTrans (I := I) (M := M) g _ i A6 (fun _ => 0) hA6_nn
      (fun _ => le_refl 0) P T hPk (fun q => ?_)
    have h := w6 gm P htie hδ'_le hδ'0 hP hP0 q
    refine h.trans (le_of_eq ?_)
    ring
  have hrw : pathIntegrand (I := I) (M := M) g g_bg T hδg hδZ s =
      ((((((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P + L) + X) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm) := by
    rw [selfLow_split_bg (I := I) (M := M) g g_bg T hT hδ_lt hδg hδZ hs, hPeq]
    dsimp only [L, X]
    abel
  rw [hrw]
  have j5 := covariantJetNormSq_add_le (I := I) (M := M) g i
    (((((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P + L) + X) +
      lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
      lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg)
    (lieCorrectionZeroRiemann (I := I) (M := M) g gm)
  have j4 := covariantJetNormSq_add_le (I := I) (M := M) g i
    ((((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P + L) + X) +
      lieCorrectionZeroVectorBundle (I := I) (M := M) g gm)
    (lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g_bg)
  have j3 := covariantJetNormSq_add_le (I := I) (M := M) g i
    (((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P + L) + X)
    (lieCorrectionZeroVectorBundle (I := I) (M := M) g gm)
  have j2 := covariantJetNormSq_add_le (I := I) (M := M) g i
    ((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P + L) X
  have j1 := covariantJetNormSq_add_le (I := I) (M := M) g i
    ((-2 : ℝ) • symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P)
    L
  have hfin : (128 * (∑ q ∈ Finset.range (i + 1), A1 q) +
      32 * A2 i + 16 * A3 i +
      8 * (∑ q ∈ Finset.range (i + 1), A4 q) +
      4 * (∑ q ∈ Finset.range (i + 1), A5 q) +
      2 * (∑ q ∈ Finset.range (i + 1), A6 q) +
      (128 * (∑ q ∈ Finset.range (i + 1), B1 q) +
        32 * B2 i +
        8 * (∑ q ∈ Finset.range (i + 1), B4 q) +
        4 * (∑ q ∈ Finset.range (i + 1), B5 q)) * H3) * JS =
      32 * (4 * (((∑ q ∈ Finset.range (i + 1), A1 q) +
          (∑ q ∈ Finset.range (i + 1), B1 q) * H3) * JS)) +
        32 * ((A2 i + B2 i * H3) * JS) +
        16 * (A3 i * JS) +
        8 * (((∑ q ∈ Finset.range (i + 1), A4 q) +
          (∑ q ∈ Finset.range (i + 1), B4 q) * H3) * JS) +
        4 * (((∑ q ∈ Finset.range (i + 1), A5 q) +
          (∑ q ∈ Finset.range (i + 1), B5 q) * H3) * JS) +
        2 * (((∑ q ∈ Finset.range (i + 1), A6 q) +
          (∑ q ∈ Finset.range (i + 1), (0 : ℝ)) * H3) * JS) := by
    simp only [Finset.sum_const_zero]
    ring
  rw [hfin]
  linarith [j1, j2, j3, j4, j5, e1, e2, e3, e4, e5, e6]

theorem selfLow_jet_quad
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        covariantJetNormSq (I := I) (M := M) g i
            (pathIntegrand (I := I) (M := M) g g T hδg hδZ s) ≤
          (K0 i + K2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
  selfLowJetQBackground (I := I) (M := M) hDim g g

end Integrand

section Towers

theorem firstOrderCoefficient_jet_tower_quadratic_background
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := firstOrderKernel_jet_bound_background (I := I) (M := M) g g_bg
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set Λ : ℝ := Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Λ := mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 i
    (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T
      (0 : SmoothCcTensor g 0 2) hδg hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g_bg T
      (0 : SmoothCcTensor g 0 2) hδg hδZ)
    (fun s hs => by
      rw [hsΛ, hΛdef]
      simpa only [covariantJetNormSq] using
        hker T hT hδ0 hδ_le hδg hδZ i s hs)
  rw [hsΛ] at hpath
  have hjet : covariantJetNormSq (I := I) (M := M) g i
      (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδg hδZ).firstOrderCoefficient ≤ Λ := by
    rw [firstOrderCoefficient_eq (I := I) (M := M) g g_bg T hδ_lt hδg hδZ]
    simpa only [ricciDeTurckRemainderFirstOrderPathIntegral, covariantJetNormSq] using hpath
  refine le_trans ?_ hjet
  unfold covariantJetNormSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 3 2 q
      (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδg hδZ).firstOrderCoefficient‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

theorem firstOrderCoefficient_jet_tower_quadratic
    (g : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
  firstOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) g g

theorem firstOrderCoefficient_jet_tower_background
    (g g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) {R₀ : ℝ} :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kc, hKc_nn, h⟩ := firstOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) g g_bg
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ _ i
  exact h T hT hδ0 hδ_le hδg hδZ i

theorem firstOrderCoefficient_jet_tower
    (g : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 3 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
  firstOrderCoefficient_jet_tower_background (I := I) (M := M) g g a

theorem zeroOrderCoefficient_jet_tower
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).zeroOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := selfLow_jet (I := I) (M := M) hDim g a ha hR₀
  refine ⟨fun i => 2 * (Kk i +
      covariantJetNormSq (I := I) (M := M) g i (-metricPrincipalDefectCurvCoeff (I := I) g g)),
    fun i => by
      have := covariantJetNormSq_nonneg (I := I) (M := M) (m := i) g
        (-metricPrincipalDefectCurvCoeff (I := I) g g)
      have := hKk_nn i
      linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set Λ : ℝ := Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Λ := mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 i
    (pathIntegrand (I := I) (M := M) g g T hδg hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (selfLow_joint (I := I) (M := M) g g T hδg hδZ)
    (fun s hs => by
      rw [hsΛ, hΛdef]
      simpa only [covariantJetNormSq] using
        hker T hT hδ0 hδ_le hδg hδZ hball i s hs)
  rw [hsΛ] at hpath
  have hint : covariantJetNormSq (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g T hδ_lt hδg hδZ) ≤ Λ := by
    simpa only [selfLowInt, covariantJetNormSq] using hpath
  have hfix : (0 : ℝ) ≤ covariantJetNormSq (I := I) (M := M) g i
      (-metricPrincipalDefectCurvCoeff (I := I) g g) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := i) g (-metricPrincipalDefectCurvCoeff (I := I) g g)
  have hjet : covariantJetNormSq (I := I) (M := M) g i
      (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδg hδZ).zeroOrderCoefficient ≤
      2 * (Kk i +
        covariantJetNormSq (I := I) (M := M) g i (-metricPrincipalDefectCurvCoeff (I := I) g g)) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    have hsplit := covariantJetNormSq_sub_le (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g T hδ_lt hδg hδZ)
      (-metricPrincipalDefectCurvCoeff (I := I) g g)
    rw [sub_neg_eq_add] at hsplit
    rw [zeroOrderCoefficient_eq (I := I) (M := M) g g T hδ_lt hδg hδZ]
    refine hsplit.trans ?_
    have : Λ + covariantJetNormSq (I := I) (M := M) g i
          (-metricPrincipalDefectCurvCoeff (I := I) g g) ≤
        (Kk i + covariantJetNormSq (I := I) (M := M) g i
            (-metricPrincipalDefectCurvCoeff (I := I) g g)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
      rw [hΛdef]
      nlinarith [hsum, hfix]
    linarith only [hint, this]
  refine le_trans ?_ hjet
  unfold covariantJetNormSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 2 2 q
      (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδg hδZ).zeroOrderCoefficient‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

theorem zeroOrderCoefficient_jet_tower_quadratic_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).zeroOrderCoefficient‖ ^ 2 ≤
            (K0 i + K2 i * ∑ j ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk0, Kk2, hKk0_nn, hKk2_nn, hker⟩ :=
    selfLowJetQBackground (I := I) (M := M) hDim g g_bg
  refine ⟨fun i => 2 * (Kk0 i +
      covariantJetNormSq (I := I) (M := M) g i (-metricPrincipalDefectCurvCoeff (I := I) g g)),
    fun i => 2 * Kk2 i,
    fun i => by
      have := covariantJetNormSq_nonneg (I := I) (M := M) (m := i) g
        (-metricPrincipalDefectCurvCoeff (I := I) g g)
      have := hKk0_nn i
      linarith,
    fun i => by have := hKk2_nn i; linarith, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hH3 : (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Λ : ℝ := (Kk0 i + Kk2 i * ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
    (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg (add_nonneg (hKk0_nn i) (mul_nonneg (hKk2_nn i) hH3))
      (by linarith)
  have hsΛ : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hΛ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 i
    (pathIntegrand (I := I) (M := M) g g_bg T hδg hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (selfLow_joint (I := I) (M := M) g g_bg T hδg hδZ)
    (fun s hs => by
      rw [hsΛ, hΛdef]
      simpa only [covariantJetNormSq] using
        hker T hT hδ0 hδ_le hδg hδZ i s hs)
  rw [hsΛ] at hpath
  have hint : covariantJetNormSq (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδg hδZ) ≤ Λ := by
    simpa only [selfLowInt, covariantJetNormSq] using hpath
  have hfix : (0 : ℝ) ≤ covariantJetNormSq (I := I) (M := M) g i
      (-metricPrincipalDefectCurvCoeff (I := I) g g) :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := i) g (-metricPrincipalDefectCurvCoeff (I := I) g g)
  have hjet : covariantJetNormSq (I := I) (M := M) g i
      (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδg hδZ).zeroOrderCoefficient ≤
      (2 * (Kk0 i + covariantJetNormSq (I := I) (M := M) g i
            (-metricPrincipalDefectCurvCoeff (I := I) g g)) +
          2 * Kk2 i * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
    have hsplit := covariantJetNormSq_sub_le (I := I) (M := M) g i
      (selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδg hδZ)
      (-metricPrincipalDefectCurvCoeff (I := I) g g)
    rw [sub_neg_eq_add] at hsplit
    rw [zeroOrderCoefficient_eq (I := I) (M := M) g g_bg T hδ_lt hδg hδZ]
    refine hsplit.trans ?_
    have hstep : 2 * (Λ + covariantJetNormSq (I := I) (M := M) g i
          (-metricPrincipalDefectCurvCoeff (I := I) g g)) ≤
        (2 * (Kk0 i + covariantJetNormSq (I := I) (M := M) g i
              (-metricPrincipalDefectCurvCoeff (I := I) g g)) +
            2 * Kk2 i * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
      rw [hΛdef]
      nlinarith [mul_nonneg hfix hsum, hfix, hsum, hH3,
        hKk0_nn i, hKk2_nn i, mul_nonneg (hKk2_nn i) hH3]
    linarith only [hint, hstep]
  refine le_trans ?_ hjet
  unfold covariantJetNormSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 2 2 q
      (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδg hδZ).zeroOrderCoefficient‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

theorem zeroOrderCoefficient_jet_tower_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).zeroOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨K0, K2, hK0_nn, hK2_nn, hQ⟩ :=
    zeroOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) hDim g g_bg
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
      (I := I) (M := M) g (a + 2)
  refine ⟨fun i => K0 i + K2 i * (3 * (C * R₀) ^ 2),
    fun i => add_nonneg (hK0_nn i)
      (mul_nonneg (hK2_nn i) (mul_nonneg (by norm_num) (sq_nonneg _))), ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ hball i
  have hsum := hC T
  have hcast :
      ‖smoothCcToTensorHs (I := I) (M := M) g ((a + 2 : ℕ) : ℝ) T‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; ring) T
  rw [hcast] at hsum
  have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g 0 2 l T‖ ≤ C * R₀ :=
    le_trans hsum (mul_le_mul_of_nonneg_left hball hC_nn)
  have hCR_nn : 0 ≤ C * R₀ := mul_nonneg hC_nn hR₀
  have hjet3 : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ≤ C * R₀ := by
    intro j hjmem
    refine le_trans (Finset.single_le_sum
      (fun l _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 l T))
      (Finset.mem_range.mpr ?_)) hsumB
    have hj3 : j < 3 := Finset.mem_range.mp hjmem
    omega
  have hH3 : ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤
        3 * (C * R₀) ^ 2 := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤
          ∑ j ∈ Finset.range 3, (C * R₀) ^ 2 :=
        Finset.sum_le_sum (fun j hjmem =>
          pow_le_pow_left₀ (norm_nonneg _) (hjet3 j hjmem) 2)
      _ = 3 * (C * R₀) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
  have hJS : 0 ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
    have : 0 ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  refine (hQ T hT hδ0 hδ_le hδg hδZ i).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add (le_refl (K0 i))
      (mul_le_mul_of_nonneg_left hH3 (hK2_nn i))) hJS

theorem zeroOrderCoefficient_jet_tower_quadratic
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K0 K2 : ℕ → ℝ, (∀ i, 0 ≤ K0 i) ∧ (∀ i, 0 ≤ K2 i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 2 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).zeroOrderCoefficient‖ ^ 2 ≤
            (K0 i + K2 i * ∑ j ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
  zeroOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) hDim g g

end Towers

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
