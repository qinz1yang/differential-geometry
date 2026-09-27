import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowerOrderTerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.RicciTerms

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (sq_add_sq_le_sq_add_of_nonneg)
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs deTurckLieTopOrderPairingFamily lieCorrectionZeroMixedConnection lieCorrectionZeroInsertion lieCorrectionZeroRiemann
  lieCorrectionZeroVectorBundle lieCorrectionZeroField tail_base_split)
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_smul)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private theorem deTurckSmoothRemainder_self_low_order_decomposition
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
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
              (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s)) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [RicciDeTurckLowOrder.selfLow_good
    (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
            lieCorrectionZeroField (I := I) (M := M) g gm g - Q =
        (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoTermField (I := I) (M := M) g gm g -
            deTurckLieEndoTermField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm) := by
    rw [deTurckLieCoeffField_eq_covDerivTerm_add_endoTerm]
    rw [← tail_base_split (I := I) (M := M) g gm g]
    abel
  calc
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
            (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient
            (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoTermField (I := I) (M := M) g gm g -
            deTurckLieEndoTermField (I := I) (M := M) g gm g) +
          ((((lieCorrectionZeroInsertion (I := I) (M := M) g gm g -
                lieCorrectionZeroInsertion (I := I) (M := M) g gm g) +
              lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
            lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm)) := by
      rw [hlie]
    _ = _ := by
      simp only [sub_self, zero_add, add_zero]
      abel

omit [SigmaCompactSpace M] in
private theorem deTurckSmoothRemainder_self_low_order_sub_decomposition
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδT hδZ s -
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g U hδU hδZ s =
      (((((-2 : ℝ) •
            (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
                (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
              RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
                (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U)) +
          ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s))) +
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
          lieCorrectionZeroVectorBundle (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) +
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g)) +
        (lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
          lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s))) := by
  rw [deTurckSmoothRemainder_self_low_order_decomposition (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    deTurckSmoothRemainder_self_low_order_decomposition (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  dsimp only
  module

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_weighted_five_term_sum_le
    (g : SmoothRiemannianMetric I M)
    (Y1 Y2 Y3 Y4 Y5 : SmoothCcTensor g 2 2)
    (Z1 Z2 Z3 Z4 Z5 : ℝ)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hZ4 : 0 ≤ Z4) (hZ5 : 0 ≤ Z5)
    (hY1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Z1 ^ 2)
    (hY2 : covariantJetNormSq (I := I) (M := M) g 2 Y2 ≤ Z2 ^ 2)
    (hY3 : covariantJetNormSq (I := I) (M := M) g 2 Y3 ≤ Z3 ^ 2)
    (hY4 : covariantJetNormSq (I := I) (M := M) g 2 Y4 ≤ Z4 ^ 2)
    (hY5 : covariantJetNormSq (I := I) (M := M) g 2 Y5 ≤ Z5 ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2 (((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) + Y5) ≤
      (4 * (2 * Z1 + Z2 + Z3 + Z4 + Z5)) ^ 2 := by
  have hj1 : covariantJetNormSq (I := I) (M := M) g 2 ((-2 : ℝ) • Y1) ≤ (2 * Z1) ^ 2 := by
    rw [covariantJetNormSq_smul]
    have h4 : ((-2 : ℝ)) ^ 2 = 4 := by norm_num
    have he : (2 * Z1) ^ 2 = 4 * Z1 ^ 2 := by ring
    rw [h4, he]
    exact mul_le_mul_of_nonneg_left hY1 (by norm_num)
  have h12 : covariantJetNormSq (I := I) (M := M) g 2 ((-2 : ℝ) • Y1 + Y2) ≤
      2 * ((2 * Z1) ^ 2 + Z2 ^ 2) := by
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 ((-2 : ℝ) • Y1) Y2).trans
      (mul_le_mul_of_nonneg_left (add_le_add hj1 hY2) (by norm_num))
  have h123 : covariantJetNormSq (I := I) (M := M) g 2 (((-2 : ℝ) • Y1 + Y2) + Y3) ≤
      2 * (2 * ((2 * Z1) ^ 2 + Z2 ^ 2) + Z3 ^ 2) := by
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 ((-2 : ℝ) • Y1 + Y2) Y3).trans
      (mul_le_mul_of_nonneg_left (add_le_add h12 hY3) (by norm_num))
  have h1234 : covariantJetNormSq (I := I) (M := M) g 2 ((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) ≤
      2 * (2 * (2 * ((2 * Z1) ^ 2 + Z2 ^ 2) + Z3 ^ 2) + Z4 ^ 2) := by
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 (((-2 : ℝ) • Y1 + Y2) + Y3) Y4).trans
      (mul_le_mul_of_nonneg_left (add_le_add h123 hY4) (by norm_num))
  have hfin : covariantJetNormSq (I := I) (M := M) g 2 (((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) + Y5) ≤
      2 * (2 * (2 * (2 * ((2 * Z1) ^ 2 + Z2 ^ 2) + Z3 ^ 2) + Z4 ^ 2) + Z5 ^ 2) := by
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 ((((-2 : ℝ) • Y1 + Y2) + Y3) + Y4) Y5).trans
      (mul_le_mul_of_nonneg_left (add_le_add h1234 hY5) (by norm_num))
  have h2g : (0 : ℝ) ≤ 2 * Z1 := mul_nonneg (by norm_num) hZ1
  have hsq : (2 * Z1) ^ 2 + Z2 ^ 2 + Z3 ^ 2 + Z4 ^ 2 + Z5 ^ 2 ≤
      (2 * Z1 + Z2 + Z3 + Z4 + Z5) ^ 2 := by
    have e1 := sq_add_sq_le_sq_add_of_nonneg (a := 2 * Z1) (b := Z2) h2g hZ2
    have e2 := sq_add_sq_le_sq_add_of_nonneg (a := 2 * Z1 + Z2) (b := Z3) (add_nonneg h2g hZ2) hZ3
    have e3 := sq_add_sq_le_sq_add_of_nonneg (a := 2 * Z1 + Z2 + Z3) (b := Z4)
      (add_nonneg (add_nonneg h2g hZ2) hZ3) hZ4
    have e4 := sq_add_sq_le_sq_add_of_nonneg (a := 2 * Z1 + Z2 + Z3 + Z4) (b := Z5)
      (add_nonneg (add_nonneg (add_nonneg h2g hZ2) hZ3) hZ4) hZ5
    linarith only [e1, e2, e3, e4]
  have hexp : 2 * (2 * (2 * (2 * ((2 * Z1) ^ 2 + Z2 ^ 2) + Z3 ^ 2) + Z4 ^ 2) + Z5 ^ 2) ≤
      16 * ((2 * Z1) ^ 2 + Z2 ^ 2 + Z3 ^ 2 + Z4 ^ 2 + Z5 ^ 2) := by
    linarith only [sq_nonneg Z3, sq_nonneg Z4, sq_nonneg Z5]
  exact hfin.trans (hexp.trans ((mul_le_mul_of_nonneg_left hsq (by norm_num)).trans_eq (by ring)))

theorem exists_pathIntegrand_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g T hδT hδZ s -
            RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g U hδU hδZ s) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨ρg, G0, G1, hρg, hG0, hG1, hgood⟩ :=
    RicciDeTurckLowOrder.exists_symmetricRicciTerm_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρl, L0, L1, hρl, hL0, hL1, hlie⟩ :=
    exists_deTurckLieCovariantDerivativeRemainder_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρv, V0, V1, hρv, hV0, hV1, hvb⟩ :=
    exists_lieCorrectionZeroVectorBundle_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, W0, W1, hρa, hW0, hW1, hamix⟩ :=
    RicciDeTurckLowOrder.exists_lieCorrectionZeroMixedConnection_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρr, C0, C1, hρr, hC0, hC1, hriem⟩ :=
    RicciDeTurckLowOrder.exists_lieCorrectionZeroRiemann_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  set ρ : ℝ := min (min ρg ρl) (min ρv (min ρa ρr)) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρg hρl) (lt_min hρv (lt_min hρa hρr))
  let MB0 : ℝ → ℝ := fun R => 8 * G0 R + 4 * (L0 R + V0 R + W0 R + C0 R)
  let MB1 : ℝ → ℝ := fun R => 8 * G1 R + 4 * (L1 R + V1 R + W1 R + C1 R)
  refine ⟨ρ, MB0, MB1, hρ0, ?_, ?_, ?_⟩
  · intro R hR
    have e1 := hG0 R hR
    have e2 := hL0 R hR
    have e3 := hV0 R hR
    have e4 := hW0 R hR
    have e5 := hC0 R hR
    simp only [MB0]
    exact add_nonneg (mul_nonneg (by norm_num) e1)
      (mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg e2 e3) e4) e5))
  · intro R hR
    have e1 := hG1 R hR
    have e2 := hL1 R hR
    have e3 := hV1 R hR
    have e4 := hW1 R hR
    have e5 := hC1 R hR
    simp only [MB1]
    exact add_nonneg (mul_nonneg (by norm_num) e1)
      (mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg e2 e3) e4) e5))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hρc : ρ ≤ ρg ∧ ρ ≤ ρl ∧ ρ ≤ ρv ∧ ρ ≤ ρa ∧ ρ ≤ ρr := by
    rw [hρdef]
    exact ⟨
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hXg := hgood T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.1) (hUn.trans hρc.1) hTUn hs
  have hXl := hlie T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.1) (hUn.trans hρc.2.1) hTUn hs
  have hXv := hvb T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.1) (hUn.trans hρc.2.2.1) hTUn hs
  have hXa := hamix T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.2.1) (hUn.trans hρc.2.2.2.1) hTUn hs
  have hXr := hriem T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans hρc.2.2.2.2) (hUn.trans hρc.2.2.2.2) hTUn hs
  rw [deTurckSmoothRemainder_self_low_order_sub_decomposition (I := I) (M := M) g T U hT hU
    hδ_lt hδT hδU hδZ hs]
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set Y1 : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT (s • T) -
      RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU (s • U)
    with hY1
  set Y2 : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmT g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
          lieDecompositionQ lieDecompositionEps s) -
      (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmU g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
          lieDecompositionQ lieDecompositionEps s) with hY2
  set Y3 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT -
      lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU with hY3
  set Y4 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroMixedConnection (I := I) (M := M) g gmT g -
      lieCorrectionZeroMixedConnection (I := I) (M := M) g gmU g with hY4
  set Y5 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
      lieCorrectionZeroRiemann (I := I) (M := M) g gmU with hY5
  set Zg : ℝ := G0 R * (1 + A) * (D4 + D3 + D2 + N) +
    G1 R * A4 * (D3 + N) with hZg
  set Zl : ℝ := L0 R * (1 + A) * (D4 + D3 + D2 + N) +
    L1 R * A4 * (D3 + N) with hZl
  set Zv : ℝ := V0 R * (1 + A) * (D4 + D3 + D2 + N) +
    V1 R * A4 * (D3 + N) with hZv
  set Za : ℝ := W0 R * (1 + A) * (D4 + D3 + D2 + N) +
    W1 R * A4 * (D3 + N) with hZa
  set Zr : ℝ := C0 R * (1 + A) * (D4 + D3 + D2 + N) +
    C1 R * A4 * (D3 + N) with hZr
  have hA1 : 0 ≤ (1 : ℝ) + A := add_nonneg zero_le_one hA
  have hbase : 0 ≤ D4 + D3 + D2 + N :=
    add_nonneg (add_nonneg (add_nonneg hD4 hD3) hD2) hN
  have htail : 0 ≤ D3 + N := add_nonneg hD3 hN
  have hZnonneg : ∀ b0 b1 : ℝ, 0 ≤ b0 → 0 ≤ b1 →
      0 ≤ b0 * (1 + A) * (D4 + D3 + D2 + N) + b1 * A4 * (D3 + N) := by
    intro b0 b1 hb0 hb1
    exact add_nonneg (mul_nonneg (mul_nonneg hb0 hA1) hbase)
      (mul_nonneg (mul_nonneg hb1 hA4) htail)
  have hZgn : 0 ≤ Zg := by
    rw [hZg]
    exact hZnonneg (G0 R) (G1 R) (hG0 R hR) (hG1 R hR)
  have hZln : 0 ≤ Zl := by
    rw [hZl]
    exact hZnonneg (L0 R) (L1 R) (hL0 R hR) (hL1 R hR)
  have hZvn : 0 ≤ Zv := by
    rw [hZv]
    exact hZnonneg (V0 R) (V1 R) (hV0 R hR) (hV1 R hR)
  have hZan : 0 ≤ Za := by
    rw [hZa]
    exact hZnonneg (W0 R) (W1 R) (hW0 R hR) (hW1 R hR)
  have hZrn : 0 ≤ Zr := by
    rw [hZr]
    exact hZnonneg (C0 R) (C1 R) (hC0 R hR) (hC1 R hR)
  refine (covariantJetNormSq_weighted_five_term_sum_le (I := I) (M := M) g Y1 Y2 Y3 Y4 Y5 Zg Zl Zv Za Zr
    hZgn hZln hZvn hZan hZrn hXg hXl hXv hXa hXr).trans (le_of_eq ?_)
  simp only [MB0, MB1]
  rw [hZg, hZl, hZv, hZa, hZr]
  apply congrArg (fun x : ℝ => x ^ 2)
  ring

theorem exists_ricciDeTurckLowOrderDifference_covariantJetNormSq_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hker⟩ :=
    exists_pathIntegrand_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    hTn hUn hTUn
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδT hδZ s -
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g U hδU hδZ s
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint :=
    covariantJetJoint_sub (I := I) (M := M) g _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  set Btot : ℝ := B0 R * (1 + A) * (D4 + D3 + D2 + N) +
    B1 R * A4 * (D3 + N) with hBtot
  have hBn : 0 ≤ Btot := by
    have h0 := hB0 R hR
    have h1 := hB1 R hR
    have e1 : 0 ≤ B0 R * (1 + A) * (D4 + D3 + D2 + N) := by
      have hs1 : 0 ≤ D4 + D3 + D2 + N := by linarith
      have hA1 : 0 ≤ (1 : ℝ) + A := by linarith
      exact mul_nonneg (mul_nonneg h0 hA1) hs1
    have e2 : 0 ≤ B1 R * A4 * (D3 + N) := by
      have hs2 : 0 ≤ D3 + N := by linarith
      exact mul_nonneg (mul_nonneg h1 hA4) hs2
    rw [hBtot]
    linarith
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (Φ s) ≤ Btot ^ 2 := by
    intro s hs
    rw [hBtot]
    exact hker T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
      hTn hUn hTUn hs
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 2 Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (B := Btot)
    (by
      intro t ht
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hpoint t ht)
  have hfin : covariantJetNormSq (I := I) (M := M) g 2
      (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U hδ_lt hδT hδU hδZ) ≤
      Btot ^ 2 := by
    simpa only [covariantJetNormSq, ricciDeTurckLowOrderDifference, Φ, S, Nat.reduceAdd] using hpath
  exact hfin

private theorem exists_pathIntegrand_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g T hδT hδZ s -
            RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
              g g U hδU hδZ s) ≤
        (B R * (1 + A ^ 2) * (D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρg, G, hρg, hG, hgood⟩ :=
    RicciDeTurckLowOrder.exists_symmetricRicciTerm_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρl, L, hρl, hL, hlie⟩ :=
    RicciDeTurckLowOrder.exists_deTurckLieCovariantDerivative_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρv, V, hρv, hV, hvb⟩ :=
    RicciDeTurckLowOrder.exists_lieCorrectionZeroVectorBundle_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, W, hρa, hW, hamix⟩ :=
    RicciDeTurckLowOrder.exists_lieCorrectionZeroMixedConnection_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨ρr, C, hρr, hC, hriem⟩ :=
    RicciDeTurckLowOrder.exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min (min ρg ρl) (min ρv (min ρa ρr))
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρg hρl) (lt_min hρv (lt_min hρa hρr))
  let B : ℝ → ℝ := fun R =>
    4 * (2 * G R + 2 * L R + 2 * V R + 2 * W R + C)
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    have hGn := hG R hR
    have hLn := hL R hR
    have hVn := hV R hR
    have hWn := hW R hR
    simp only [B]
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (by norm_num) hGn)
              (mul_nonneg (by norm_num) hLn))
            (mul_nonneg (by norm_num) hVn))
          (mul_nonneg (by norm_num) hWn)) hC)
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
    hTU2 hTU3 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hρc : ρ ≤ ρg ∧ ρ ≤ ρl ∧ ρ ≤ ρv ∧ ρ ≤ ρa ∧ ρ ≤ ρr := by
    simp only [ρ]
    exact ⟨
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hXg := hgood T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3 hTU2 hTU3
    (hTn.trans hρc.1) (hUn.trans hρc.1) hTUn hs
  have hXl0 := hlie T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    (hTn.trans hρc.2.1) (hUn.trans hρc.2.1) hTUn hs
  have hXv0 := hvb T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    (hTn.trans hρc.2.2.1) (hUn.trans hρc.2.2.1) hTUn hs
  have hXa0 := hamix T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D3 N hR hA hD3 hN hT2 hU2 hT3 hU3 hTU3
    (hTn.trans hρc.2.2.2.1) (hUn.trans hρc.2.2.2.1) hTUn hs
  have hXr0 := hriem T U hT hU hδ_le hδ0 hδT hδU hδZ
    D2 D3 N hD2 hD3 hN
    (hTn.trans hρc.2.2.2.2) (hUn.trans hρc.2.2.2.2) hTUn hs
  let S : ℝ := D3 + D2 + N
  let F : ℝ := (1 + A ^ 2) * S
  let Zg : ℝ := G R * F
  let Zl : ℝ := 2 * L R * F
  let Zv : ℝ := 2 * V R * F
  let Za : ℝ := 2 * W R * F
  let Zr : ℝ := C * F
  have hS : 0 ≤ S := by
    simp only [S]
    exact add_nonneg (add_nonneg hD3 hD2) hN
  have hF : 0 ≤ F :=
    mul_nonneg (add_nonneg (by norm_num) (sq_nonneg A)) hS
  have hZgn : 0 ≤ Zg := mul_nonneg (hG R hR) hF
  have hZln : 0 ≤ Zl := mul_nonneg (mul_nonneg (by norm_num) (hL R hR)) hF
  have hZvn : 0 ≤ Zv := mul_nonneg (mul_nonneg (by norm_num) (hV R hR)) hF
  have hZan : 0 ≤ Za := mul_nonneg (mul_nonneg (by norm_num) (hW R hR)) hF
  have hZrn : 0 ≤ Zr := mul_nonneg hC hF
  have hfac : (1 + A) ^ 2 ≤ 2 * (1 + A ^ 2) := by
    nlinarith only [sq_nonneg (A - 1)]
  have hpart : D3 + N ≤ S := by
    simp only [S]
    calc
      D3 + N ≤ D3 + (D2 + N) :=
        add_le_add (le_refl D3) (le_add_of_nonneg_left hD2)
      _ = D3 + D2 + N := by ring
  have hfull : S ≤ F := by
    simp only [F]
    calc
      S = 1 * S := (one_mul S).symm
      _ ≤ (1 + A ^ 2) * S :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (sq_nonneg A)) hS
  have hinflate : ∀ K : ℝ, 0 ≤ K →
      K * (1 + A) ^ 2 * (D3 + N) ≤ 2 * K * F := by
    intro K hK
    calc
      K * (1 + A) ^ 2 * (D3 + N) ≤
          K * (2 * (1 + A ^ 2)) * (D3 + N) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac hK) (add_nonneg hD3 hN)
      _ ≤ K * (2 * (1 + A ^ 2)) * S :=
        mul_le_mul_of_nonneg_left hpart
          (mul_nonneg hK (mul_nonneg (by norm_num)
            (add_nonneg (by norm_num) (sq_nonneg A))))
      _ = 2 * K * F := by simp only [F]; ring
  have hXl : covariantJetNormSq (I := I) (M := M) g 2
      ((deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
            lieDecompositionQ lieDecompositionEps s) -
        (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
            lieDecompositionQ lieDecompositionEps s)) ≤ Zl ^ 2 := by
    refine hXl0.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hL R hR)
        (sq_nonneg (1 + A))) (add_nonneg hD3 hN)) ?_ 2)
    simpa only [Zl] using hinflate (L R) (hL R hR)
  have hXv : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundle (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
        lieCorrectionZeroVectorBundle (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤ Zv ^ 2 := by
    refine hXv0.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hV R hR)
        (sq_nonneg (1 + A))) (add_nonneg hD3 hN)) ?_ 2)
    simpa only [Zv] using hinflate (V R) (hV R hR)
  have hXa : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroMixedConnection (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g) ≤ Za ^ 2 := by
    refine hXa0.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hW R hR)
        (sq_nonneg (1 + A))) (add_nonneg hD3 hN)) ?_ 2)
    simpa only [Za] using hinflate (W R) (hW R hR)
  have hXr : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
        lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤ Zr ^ 2 := by
    refine hXr0.trans (pow_le_pow_left₀
      (mul_nonneg hC hS) ?_ 2)
    simp only [Zr]
    exact mul_le_mul_of_nonneg_left hfull hC
  rw [deTurckSmoothRemainder_self_low_order_sub_decomposition (I := I) (M := M) g T U hT hU
    hδ_lt hδT hδU hδZ hs]
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT_def
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU_def
  set Y1 : SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT (s • T) -
      RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU (s • U) with hY1_def
  set Y2 : SmoothCcTensor g 2 2 :=
    (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmT g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
          lieDecompositionQ lieDecompositionEps s) -
      (deTurckLieCovariantDerivativeTermField (I := I) (M := M) g gmU g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
          lieDecompositionQ lieDecompositionEps s) with hY2_def
  set Y3 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU with hY3_def
  set Y4 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroMixedConnection (I := I) (M := M) g gmT g - lieCorrectionZeroMixedConnection (I := I) (M := M) g gmU g with hY4_def
  set Y5 : SmoothCcTensor g 2 2 :=
    lieCorrectionZeroRiemann (I := I) (M := M) g gmT - lieCorrectionZeroRiemann (I := I) (M := M) g gmU with hY5_def
  have hY1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Zg ^ 2 := by
    have hY1raw : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤
        (G R * (1 + A ^ 2) * S) ^ 2 := by
      simpa only [Y1, gmT, gmU, S] using hXg
    refine hY1raw.trans (le_of_eq ?_)
    simp only [Zg, F]
    ring
  have hY2 : covariantJetNormSq (I := I) (M := M) g 2 Y2 ≤ Zl ^ 2 := by
    simpa only [Y2, gmT, gmU] using hXl
  have hY3 : covariantJetNormSq (I := I) (M := M) g 2 Y3 ≤ Zv ^ 2 := by
    simpa only [Y3, gmT, gmU] using hXv
  have hY4 : covariantJetNormSq (I := I) (M := M) g 2 Y4 ≤ Za ^ 2 := by
    simpa only [Y4, gmT, gmU] using hXa
  have hY5 : covariantJetNormSq (I := I) (M := M) g 2 Y5 ≤ Zr ^ 2 := by
    simpa only [Y5, gmT, gmU] using hXr
  refine (covariantJetNormSq_weighted_five_term_sum_le (I := I) (M := M) g
    Y1 Y2 Y3 Y4 Y5 Zg Zl Zv Za Zr hZgn hZln hZvn hZan hZrn
    hY1 hY2 hY3 hY4 hY5).trans (le_of_eq ?_)
  simp only [B, Zg, Zl, Zv, Za, Zr, F, S]
  apply congrArg (fun x : ℝ => x ^ 2)
  ring

theorem exists_ricciDeTurckLowOrderDifference_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        (B R * (1 + A ^ 2) * (D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hker⟩ :=
    exists_pathIntegrand_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
    hTU2 hTU3 hTn hUn hTUn
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g T hδT hδZ s -
      RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
        g g U hδU hδZ s
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint :=
    covariantJetJoint_sub (I := I) (M := M) g _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  let Btot : ℝ := B R * (1 + A ^ 2) * (D3 + D2 + N)
  have hBn : 0 ≤ Btot :=
    mul_nonneg
      (mul_nonneg (hB R hR) (add_nonneg (by norm_num) (sq_nonneg A)))
      (by linarith)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (Φ s) ≤ Btot ^ 2 := by
    intro s hs
    simpa only [Btot, Φ] using
      hker T U hT hU hδ_le hδ0 hδT hδU hδZ
        R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
        hTU2 hTU3 hTn hUn hTUn hs
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 2 Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (B := Btot)
    (by
      intro t ht
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hpoint t ht)
  simpa only [covariantJetNormSq, ricciDeTurckLowOrderDifference, Φ, S, Btot, Nat.reduceAdd] using hpath

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
