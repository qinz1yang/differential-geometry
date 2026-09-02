import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MetricDifference
import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Interpolation

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (sq_add_sq_le_sq_add_of_nonneg)
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccInputSlotSymm
  ccInputSlotSymm_sub ccSlotSwapField ccTensorToHs ccTensorToHs_smul covGrad_sub metricComparisonEndomorphismField permCoeff
  pureTrace pureTrace_toSection ricciConnectionDifferenceQuadraticArm ricciConnectionDifferenceQuadraticKernel rsDomDomCongr slotExtend slotExtendIter slotExtend_sub)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_connectionDifferenceSection_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => C0 0 + C1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg (hC0 0 (by norm_num))
      (mul_nonneg (hC1 0 (by norm_num)) hR)
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hzeroSymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have h02 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, covariantJetNormSq_smul]
    norm_num
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g -
            connectionDifferenceSection (I := I) g g) ≤
        (C0 0 * A + C1 0 * R + C1 0 * A * R) ^ 2 :=
    hpair gm g T (0 : SmoothCcTensor g 0 2) hT hzeroSymm
      htie hzeroTie hδ_le hδ0 hδT hδ_le hδ0 hδZ
      0 A R A (by norm_num) hA hR hA h02 hT3
      (by simpa only [sub_zero] using hT2)
      (by simpa only [sub_zero] using hT3)
  rw [connectionDifferenceSection_self (I := I) (M := M) g, sub_zero] at hraw
  have hc0 : 0 ≤ C0 0 := hC0 0 (by norm_num)
  have hc1 : 0 ≤ C1 0 := hC1 0 (by norm_num)
  have hold : 0 ≤ C0 0 * A + C1 0 * R + C1 0 * A * R :=
    add_nonneg (add_nonneg (mul_nonneg hc0 hA) (mul_nonneg hc1 hR))
      (mul_nonneg (mul_nonneg hc1 hA) hR)
  have hlin :
      C0 0 * A + C1 0 * R + C1 0 * A * R ≤
        B R * (1 + A) := by
    dsimp only [B]
    nlinarith only [mul_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1),
      mul_nonneg hc1 hR]
  exact hraw.trans (pow_le_pow_left₀ hold hlin 2)

private theorem exists_connectionDifferenceSection_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B : ℝ → ℝ := fun R => C0 R + C1 R
  refine ⟨B, fun R hR => add_nonneg (hC0 R hR) (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hraw := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hc0 := hC0 R hR
  have hc1 := hC1 R hR
  have hold : 0 ≤ C0 R * D3 + C1 R * D2 + C1 R * A * D2 :=
    add_nonneg (add_nonneg (mul_nonneg hc0 hD3) (mul_nonneg hc1 hD2))
      (mul_nonneg (mul_nonneg hc1 hA) hD2)
  have hlin :
      C0 R * D3 + C1 R * D2 + C1 R * A * D2 ≤
        B R * (D3 + D2 + A * D2) := by
    dsimp only [B]
    nlinarith only [mul_nonneg hc0 hD2,
      mul_nonneg hc0 (mul_nonneg hA hD2),
      mul_nonneg hc1 hD3]
  exact hraw.trans (pow_le_pow_left₀ hold hlin 2)

private theorem exists_connectionDifferenceContrInsertionInnerField_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceSection_covariantJetNormSq_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gm g)) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _
    _ = 3 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by rw [hDim]; norm_num
    _ ≤ 3 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (B R * (1 + A)) ^ 2 := by
      simp only [B]
      nlinarith only [sq_nonneg (C R * (1 + A))]

private theorem exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceSection_covariantJetNormSq_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g))) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) gm g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (Nat.cast_nonneg _)
    _ = 9 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by
      rw [hDim]
      ring
    _ ≤ 9 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (B R * (1 + A)) ^ 2 := by simp only [B]; ring

private theorem exists_connectionDifferenceContrInsertionInnerField_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ :=
    exists_connectionDifferenceSection_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hs := hsec gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gT,
    connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gU,
    ← reindexCoeffGen_sub (I := I) (M := M) g,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g,
    ← slotExtend_sub]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g)) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _
    _ = 3 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by rw [hDim]; norm_num
    _ ≤ 3 * (C R * (D3 + D2 + A * D2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (B R * (D3 + D2 + A * D2)) ^ 2 := by
      simp only [B]
      nlinarith only [sq_nonneg (C R * (D3 + D2 + A * D2))]

private theorem exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ :=
    exists_connectionDifferenceSection_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hs := hsec gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gT,
    connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gU,
    ← reindexCoeffGen_sub (I := I) (M := M) g,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g,
    ← slotExtend_sub, ← slotExtend_sub]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g))) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (Nat.cast_nonneg _)
    _ = 9 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) := by
      rw [hDim]
      ring
    _ ≤ 9 * (C R * (D3 + D2 + A * D2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
      simp only [B]
      ring

private def ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_swapBlocks : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_cycleZeroThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_cycleZeroOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_swapZeroTwo : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_swapZeroOne : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ricciQuadraticConnectionPermutation_rotateInputs : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def ricciQuadraticConnectionInner
    (g gm : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 3)) :
    SmoothCcTensor g 2 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 3 3
    (permCoeff (I := I) (M := M) g ρ)
    (connectionDifferenceContrInsertionInnerField (I := I) g gm)

private noncomputable def ricciQuadraticConnectionBlock
    (g gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (Z : SmoothCcTensor g 2 3) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
    (permCoeff (I := I) (M := M) g pm)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)

private noncomputable def ricciQuadraticConnectionBlockSum
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo
          (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroOne) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapBlocks
            (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroOne))
          innerCoreInPerm10 +
        ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroThreeTwo
          (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_rotateInputs) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
            (connectionDifferenceContrInsertionInnerField (I := I) g gm))
          innerCoreInPerm10 +
        ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroOneTwo
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroTwo
            (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_rotateInputs))
          innerCoreInPerm10

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciQuadraticConnectionKernel_eq_block_sum (g gm : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm =
      ricciQuadraticConnectionBlockSum (I := I) (M := M) g gm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply DifferentialGeometry.Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  unfold ricciConnectionDifferenceQuadraticKernel ricciQuadraticConnectionBlockSum
  rfl

private noncomputable def ricciQuadraticConnectionJetCap
    (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapBlocks) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroOne) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_rotateInputs)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciQuadraticConnectionJetCap_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ ricciQuadraticConnectionJetCap (I := I) (M := M) g := by
  unfold ricciQuadraticConnectionJetCap
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_rotateInputs)
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_permCoeff_four_le_ricciQuadraticConnectionJetCap
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (hpm : pm = ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapBlocks ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroThreeTwo ∨
      pm = ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapZeroTwo) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      ricciQuadraticConnectionJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_rotateInputs)
  unfold ricciQuadraticConnectionJetCap
  rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_permCoeff_three_le_ricciQuadraticConnectionJetCap
    (g : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 3))
    (hρ : ρ = ricciQuadraticConnectionPermutation_swapZeroOne ∨ ρ = ricciQuadraticConnectionPermutation_rotateInputs) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g ρ) ≤
      ricciQuadraticConnectionJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_cycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_swapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticConnectionPermutation_rotateInputs)
  unfold ricciQuadraticConnectionJetCap
  rcases hρ with rfl | rfl <;> linarith

private theorem exists_ricciQuadraticConnectionBlock_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (Z : SmoothCcTensor g 2 3),
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciQuadraticConnectionBlock (I := I) (M := M) g gm pm Z) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gm) *
              covariantJetNormSq (I := I) (M := M) g 2 Z)) := by
  obtain ⟨C₄, hC₄, h₄⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C₃, hC₃, h₃⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 4
  refine ⟨C₄ * C₃, mul_nonneg hC₄ hC₃, ?_⟩
  intro gm pm Z
  change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
          (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)) ≤ _
  refine (h₄ _ _).trans ?_
  have hz := h₃ (connectionDifferenceContravariantInsertionField (I := I) g gm) Z
  exact (mul_le_mul_of_nonneg_left hz
    (mul_nonneg hC₄
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (permCoeff (I := I) (M := M) g pm)))).trans_eq (by ring)

private theorem exists_ricciQuadraticConnectionBlock_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (ZT ZU : SmoothCcTensor g 2 3),
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciQuadraticConnectionBlock (I := I) (M := M) g gT pm ZT -
              ricciQuadraticConnectionBlock (I := I) (M := M) g gU pm ZU) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gT -
                  connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 2 ZT +
              covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU))) := by
  obtain ⟨C₄, hC₄, h₄⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C₃, hC₃, h₃⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 4
  refine ⟨2 * C₄ * C₃, by positivity, ?_⟩
  intro gT gU pm ZT ZU
  let OT := connectionDifferenceContravariantInsertionField (I := I) g gT
  let OU := connectionDifferenceContravariantInsertionField (I := I) g gU
  let X := ccOperatorFieldComp (I := I) (M := M) g 2 3 4 (OT - OU) ZT
  let Y := ccOperatorFieldComp (I := I) (M := M) g 2 3 4 OU (ZT - ZU)
  have hinner :
      ccOperatorFieldComp (I := I) (M := M) g 2 3 4 OT ZT -
          ccOperatorFieldComp (I := I) (M := M) g 2 3 4 OU ZU =
        X + Y := by
    simp only [X, Y, OT, OU, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hsub :
      ricciQuadraticConnectionBlock (I := I) (M := M) g gT pm ZT -
          ricciQuadraticConnectionBlock (I := I) (M := M) g gU pm ZU =
        ccOperatorFieldComp (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g pm) (X + Y) := by
    change
      ccOperatorFieldComp (I := I) (M := M) g 2 4 4
            (permCoeff (I := I) (M := M) g pm)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 4 OT ZT) -
          ccOperatorFieldComp (I := I) (M := M) g 2 4 4
            (permCoeff (I := I) (M := M) g pm)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 4 OU ZU) =
        _
    rw [← operatorFieldComposition_sub_right, hinner]
  have hx :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
        C₃ * (covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) *
          covariantJetNormSq (I := I) (M := M) g 2 ZT) := by
    simpa only [X, mul_assoc] using h₃ (OT - OU) ZT
  have hy :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        C₃ * (covariantJetNormSq (I := I) (M := M) g 2 OU *
          covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU)) := by
    simpa only [Y, mul_assoc] using h₃ OU (ZT - ZU)
  have hxy :
      covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * C₃ *
          (covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) *
              covariantJetNormSq (I := I) (M := M) g 2 ZT +
            covariantJetNormSq (I := I) (M := M) g 2 OU *
              covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU)) := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
    linarith
  rw [hsub]
  refine (h₄ _ _).trans ?_
  have hp0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g pm)
  exact (mul_le_mul_of_nonneg_left hxy (mul_nonneg hC₄ hp0)).trans_eq
    (by simp only [OT, OU]; ring)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_ricciQuadraticConnectionKernel_sum_le
    (g : SmoothRiemannianMetric I M)
    (Y0 Y1 Y2 Y3 Y4 Y5 : SmoothCcTensor g 2 4)
    (Q : ℝ)
    (h0 : covariantJetNormSq (I := I) (M := M) g 2 Y0 ≤ Q)
    (h1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Q)
    (h2 : covariantJetNormSq (I := I) (M := M) g 2 Y2 ≤ Q)
    (h3 : covariantJetNormSq (I := I) (M := M) g 2 Y3 ≤ Q)
    (h4 : covariantJetNormSq (I := I) (M := M) g 2 Y4 ≤ Q)
    (h5 : covariantJetNormSq (I := I) (M := M) g 2 Y5 ≤ Q) :
    covariantJetNormSq (I := I) (M := M) g 2
        (Y0 + Y1 + Y2 + Y3 + Y4 + Y5) ≤ 94 * Q := by
  have h01 :
      covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤ 4 * Q :=
    (covariantJetNormSq_add_le (I := I) (M := M) g 2 Y0 Y1).trans (by linarith)
  have h012 :
      covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1 + Y2) ≤ 10 * Q :=
    (covariantJetNormSq_add_le (I := I) (M := M) g 2 (Y0 + Y1) Y2).trans
      (by linarith)
  have h0123 :
      covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1 + Y2 + Y3) ≤ 22 * Q :=
    (covariantJetNormSq_add_le (I := I) (M := M) g 2 (Y0 + Y1 + Y2) Y3).trans
      (by linarith)
  have h01234 :
      covariantJetNormSq (I := I) (M := M) g 2
          (Y0 + Y1 + Y2 + Y3 + Y4) ≤ 46 * Q :=
    (covariantJetNormSq_add_le (I := I) (M := M) g 2 (Y0 + Y1 + Y2 + Y3) Y4).trans
      (by linarith)
  exact
    (covariantJetNormSq_add_le (I := I) (M := M) g 2
      (Y0 + Y1 + Y2 + Y3 + Y4) Y5).trans (by linarith)

private theorem exists_ricciQuadraticConnectionKernel_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm) ≤
        (B R * (1 + A) ^ 2) ^ 2 := by
  obtain ⟨Cb, hCb, hblk⟩ :=
    exists_ricciQuadraticConnectionBlock_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hinnApp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bo, hBo, hout⟩ :=
    exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bi, hBi, hinn⟩ :=
    exists_connectionDifferenceContrInsertionInnerField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  let P : ℝ := ricciQuadraticConnectionJetCap (I := I) (M := M) g
  let KZ : ℝ → ℝ := fun R => (1 + Ci * P) * Bi R ^ 2
  let L : ℝ → ℝ := fun R => 94 * Cb * P * (Bo R ^ 2 * KZ R)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hP : 0 ≤ P := ricciQuadraticConnectionJetCap_nonneg (I := I) (M := M) g
  have hKZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ KZ R := by
    intro R hR
    exact mul_nonneg
      (add_nonneg (by norm_num) (mul_nonneg hCi hP))
      (sq_nonneg (Bi R))
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCb) hP)
      (mul_nonneg (sq_nonneg (Bo R)) (hKZ R hR))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let S : ℝ := (1 + A) ^ 2
  let Q : ℝ := Cb * (P * ((Bo R ^ 2 * S) * (KZ R * S)))
  have hS : 0 ≤ S := sq_nonneg _
  have hO :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        Bo R ^ 2 * S := by
    calc
      _ ≤ (Bo R * (1 + A)) ^ 2 :=
        hout gm T hT htie hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3
      _ = Bo R ^ 2 * S := by simp only [S]; ring
  have hI :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
        Bi R ^ 2 * S := by
    calc
      _ ≤ (Bi R * (1 + A)) ^ 2 :=
        hinn gm T hT htie hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3
      _ = Bi R ^ 2 * S := by simp only [S]; ring
  have hZdir :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
        KZ R * S := by
    refine hI.trans ?_
    simp only [KZ]
    have hcp : 0 ≤ Ci * P := mul_nonneg hCi hP
    have hz : 0 ≤ Bi R ^ 2 * S :=
      mul_nonneg (sq_nonneg _) hS
    nlinarith only [hcp, hz]
  have hZinn : ∀ ρ : Equiv.Perm (Fin 3),
      (ρ = ricciQuadraticConnectionPermutation_swapZeroOne ∨ ρ = ricciQuadraticConnectionPermutation_rotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticConnectionInner (I := I) (M := M) g gm ρ) ≤
        KZ R * S := by
    intro ρ hρ
    have hpρ := covariantJetNormSq_permCoeff_three_le_ricciQuadraticConnectionJetCap (I := I) (M := M) g ρ hρ
    have hraw := hinnApp
      (permCoeff (I := I) (M := M) g ρ)
      (connectionDifferenceContrInsertionInnerField (I := I) g gm)
    change covariantJetNormSq (I := I) (M := M) g 2
        (ricciQuadraticConnectionInner (I := I) (M := M) g gm ρ) ≤ _ at hraw ⊢
    refine hraw.trans ?_
    have hmul :
        Ci * covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g ρ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
          Ci * P * (Bi R ^ 2 * S) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpρ hCi) hI
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCi hP)
    refine hmul.trans ?_
    simp only [KZ]
    have hz : 0 ≤ Bi R ^ 2 * S :=
      mul_nonneg (sq_nonneg _) hS
    nlinarith only [mul_nonneg hCi hP, hz]
  have hQ : 0 ≤ Q := by
    exact mul_nonneg hCb
      (mul_nonneg hP
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) hS)
          (mul_nonneg (hKZ R hR) hS)))
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapBlocks ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroThreeTwo ∨
        pm = ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapZeroTwo) →
      ∀ Z : SmoothCcTensor g 2 3,
      covariantJetNormSq (I := I) (M := M) g 2 Z ≤ KZ R * S →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gm pm Z) ≤ Q := by
    intro pm hpm Z hZ
    have hp := covariantJetNormSq_permCoeff_four_le_ricciQuadraticConnectionJetCap (I := I) (M := M) g pm hpm
    refine (hblk gm pm Z).trans ?_
    have hprod :
        covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContravariantInsertionField (I := I) g gm) *
            covariantJetNormSq (I := I) (M := M) g 2 Z ≤
          (Bo R ^ 2 * S) * (KZ R * S) :=
      mul_le_mul hO hZ
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Z)
        (mul_nonneg (sq_nonneg _) hS)
    have hmid :
        covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gm) *
              covariantJetNormSq (I := I) (M := M) g 2 Z) ≤
          P * ((Bo R ^ 2 * S) * (KZ R * S)) :=
      mul_le_mul hp hprod
        (mul_nonneg
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Z))
        hP
    simpa only [Q] using mul_le_mul_of_nonneg_left hmid hCb
  have hx0 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo (Or.inl rfl) _
    (hZinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
  have hx1 := hblkQ ricciQuadraticConnectionPermutation_swapBlocks (Or.inr (Or.inl rfl)) _
    (hZinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
  have hx2 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _
    (hZinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
  have hx3 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hZdir
  have hx4 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroOneTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ hZdir
  have hx5 := hblkQ ricciQuadraticConnectionPermutation_swapZeroTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _
    (hZinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
  rw [ricciQuadraticConnectionKernel_eq_block_sum (I := I) (M := M) g gm]
  unfold ricciQuadraticConnectionBlockSum
  set Y0 := ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroOne)
  set Y1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapBlocks
      (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroOne))
    innerCoreInPerm10
  set Y2 := ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroThreeTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_rotateInputs)
  set Y3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
      (connectionDifferenceContrInsertionInnerField (I := I) g gm))
    innerCoreInPerm10
  set Y4 := ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroOneTwo
    (connectionDifferenceContrInsertionInnerField (I := I) g gm)
  set Y5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroTwo
      (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_rotateInputs))
    innerCoreInPerm10
  have hY1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Q := by
    rw [show Y1 = reindexCoeffGen (I := I) (M := M) g 2 4
      (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapBlocks
        (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroOne))
      innerCoreInPerm10 by rfl,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx1
  have hY3 : covariantJetNormSq (I := I) (M := M) g 2 Y3 ≤ Q := by
    rw [show Y3 = reindexCoeffGen (I := I) (M := M) g 2 4
      (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
        (connectionDifferenceContrInsertionInnerField (I := I) g gm))
      innerCoreInPerm10 by rfl,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx3
  have hY5 : covariantJetNormSq (I := I) (M := M) g 2 Y5 ≤ Q := by
    rw [show Y5 = reindexCoeffGen (I := I) (M := M) g 2 4
      (ricciQuadraticConnectionBlock (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_swapZeroTwo
        (ricciQuadraticConnectionInner (I := I) (M := M) g gm ricciQuadraticConnectionPermutation_rotateInputs))
      innerCoreInPerm10 by rfl,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx5
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 2
          (Y0 + Y1 + Y2 + Y3 + Y4 + Y5) ≤ 94 * Q :=
    covariantJetNormSq_ricciQuadraticConnectionKernel_sum_le (I := I) (M := M) g Y0 Y1 Y2 Y3 Y4 Y5
      Q hx0 hY1 hx2 hY3 hx4 hY5
  refine hsum.trans (le_of_eq ?_)
  have hBsq : B R ^ 2 = L R := by
    simpa only [B] using Real.sq_sqrt (hL R hR)
  simp only [Q, S]
  rw [mul_pow, hBsq]
  ring

private theorem exists_ricciQuadraticConnectionKernel_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Cb, hCb, hblk⟩ :=
    exists_ricciQuadraticConnectionBlock_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hinnApp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bo, hBo, houtB⟩ :=
    exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bi, hBi, hinnB⟩ :=
    exists_connectionDifferenceContrInsertionInnerField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bod, hBod, houtD⟩ :=
    exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bid, hBid, hinnD⟩ :=
    exists_connectionDifferenceContrInsertionInnerField_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let P : ℝ := ricciQuadraticConnectionJetCap (I := I) (M := M) g
  let KZ : ℝ → ℝ := fun R => (1 + Ci * P) * Bi R ^ 2
  let KD : ℝ → ℝ := fun R => (1 + Ci * P) * Bid R ^ 2
  let L : ℝ → ℝ := fun R =>
    94 * Cb * P * (Bod R ^ 2 * KZ R + Bo R ^ 2 * KD R)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hP : 0 ≤ P := ricciQuadraticConnectionJetCap_nonneg (I := I) (M := M) g
  have hfac : 0 ≤ 1 + Ci * P :=
    add_nonneg (by norm_num) (mul_nonneg hCi hP)
  have hKZ : ∀ R : ℝ, 0 ≤ KZ R :=
    fun R => mul_nonneg hfac (sq_nonneg _)
  have hKD : ∀ R : ℝ, 0 ≤ KD R :=
    fun R => mul_nonneg hfac (sq_nonneg _)
  have hL : ∀ R : ℝ, 0 ≤ L R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCb) hP)
      (add_nonneg
        (mul_nonneg (sq_nonneg _) (hKZ R))
        (mul_nonneg (sq_nonneg _) (hKD R)))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let S : ℝ := (1 + A) ^ 2
  let D : ℝ := (D3 + D2 + A * D2) ^ 2
  let Q : ℝ := Cb * (P *
    ((Bod R ^ 2 * D) * (KZ R * S) +
      (Bo R ^ 2 * S) * (KD R * D)))
  have hS : 0 ≤ S := sq_nonneg _
  have hD : 0 ≤ D := sq_nonneg _
  have hOTU :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ≤
        Bod R ^ 2 * D := by
    calc
      _ ≤ (Bod R * (D3 + D2 + A * D2)) ^ 2 :=
        houtD gT gU T U hT hU hTtie hUtie
          hδ_le hδ0 hδT hδ_le hδ0 hδU
          R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
      _ = Bod R ^ 2 * D := by simp only [D]; ring
  have hOU :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gU) ≤
        Bo R ^ 2 * S := by
    calc
      _ ≤ (Bo R * (1 + A)) ^ 2 :=
        houtB gU U hU hUtie hδ_le hδ0 hδU hδZ
          R A hR hA hU2 hU3
      _ = Bo R ^ 2 * S := by simp only [S]; ring
  have hIT :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
        Bi R ^ 2 * S := by
    calc
      _ ≤ (Bi R * (1 + A)) ^ 2 :=
        hinnB gT T hT hTtie hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3
      _ = Bi R ^ 2 * S := by simp only [S]; ring
  have hITU :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
        Bid R ^ 2 * D := by
    calc
      _ ≤ (Bid R * (D3 + D2 + A * D2)) ^ 2 :=
        hinnD gT gU T U hT hU hTtie hUtie
          hδ_le hδ0 hδT hδ_le hδ0 hδU
          R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
      _ = Bid R ^ 2 * D := by simp only [D]; ring
  have hZTdir :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
        KZ R * S := by
    refine hIT.trans ?_
    simp only [KZ]
    have hz : 0 ≤ Bi R ^ 2 * S :=
      mul_nonneg (sq_nonneg _) hS
    calc
      Bi R ^ 2 * S = 1 * (Bi R ^ 2 * S) := (one_mul _).symm
      _ ≤ (1 + Ci * P) * (Bi R ^ 2 * S) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg hCi hP)) hz
      _ = (1 + Ci * P) * Bi R ^ 2 * S := by ring
  have hZDdir :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gT -
            connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
        KD R * D := by
    refine hITU.trans ?_
    simp only [KD]
    have hz : 0 ≤ Bid R ^ 2 * D :=
      mul_nonneg (sq_nonneg _) hD
    calc
      Bid R ^ 2 * D = 1 * (Bid R ^ 2 * D) := (one_mul _).symm
      _ ≤ (1 + Ci * P) * (Bid R ^ 2 * D) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg hCi hP)) hz
      _ = (1 + Ci * P) * Bid R ^ 2 * D := by ring
  have hZTinn : ∀ ρ : Equiv.Perm (Fin 3),
      (ρ = ricciQuadraticConnectionPermutation_swapZeroOne ∨ ρ = ricciQuadraticConnectionPermutation_rotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticConnectionInner (I := I) (M := M) g gT ρ) ≤
        KZ R * S := by
    intro ρ hρ
    have hpρ := covariantJetNormSq_permCoeff_three_le_ricciQuadraticConnectionJetCap (I := I) (M := M) g ρ hρ
    have hraw := hinnApp
      (permCoeff (I := I) (M := M) g ρ)
      (connectionDifferenceContrInsertionInnerField (I := I) g gT)
    change covariantJetNormSq (I := I) (M := M) g 2
        (ricciQuadraticConnectionInner (I := I) (M := M) g gT ρ) ≤ _ at hraw ⊢
    refine hraw.trans ?_
    have hmul :
        Ci * covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g ρ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContrInsertionInnerField (I := I) g gT) ≤
          Ci * P * (Bi R ^ 2 * S) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpρ hCi) hIT
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCi hP)
    refine hmul.trans ?_
    simp only [KZ]
    have hz : 0 ≤ Bi R ^ 2 * S :=
      mul_nonneg (sq_nonneg _) hS
    calc
      Ci * P * (Bi R ^ 2 * S) ≤ (1 + Ci * P) * (Bi R ^ 2 * S) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hz
      _ = (1 + Ci * P) * Bi R ^ 2 * S := by ring
  have hZDinn : ∀ ρ : Equiv.Perm (Fin 3),
      (ρ = ricciQuadraticConnectionPermutation_swapZeroOne ∨ ρ = ricciQuadraticConnectionPermutation_rotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticConnectionInner (I := I) (M := M) g gT ρ -
            ricciQuadraticConnectionInner (I := I) (M := M) g gU ρ) ≤
        KD R * D := by
    intro ρ hρ
    have hpρ := covariantJetNormSq_permCoeff_three_le_ricciQuadraticConnectionJetCap (I := I) (M := M) g ρ hρ
    have heq :
        ricciQuadraticConnectionInner (I := I) (M := M) g gT ρ -
            ricciQuadraticConnectionInner (I := I) (M := M) g gU ρ =
          ccOperatorFieldComp (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ρ)
            (connectionDifferenceContrInsertionInnerField (I := I) g gT -
              connectionDifferenceContrInsertionInnerField (I := I) g gU) := by
      simp only [ricciQuadraticConnectionInner]
      rw [operatorFieldComposition_sub_right]
    rw [heq]
    refine (hinnApp _ _).trans ?_
    have hmul :
        Ci * covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g ρ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContrInsertionInnerField (I := I) g gT -
                connectionDifferenceContrInsertionInnerField (I := I) g gU) ≤
          Ci * P * (Bid R ^ 2 * D) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpρ hCi) hITU
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCi hP)
    refine hmul.trans ?_
    simp only [KD]
    have hz : 0 ≤ Bid R ^ 2 * D :=
      mul_nonneg (sq_nonneg _) hD
    calc
      Ci * P * (Bid R ^ 2 * D) ≤ (1 + Ci * P) * (Bid R ^ 2 * D) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left zero_le_one) hz
      _ = (1 + Ci * P) * Bid R ^ 2 * D := by ring
  have hQ : 0 ≤ Q := by
    exact mul_nonneg hCb
      (mul_nonneg hP
        (add_nonneg
          (mul_nonneg
            (mul_nonneg (sq_nonneg _) hD)
            (mul_nonneg (hKZ R) hS))
          (mul_nonneg
            (mul_nonneg (sq_nonneg _) hS)
            (mul_nonneg (hKD R) hD))))
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapBlocks ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroThreeTwo ∨
        pm = ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticConnectionPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticConnectionPermutation_swapZeroTwo) →
      ∀ ZT ZU : SmoothCcTensor g 2 3,
      covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ KZ R * S →
      covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤ KD R * D →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gT pm ZT -
            ricciQuadraticConnectionBlock (I := I) (M := M) g gU pm ZU) ≤ Q := by
    intro pm hpm ZT ZU hZT hZD
    have hp := covariantJetNormSq_permCoeff_four_le_ricciQuadraticConnectionJetCap (I := I) (M := M) g pm hpm
    refine (hblk gT gU pm ZT ZU).trans ?_
    have hprod1 :
        covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContravariantInsertionField (I := I) g gT -
                connectionDifferenceContravariantInsertionField (I := I) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2 ZT ≤
          (Bod R ^ 2 * D) * (KZ R * S) :=
      mul_le_mul hOTU hZT
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g ZT)
        (mul_nonneg (sq_nonneg _) hD)
    have hprod2 :
        covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceContravariantInsertionField (I := I) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤
          (Bo R ^ 2 * S) * (KD R * D) :=
      mul_le_mul hOU hZD
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (ZT - ZU))
        (mul_nonneg (sq_nonneg _) hS)
    have hsum :
        covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gT -
                  connectionDifferenceContravariantInsertionField (I := I) g gU) *
              covariantJetNormSq (I := I) (M := M) g 2 ZT +
            covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gU) *
              covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤
          (Bod R ^ 2 * D) * (KZ R * S) +
            (Bo R ^ 2 * S) * (KD R * D) :=
      add_le_add hprod1 hprod2
    have hmid :
        covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceContravariantInsertionField (I := I) g gT -
                  connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 2 ZT +
              covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceContravariantInsertionField (I := I) g gU) *
                covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU)) ≤
          P * ((Bod R ^ 2 * D) * (KZ R * S) +
            (Bo R ^ 2 * S) * (KD R * D)) :=
      mul_le_mul hp hsum
        (add_nonneg
          (mul_nonneg
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g ZT))
          (mul_nonneg
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
            (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (ZT - ZU))))
        hP
    simpa only [Q] using mul_le_mul_of_nonneg_left hmid hCb
  have hx0 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo (Or.inl rfl) _ _
    (hZTinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
    (hZDinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
  have hx1 := hblkQ ricciQuadraticConnectionPermutation_swapBlocks (Or.inr (Or.inl rfl)) _ _
    (hZTinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
    (hZDinn ricciQuadraticConnectionPermutation_swapZeroOne (Or.inl rfl))
  have hx2 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _ _
    (hZTinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
    (hZDinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
  have hx3 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ _
    hZTdir hZDdir
  have hx4 := hblkQ ricciQuadraticConnectionPermutation_cycleZeroOneTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ _
    hZTdir hZDdir
  have hx5 := hblkQ ricciQuadraticConnectionPermutation_swapZeroTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
    (hZTinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
    (hZDinn ricciQuadraticConnectionPermutation_rotateInputs (Or.inr rfl))
  rw [ricciQuadraticConnectionKernel_eq_block_sum (I := I) (M := M) g gT,
    ricciQuadraticConnectionKernel_eq_block_sum (I := I) (M := M) g gU]
  unfold ricciQuadraticConnectionBlockSum
  let Y0 := ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapZeroOne)
  let Y1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapBlocks
      (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapZeroOne))
    innerCoreInPerm10
  let Y2 := ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_cycleZeroThreeTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_rotateInputs)
  let Y3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
      (connectionDifferenceContrInsertionInnerField (I := I) g gT))
    innerCoreInPerm10
  let Y4 := ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_cycleZeroOneTwo
    (connectionDifferenceContrInsertionInnerField (I := I) g gT)
  let Y5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapZeroTwo
      (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_rotateInputs))
    innerCoreInPerm10
  let Z0 := ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_cycleZeroThreeOneTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapZeroOne)
  let Z1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapBlocks
      (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapZeroOne))
    innerCoreInPerm10
  let Z2 := ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_cycleZeroThreeTwo
    (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_rotateInputs)
  let Z3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
      (connectionDifferenceContrInsertionInnerField (I := I) g gU))
    innerCoreInPerm10
  let Z4 := ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_cycleZeroOneTwo
    (connectionDifferenceContrInsertionInnerField (I := I) g gU)
  let Z5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapZeroTwo
      (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_rotateInputs))
    innerCoreInPerm10
  change covariantJetNormSq (I := I) (M := M) g 2
      ((Y0 + Y1 + Y2 + Y3 + Y4 + Y5) -
        (Z0 + Z1 + Z2 + Z3 + Z4 + Z5)) ≤ _
  have hsplit :
      (Y0 + Y1 + Y2 + Y3 + Y4 + Y5) -
          (Z0 + Z1 + Z2 + Z3 + Z4 + Z5) =
        (Y0 - Z0) + (Y1 - Z1) + (Y2 - Z2) +
          (Y3 - Z3) + (Y4 - Z4) + (Y5 - Z5) := by
    module
  rw [hsplit]
  have hY1 : covariantJetNormSq (I := I) (M := M) g 2 (Y1 - Z1) ≤ Q := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapBlocks
            (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapZeroOne))
          innerCoreInPerm10 -
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapBlocks
            (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapZeroOne))
          innerCoreInPerm10) ≤ Q
    rw [← reindexCoeffGen_sub (I := I) (M := M) g,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx1
  have hY3 : covariantJetNormSq (I := I) (M := M) g 2 (Y3 - Z3) ≤ Q := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
            (connectionDifferenceContrInsertionInnerField (I := I) g gT))
          innerCoreInPerm10 -
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_cycleZeroOneThreeTwo
            (connectionDifferenceContrInsertionInnerField (I := I) g gU))
          innerCoreInPerm10) ≤ Q
    rw [← reindexCoeffGen_sub (I := I) (M := M) g,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx3
  have hY5 : covariantJetNormSq (I := I) (M := M) g 2 (Y5 - Z5) ≤ Q := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_swapZeroTwo
            (ricciQuadraticConnectionInner (I := I) (M := M) g gT ricciQuadraticConnectionPermutation_rotateInputs))
          innerCoreInPerm10 -
        reindexCoeffGen (I := I) (M := M) g 2 4
          (ricciQuadraticConnectionBlock (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_swapZeroTwo
            (ricciQuadraticConnectionInner (I := I) (M := M) g gU ricciQuadraticConnectionPermutation_rotateInputs))
          innerCoreInPerm10) ≤ Q
    rw [← reindexCoeffGen_sub (I := I) (M := M) g,
      covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
    exact hx5
  have hsum :=
    covariantJetNormSq_ricciQuadraticConnectionKernel_sum_le (I := I) (M := M) g
      (Y0 - Z0) (Y1 - Z1) (Y2 - Z2)
      (Y3 - Z3) (Y4 - Z4) (Y5 - Z5)
      Q hx0 hY1 hx2 hY3 hx4 hY5
  refine hsum.trans (le_of_eq ?_)
  have hBsq : B R ^ 2 = L R := by
    simpa only [B] using Real.sq_sqrt (hL R)
  simp only [Q, S, D]
  rw [mul_pow, mul_pow, hBsq]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem cometricDoubleTraceCoefficient_eq_pureTrace
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, pureTrace_toSection]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_ricciFourTrace_reindexCombination_le
    (g : SmoothRiemannianMetric I M) (F : SmoothCcTensor g 4 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0321 -
            F -
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm2301)) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 F := by
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have h1 := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321)
  have h2 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) F
  have h3 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
        reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321 - F)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm2301)
  rw [covariantJetNormSq_reindexCoeffGen, covariantJetNormSq_reindexCoeffGen] at h1
  rw [covariantJetNormSq_reindexCoeffGen] at h3
  rw [covariantJetNormSq_smul]
  norm_num at h1 h2 h3 ⊢
  linarith

private theorem exists_ricciCometricFourTraceCastG0_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hbdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  let L : ℝ := 22 * C ^ 2
  let B : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C)
  refine ⟨ρ, B, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T gT htie hTn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gT) ≤ C ^ 2 := by
    rw [cometricDoubleTraceCoefficient_eq_pureTrace]
    exact hbdd T gT htie hTn
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination
    (I := I) (M := M) g gT]
  refine (covariantJetNormSq_ricciFourTrace_reindexCombination_le (I := I) (M := M) g _).trans ?_
  rw [show B ^ 2 = L by simpa only [B] using Real.sq_sqrt hL]
  simp only [L]
  exact mul_le_mul_of_nonneg_left hF (by norm_num)

private theorem exists_ricciCometricFourTraceCastG0_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C0, hρ, hC0, hlip⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  let L : ℝ := 22 * C0 ^ 2
  let C : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C0)
  refine ⟨ρ, C, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
        cometricDoubleTraceCoefficient (I := I) (M := M) g gU) ≤
      (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 := by
    rw [cometricDoubleTraceCoefficient_eq_pureTrace, cometricDoubleTraceCoefficient_eq_pureTrace]
    exact hlip T U gT gU hTtie hUtie hTn hUn
  have heq :
      ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU =
        ((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0321 -
            (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
              cometricDoubleTraceCoefficient (I := I) (M := M) g gU) -
            reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindexCoeffGen_sub, reindexCoeffGen_sub, reindexCoeffGen_sub]
    module
  rw [heq]
  refine (covariantJetNormSq_ricciFourTrace_reindexCombination_le (I := I) (M := M) g _).trans ?_
  calc
    22 * covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
          cometricDoubleTraceCoefficient (I := I) (M := M) g gU) ≤
      22 * (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (C *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
      simp only [C, mul_pow]
      rw [Real.sq_sqrt hL]
      simp only [L]
      ring

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem kernelContractionMonomialField_sub
    (g : SmoothRiemannianMetric I M)
    (G H : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    decompositionKernelContractionMonomialField (I := I) (M := M) g g (G - H) σ =
      decompositionKernelContractionMonomialField (I := I) (M := M) g g G σ -
        decompositionKernelContractionMonomialField (I := I) (M := M) g g H σ := by
  classical
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp, hiter]
  rw [domDomCongrSection_sub, slotExtend_sub, slotExtend_sub, rsDomDomCongrSection_sub,
    operatorFieldComposition_sub_right]

private theorem exists_kernelContractionMonomialField_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 G := by
  classical
  obtain ⟨C, hC, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  let P : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (movingMetricPairTraceOperator (I := I) (M := M) g g)
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := C * P * (fr * fr)
  have hP : 0 ≤ P := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨K, mul_nonneg (mul_nonneg hC hP)
    (mul_nonneg hfr hfr), ?_⟩
  intro G σ
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  rw [decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp,
    hiter (domDomCongrSection (I := I) g
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G)]
  refine (happ _ _).trans ?_
  have hjet :
      covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 *
                    Equiv.swap (1 : Fin 4) 3 * σ) G)))) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 G) := by
    rw [covariantJetNormSq_rsDomDomCongrSection]
    calc
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 *
                Equiv.swap (1 : Fin 4) 3 * σ) G)) := by
        simpa only [fr] using
          covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 4) 2 *
              Equiv.swap (1 : Fin 4) 3 * σ) G)) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [fr] using
            covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 G) := by
        rw [covariantJetNormSq_domDomCongrSection]
  have hstep := mul_le_mul_of_nonneg_left hjet
    (mul_nonneg hC hP)
  calc
    C * covariantJetNormSq (I := I) (M := M) g 2
          (movingMetricPairTraceOperator (I := I) (M := M) g g) *
        covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 movingMetricPairTracePermutation
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 *
                    Equiv.swap (1 : Fin 4) 3 * σ) G)))) ≤
      C * P * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 G)) := hstep
    _ = K * covariantJetNormSq (I := I) (M := M) g 2 G := by
      simp only [K, P]
      ring

private theorem exists_ccInputSlotSymm_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ C : SmoothCcTensor g 2 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (ccInputSlotSymm (I := I) (M := M) g C) ≤
          K * covariantJetNormSq (I := I) (M := M) g 2 C := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 2 2
  let Ks : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (ccSlotSwapField (I := I) (M := M) g)
  let K : ℝ := 2 * (1 + Ca * Ks)
  have hKs : 0 ≤ Ks := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num)
      (add_nonneg (by norm_num) (mul_nonneg hCa hKs))
  refine ⟨K, hK, ?_⟩
  intro C
  have ha :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        (Ca * Ks) * covariantJetNormSq (I := I) (M := M) g 2 C := by
    calc
      _ ≤ Ca * covariantJetNormSq (I := I) (M := M) g 2 C * Ks :=
        happ C (ccSlotSwapField (I := I) (M := M) g)
      _ = (Ca * Ks) * covariantJetNormSq (I := I) (M := M) g 2 C := by ring
  simp only [ccInputSlotSymm, ccInputSlotSymm]
  rw [covariantJetNormSq_smul]
  have hsum := covariantJetNormSq_add_le (I := I) (M := M) g 2 C
    (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
      (ccSlotSwapField (I := I) (M := M) g))
  have hC0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g C
  have hsum0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (C + ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C
      (ccSlotSwapField (I := I) (M := M) g))
  simp only [K]
  norm_num
  nlinarith only [ha, hsum, hC0, hsum0]

private theorem exists_ricciQuadraticConnectionArm_fourthOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gU) ≤
        (B0 R * (1 + A) * (D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨ρb, Fb, hρb, hFb, htraceB⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨ρd, Fd, hρd, hFd, htraceD⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Bk, hBk, hkerB⟩ :=
    exists_ricciQuadraticConnectionKernel_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hkerD⟩ :=
    exists_ricciQuadraticConnectionKernel_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Cj, hCj, hinterp⟩ :=
    covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  let Cs : ℝ := Real.sqrt (2 * Ca)
  have hCs : 0 ≤ Cs := Real.sqrt_nonneg _
  have hCsSq : Cs ^ 2 = 2 * Ca := by
    simpa only [Cs] using
      Real.sq_sqrt (mul_nonneg (by norm_num) hCa)
  let α : ℝ → ℝ := fun R => Cs * Fd * Bk R
  let β : ℝ → ℝ := fun R => Cs * Fb * Bd R
  let B0 : ℝ → ℝ := fun R => 2 * α R + 4 * β R
  let B1 : ℝ → ℝ := fun R =>
    2 * α R * Cj * R + 4 * β R * Cj * R
  have hα : ∀ R : ℝ, 0 ≤ R → 0 ≤ α R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCs hFd) (hBk R hR)
  have hβ : ∀ R : ℝ, 0 ≤ R → 0 ≤ β R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCs hFb) (hBd R hR)
  refine ⟨min ρb ρd, B0, B1, lt_min hρb hρd, ?_, ?_, ?_⟩
  · intro R hR
    exact add_nonneg
      (mul_nonneg (by norm_num) (hα R hR))
      (mul_nonneg (by norm_num) (hβ R hR))
  · intro R hR
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (hα R hR)) hCj) hR)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (hβ R hR)) hCj) hR)
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 N hR hA hA4 hD2 hD3 hN
    hT2 hU2 hT4 hU4 hTU3 hTn hUn hTUn
  let X : ℝ := Cj * (R * A4)
  let Ap : ℝ := Real.sqrt X
  have hX : 0 ≤ X :=
    mul_nonneg hCj (mul_nonneg hR hA4)
  have hAp : 0 ≤ Ap := Real.sqrt_nonneg _
  have hApSq : Ap ^ 2 = X := by
    simpa only [Ap] using Real.sq_sqrt hX
  have hT3i :
      covariantJetNormSq (I := I) (M := M) g 3 T ≤ Ap ^ 2 := by
    rw [hApSq]
    exact hinterp T R A4 hR hA4 hT2 hT4
  have hU3i :
      covariantJetNormSq (I := I) (M := M) g 3 U ≤ Ap ^ 2 := by
    rw [hApSq]
    exact hinterp U R A4 hR hA4 hU2 hU4
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) (T - U)).trans hTU3
  have hTb :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb :=
    hTn.trans (min_le_left _ _)
  have hUb :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρb :=
    hUn.trans (min_le_left _ _)
  have hTd :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρd :=
    hTn.trans (min_le_right _ _)
  have hUd :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρd :=
    hUn.trans (min_le_right _ _)
  let FT := ricciCometricFourTraceCastG0 (I := I) g gT
  let FU := ricciCometricFourTraceCastG0 (I := I) g gU
  let KT := ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT
  let KU := ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU
  have hFU :
      covariantJetNormSq (I := I) (M := M) g 2 FU ≤ Fb ^ 2 :=
    htraceB U gU hUtie hUb
  have hFTU :
      covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
        (Fd * N) ^ 2 := by
    refine (htraceD T U gT gU hTtie hUtie hTd hUd).trans ?_
    have hn0 := norm_nonneg
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U))
    have hmul : Fd *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤
        Fd * N := mul_le_mul_of_nonneg_left hTUn hFd
    exact pow_le_pow_left₀ (mul_nonneg hFd hn0) hmul 2
  have hKT :
      covariantJetNormSq (I := I) (M := M) g 2 KT ≤
        (Bk R * (1 + Ap) ^ 2) ^ 2 :=
    hkerB gT T hT hTtie hδ_le hδ0 hδT hδZ
      R Ap hR hAp hT2 hT3i
  have hKTU :
      covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) ≤
        (Bd R * (1 + Ap) * (D3 + D3 + Ap * D3)) ^ 2 :=
    hkerD gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
      R Ap D3 D3 hR hAp hD3 hD3 hT2 hU2 hT3i hU3i hTU2 hTU3
  have heq :
      ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gT -
          ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gU =
        ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT +
          ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU) := by
    simp only [ricciConnectionDifferenceQuadraticArm, FT, FU, KT, KU, operatorFieldComposition_sub_left,
      operatorFieldComposition_sub_right]
    module
  let x : ℝ := α R * N * (1 + Ap) ^ 2
  let y : ℝ := β R * (1 + Ap) * (D3 + D3 + Ap * D3)
  have hx0 : 0 ≤ x :=
    mul_nonneg
      (mul_nonneg (hα R hR) hN)
      (sq_nonneg _)
  have hy0 : 0 ≤ y :=
    mul_nonneg
      (mul_nonneg (hβ R hR) (add_nonneg zero_le_one hAp))
      (add_nonneg (add_nonneg hD3 hD3) (mul_nonneg hAp hD3))
  have hterm1 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT) ≤
        Ca * (Fd * N) ^ 2 * (Bk R * (1 + Ap) ^ 2) ^ 2 := by
    refine (happ (FT - FU) KT).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hFTU hCa) hKT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g KT)
      (mul_nonneg hCa (sq_nonneg _))
  have hterm2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU)) ≤
        Ca * Fb ^ 2 *
          (Bd R * (1 + Ap) * (D3 + D3 + Ap * D3)) ^ 2 := by
    refine (happ FU (KT - KU)).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hFU hCa) hKTU
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (KT - KU))
      (mul_nonneg hCa (sq_nonneg Fb))
  rw [heq]
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT +
            ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU)) ≤
        x ^ 2 + y ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have hx :
        2 * (Ca * (Fd * N) ^ 2 *
          (Bk R * (1 + Ap) ^ 2) ^ 2) = x ^ 2 := by
      simp only [x, α, mul_pow, hCsSq]
      ring
    have hy :
        2 * (Ca * Fb ^ 2 *
          (Bd R * (1 + Ap) * (D3 + D3 + Ap * D3)) ^ 2) =
          y ^ 2 := by
      simp only [y, β, mul_pow, hCsSq]
      ring
    rw [← hx, ← hy]
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hterm1 (by norm_num))
      (mul_le_mul_of_nonneg_left hterm2 (by norm_num))
  refine hsum.trans ?_
  have hxy : x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 :=
    sq_add_sq_le_sq_add_of_nonneg (a := x) (b := y) hx0 hy0
  refine hxy.trans ?_
  have hApLe : Ap ≤ (1 + X) / 2 := by
    rw [← hApSq]
    nlinarith only [sq_nonneg (Ap - 1)]
  have hfac1 : (1 + Ap) ^ 2 ≤ 2 * (1 + X) := by
    calc
      (1 + Ap) ^ 2 = 1 + 2 * Ap + Ap ^ 2 := by ring
      _ = 1 + 2 * Ap + X := by rw [hApSq]
      _ ≤ 2 * (1 + X) := by linarith only [hApLe]
  have hfac2 : (1 + Ap) * (2 + Ap) ≤ 4 * (1 + X) := by
    calc
      (1 + Ap) * (2 + Ap) = 2 + 3 * Ap + Ap ^ 2 := by ring
      _ = 2 + 3 * Ap + X := by rw [hApSq]
      _ ≤ 4 * (1 + X) := by linarith only [hApLe, hX]
  have hxlin :
      x ≤ 2 * α R * N + 2 * α R * Cj * R * A4 * N := by
    calc
      x ≤ α R * N * (2 * (1 + X)) :=
        mul_le_mul_of_nonneg_left hfac1
          (mul_nonneg (hα R hR) hN)
      _ = 2 * α R * N + 2 * α R * Cj * R * A4 * N := by
        simp only [X]
        ring
  have hylin :
      y ≤ 4 * β R * D3 + 4 * β R * Cj * R * A4 * D3 := by
    calc
      y = β R * ((1 + Ap) * (2 + Ap)) * D3 := by
        simp only [y]
        ring
      _ ≤ β R * (4 * (1 + X)) * D3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac2 (hβ R hR)) hD3
      _ = 4 * β R * D3 + 4 * β R * Cj * R * A4 * D3 := by
        simp only [X]
        ring
  let Z : ℝ := B0 R * (1 + A) * (D3 + D2 + N) +
    B1 R * A4 * (D3 + N)
  have hZ : 0 ≤ Z := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (add_nonneg
            (mul_nonneg (by norm_num) (hα R hR))
            (mul_nonneg (by norm_num) (hβ R hR)))
          (add_nonneg zero_le_one hA))
        (add_nonneg (add_nonneg hD3 hD2) hN))
      (mul_nonneg
        (mul_nonneg
          (add_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (hα R hR)) hCj) hR)
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (hβ R hR)) hCj) hR))
          hA4)
        (add_nonneg hD3 hN))
  have hlin : x + y ≤ Z := by
    have hlo :
        2 * α R * N + 4 * β R * D3 ≤
          B0 R * (1 + A) * (D3 + D2 + N) := by
      have hbase : D3 ≤ D3 + D2 + N := by
        calc
          D3 ≤ D3 + (D2 + N) :=
            le_add_of_nonneg_right (add_nonneg hD2 hN)
          _ = D3 + D2 + N := by ring
      have hbaseN : N ≤ D3 + D2 + N := by
        calc
          N ≤ D2 + N := le_add_of_nonneg_left hD2
          _ ≤ D3 + (D2 + N) := le_add_of_nonneg_left hD3
          _ = D3 + D2 + N := by ring
      have hfac :
          D3 + D2 + N ≤ (1 + A) * (D3 + D2 + N) := by
        calc
          D3 + D2 + N = 1 * (D3 + D2 + N) := (one_mul _).symm
          _ ≤ (1 + A) * (D3 + D2 + N) :=
            mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hA) (add_nonneg (add_nonneg hD3 hD2) hN)
      have hN :
          2 * α R * N ≤
            2 * α R * ((1 + A) * (D3 + D2 + N)) := by
        exact mul_le_mul_of_nonneg_left (hbaseN.trans hfac)
          (mul_nonneg (by norm_num) (hα R hR))
      have hD :
          4 * β R * D3 ≤
            4 * β R * ((1 + A) * (D3 + D2 + N)) := by
        exact mul_le_mul_of_nonneg_left (hbase.trans hfac)
          (mul_nonneg (by norm_num) (hβ R hR))
      simp only [B0]
      calc
        2 * α R * N + 4 * β R * D3 ≤
            2 * α R * ((1 + A) * (D3 + D2 + N)) +
              4 * β R * ((1 + A) * (D3 + D2 + N)) :=
          add_le_add hN hD
        _ = (2 * α R + 4 * β R) * (1 + A) *
              (D3 + D2 + N) := by ring
    have hhi :
        2 * α R * Cj * R * A4 * N +
            4 * β R * Cj * R * A4 * D3 ≤
          B1 R * A4 * (D3 + N) := by
      have hc1 :
          0 ≤ 2 * α R * Cj * R * A4 * D3 := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (hα R hR)) hCj) hR)
              hA4)
          hD3
      have hc2 :
          0 ≤ 4 * β R * Cj * R * A4 * N := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (hβ R hR)) hCj) hR)
              hA4)
          hN
      simp only [B1]
      calc
        2 * α R * Cj * R * A4 * N +
            4 * β R * Cj * R * A4 * D3 ≤
          2 * α R * Cj * R * A4 * N +
              4 * β R * Cj * R * A4 * D3 +
            (2 * α R * Cj * R * A4 * D3 +
              4 * β R * Cj * R * A4 * N) :=
          le_add_of_nonneg_right (add_nonneg hc1 hc2)
        _ = (2 * α R * Cj * R + 4 * β R * Cj * R) * A4 * (D3 + N) := by
          ring
    calc
      x + y ≤
          (2 * α R * N + 2 * α R * Cj * R * A4 * N) +
            (4 * β R * D3 + 4 * β R * Cj * R * A4 * D3) :=
        add_le_add hxlin hylin
      _ =
          (2 * α R * N + 4 * β R * D3) +
            (2 * α R * Cj * R * A4 * N +
              4 * β R * Cj * R * A4 * D3) := by ring
      _ ≤
          B0 R * (1 + A) * (D3 + D2 + N) +
            B1 R * A4 * (D3 + N) :=
        add_le_add hlo hhi
      _ = Z := rfl
  exact pow_le_pow_left₀ (add_nonneg hx0 hy0) hlin 2

private theorem exists_ricciConnectionDerivativeArm_fourthOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A A4 D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U) ≤
        (B0 R * (1 + A) * (D3 + D2) +
          B1 R * A4 * D3) ^ 2 := by
  obtain ⟨Kd, hKd, hdagB⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bd, hBd, hdagD⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Be, hBe, hslotB⟩ :=
    RicciDeTurckLowOrder.full_slot_sobolev_two_bound (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bed, hBed, hslotD⟩ :=
    exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, happG⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Kr, hKr, hdecomposition⟩ :=
    exists_kernelContractionMonomialField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happA⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Cj, hCj, hinterp⟩ :=
    covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  let Sd : ℝ := Real.sqrt Kd
  let Sg : ℝ := Real.sqrt (2 * Cg)
  let Su : ℝ := Real.sqrt (Cg * Kd)
  let Sm : ℝ := Real.sqrt (2 * Ca * Kr)
  have hSd : 0 ≤ Sd := Real.sqrt_nonneg _
  have hSg : 0 ≤ Sg := Real.sqrt_nonneg _
  have hSu : 0 ≤ Su := Real.sqrt_nonneg _
  have hSm : 0 ≤ Sm := Real.sqrt_nonneg _
  have hSdSq : Sd ^ 2 = Kd := by
    simpa only [Sd] using Real.sq_sqrt hKd
  have hSgSq : Sg ^ 2 = 2 * Cg := by
    simpa only [Sg] using Real.sq_sqrt (mul_nonneg (by norm_num) hCg)
  have hSuSq : Su ^ 2 = Cg * Kd := by
    simpa only [Su] using Real.sq_sqrt (mul_nonneg hCg hKd)
  have hSmSq : Sm ^ 2 = 2 * Ca * Kr := by
    simpa only [Sm] using
      Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hCa) hKr)
  let K : ℝ → ℝ := fun R =>
    4 * Sm *
      (Sg * (Bd R + Sd) * Be R + Su * Bed R)
  let B0 : ℝ → ℝ := K
  let B1 : ℝ → ℝ := fun R => K R * Cj * R
  have hK : ∀ R : ℝ, 0 ≤ R → 0 ≤ K R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (by norm_num) hSm)
      (add_nonneg
        (mul_nonneg
          (mul_nonneg hSg (add_nonneg (hBd R hR) hSd))
          (hBe R hR))
        (mul_nonneg hSu (hBed R hR)))
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact hK R hR
  · intro R hR
    exact mul_nonneg
      (mul_nonneg (hK R hR) hCj) hR
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU
    R A A4 D2 D3 hR hA hA4 hD2 hD3
    hT2 hU2 hT4 hU4 hTU3
  let X : ℝ := Cj * (R * A4)
  let Ap : ℝ := Real.sqrt X
  have hX : 0 ≤ X :=
    mul_nonneg hCj (mul_nonneg hR hA4)
  have hAp : 0 ≤ Ap := Real.sqrt_nonneg _
  have hApSq : Ap ^ 2 = X := by
    simpa only [Ap] using Real.sq_sqrt hX
  have hT3i :
      covariantJetNormSq (I := I) (M := M) g 3 T ≤ Ap ^ 2 := by
    rw [hApSq]
    exact hinterp T R A4 hR hA4 hT2 hT4
  have hU3i :
      covariantJetNormSq (I := I) (M := M) g 3 U ≤ Ap ^ 2 := by
    rw [hApSq]
    exact hinterp U R A4 hR hA4 hU2 hU4
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) (T - U)).trans hTU3
  have hdagU0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        Kd * (1 + Ap ^ 2) :=
    hdagB gU U hU hUtie hδ_le hδ0 hδU
      |>.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hU3i) hKd)
  have hdagU :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (Sd * (1 + Ap)) ^ 2 := by
    refine hdagU0.trans ?_
    rw [mul_pow, hSdSq]
    apply mul_le_mul_of_nonneg_left _ hKd
    calc
      1 + Ap ^ 2 ≤ 1 + Ap ^ 2 + 2 * Ap :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) hAp)
      _ = (1 + Ap) ^ 2 := by ring
  have hdagD0 :=
    hdagD gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R Ap D3 D3 hR hAp hD3 hD3
      hT2 hU2 hT3i hU3i hTU2 hTU3
  have hdagDiff :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
            RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (Bd R * (2 + Ap) * D3) ^ 2 := by
    simpa only [
      show D3 + D3 + Ap * D3 = (2 + Ap) * D3 by ring,
      mul_assoc] using hdagD0
  have hgradT :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 T) ≤ Ap ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g T).trans hT3i
  have hgradU :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 U) ≤ Ap ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g U).trans hU3i
  have hgradDiff :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 (T - U)) ≤ D3 ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g (T - U)).trans hTU3
  let GT : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT)
      (covGrad (I := I) (M := M) g 0 2 T)
  let GU : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
      (covGrad (I := I) (M := M) g 0 2 U)
  let x : ℝ := Sg * Bd R * Ap * (2 + Ap) * D3
  let y : ℝ := Sg * Sd * (1 + Ap) * D3
  let z : ℝ := Su * (1 + Ap) * Ap
  have hx0 : 0 ≤ x :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hSg (hBd R hR)) hAp)
          (add_nonneg (by norm_num) hAp))
      hD3
  have hy0 : 0 ≤ y :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hSg hSd)
        (add_nonneg zero_le_one hAp))
      hD3
  have hz0 : 0 ≤ z :=
    mul_nonneg (mul_nonneg hSu (add_nonneg zero_le_one hAp)) hAp
  have hGcomb :
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
            RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 T) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 (T - U)) =
        GT - GU := by
    simp only [GT, GU]
    rw [operatorFieldComposition_sub_left, covGrad_sub, operatorFieldComposition_sub_right]
    module
  have hGterm1 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
            (covGrad (I := I) (M := M) g 0 2 T)) ≤
        Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2 := by
    refine (happG _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hdagDiff hCg) hgradT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (covGrad (I := I) (M := M) g 0 2 T))
      (mul_nonneg hCg (sq_nonneg _))
  have hGterm2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
            (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
        Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2 := by
    refine (happG _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hdagU hCg) hgradDiff
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (covGrad (I := I) (M := M) g 0 2 (T - U)))
      (mul_nonneg hCg (sq_nonneg _))
  have hxSq :
      2 * (Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2) = x ^ 2 := by
    simp only [x, mul_pow, hSgSq]
    ring
  have hySq :
      2 * (Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2) = y ^ 2 := by
    simp only [y, mul_pow, hSgSq, hSdSq]
    ring
  have hGdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (GT - GU) ≤ (x + y) ^ 2 := by
    rw [← hGcomb]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
                (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
                  RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
                (covGrad (I := I) (M := M) g 0 2 T)) +
            covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
                (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
                (covGrad (I := I) (M := M) g 0 2 (T - U)))) ≤
          2 * (Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2 +
            Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hGterm1 hGterm2) (by norm_num)
      _ = x ^ 2 + y ^ 2 := by rw [← hxSq, ← hySq]; ring
      _ ≤ (x + y) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hx0 hy0
  have hGU :
      covariantJetNormSq (I := I) (M := M) g 2 GU ≤ z ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 GU ≤
          Cg * covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g 0 2 U) := by
        simpa only [GU] using happG
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 U)
      _ ≤ Cg * (Sd * (1 + Ap)) ^ 2 * Ap ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdagU hCg) hgradU
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
            (covGrad (I := I) (M := M) g 0 2 U))
          (mul_nonneg hCg (sq_nonneg _))
      _ = z ^ 2 := by
        simp only [z, mul_pow, hSdSq, hSuSq]
        ring
  let ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT)
  let EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU)
  have hET :
      covariantJetNormSq (I := I) (M := M) g 2 ET ≤ (Be R) ^ 2 := by
    simpa only [ET] using
      hslotB gT T hT hTtie hδ_le hδ0 hδT R hR hT2
  have hEdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (ET - EU) ≤
        (Bed R * D3) ^ 2 := by
    simpa only [ET, EU] using
      hslotD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R D3 hR hD3 hT2 hU2 hTU2
  let u : ℝ := Sm * (x + y) * Be R
  let v : ℝ := Sm * z * Bed R * D3
  have hu0 : 0 ≤ u :=
    mul_nonneg (mul_nonneg hSm (add_nonneg hx0 hy0)) (hBe R hR)
  have hv0 : 0 ≤ v :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hSm hz0) (hBed R hR)) hD3
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ) ≤
        (u + v) ^ 2 := by
    intro σ
    have hfT :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GT σ) ET := by
      rfl
    have hfU :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GU σ) EU := by
      rfl
    have hsplit :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g (GT - GU) σ) ET +
            ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g GU σ) (ET - EU) := by
      rw [hfT, hfU, kernelContractionMonomialField_sub]
      rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
      module
    have hrDiff :
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g (GT - GU) σ) ≤
          Kr * (x + y) ^ 2 :=
      (hdecomposition (GT - GU) σ).trans
        (mul_le_mul_of_nonneg_left hGdiff hKr)
    have hrU :
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GU σ) ≤
          Kr * z ^ 2 :=
      (hdecomposition GU σ).trans
        (mul_le_mul_of_nonneg_left hGU hKr)
    have hterm1 :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g (GT - GU) σ) ET) ≤
          Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2 := by
      refine (happA _ _).trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hrDiff hCa) hET
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g ET)
        (mul_nonneg hCa (mul_nonneg hKr (sq_nonneg _)))
    have hterm2 :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g GU σ) (ET - EU)) ≤
          Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2 := by
      refine (happA _ _).trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hrU hCa) hEdiff
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (ET - EU))
        (mul_nonneg hCa (mul_nonneg hKr (sq_nonneg z)))
    have huSq :
        2 * (Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2) = u ^ 2 := by
      simp only [u, mul_pow, hSmSq]
      ring
    have hvSq :
        2 * (Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2) = v ^ 2 := by
      simp only [v, mul_pow, hSmSq]
      ring
    rw [hsplit]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
                (decompositionKernelContractionMonomialField
                  (I := I) (M := M) g g (GT - GU) σ) ET) +
            covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
                (decompositionKernelContractionMonomialField
                  (I := I) (M := M) g g GU σ) (ET - EU))) ≤
          2 * (Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2 +
            Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ = u ^ 2 + v ^ 2 := by rw [← huSq, ← hvSq]; ring
      _ ≤ (u + v) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hu0 hv0
  have hDAT :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T =
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by
    rfl
  have hDAU :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U =
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by
    rfl
  have hsplit :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U =
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) -
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap) := by
    rw [hDAT, hDAU]
    abel
  have hDAraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U) ≤
        (2 * (u + v)) ^ 2 := by
    rw [hsplit]
    refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 _ _).trans ?_
    have hpa := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
    have hpb := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
                RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) +
            covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
                RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)) ≤
          2 * ((u + v) ^ 2 + (u + v) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hpa hpb) (by norm_num)
      _ = (2 * (u + v)) ^ 2 := by ring
  have hApLe : Ap ≤ (1 + X) / 2 := by
    rw [← hApSq]
    nlinarith only [sq_nonneg (Ap - 1)]
  have hfac1 : Ap * (2 + Ap) ≤ 2 * (1 + X) := by
    rw [show Ap * (2 + Ap) = 2 * Ap + X by rw [← hApSq]; ring]
    linarith only [hApLe]
  have hfac2 : 1 + Ap ≤ 2 * (1 + X) := by
    linarith only [hApLe, hX]
  have hfac3 : (1 + Ap) * Ap ≤ 2 * (1 + X) := by
    rw [show (1 + Ap) * Ap = Ap + X by rw [← hApSq]; ring]
    linarith only [hApLe, hX]
  have hxlin :
      x ≤ 2 * Sg * Bd R * (1 + X) * D3 := by
    calc
      x = Sg * Bd R * (Ap * (2 + Ap)) * D3 := by
        simp only [x]
        ring
      _ ≤ Sg * Bd R * (2 * (1 + X)) * D3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac1
            (mul_nonneg hSg (hBd R hR))) hD3
      _ = 2 * Sg * Bd R * (1 + X) * D3 := by ring
  have hylin :
      y ≤ 2 * Sg * Sd * (1 + X) * D3 := by
    calc
      y ≤ Sg * Sd * (2 * (1 + X)) * D3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac2
            (mul_nonneg hSg hSd)) hD3
      _ = 2 * Sg * Sd * (1 + X) * D3 := by ring
  have hzlin :
      z ≤ 2 * Su * (1 + X) := by
    calc
      z = Su * ((1 + Ap) * Ap) := by
        simp only [z]
        ring
      _ ≤ Su * (2 * (1 + X)) :=
        mul_le_mul_of_nonneg_left hfac3 hSu
      _ = 2 * Su * (1 + X) := by ring
  have hxy :
      x + y ≤
        2 * Sg * (Bd R + Sd) * (1 + X) * D3 := by
    calc
      x + y ≤
          2 * Sg * Bd R * (1 + X) * D3 +
            2 * Sg * Sd * (1 + X) * D3 :=
        add_le_add hxlin hylin
      _ = 2 * Sg * (Bd R + Sd) * (1 + X) * D3 := by ring
  have huLin :
      u ≤
        2 * Sm * (Sg * (Bd R + Sd) * Be R) *
          (1 + X) * D3 := by
    calc
      u ≤ Sm *
          (2 * Sg * (Bd R + Sd) * (1 + X) * D3) * Be R := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxy hSm) (hBe R hR)
      _ =
          2 * Sm * (Sg * (Bd R + Sd) * Be R) *
            (1 + X) * D3 := by ring
  have hvLin :
      v ≤
        2 * Sm * (Su * Bed R) * (1 + X) * D3 := by
    calc
      v ≤ Sm * (2 * Su * (1 + X)) * Bed R * D3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hzlin hSm)
            (hBed R hR)) hD3
      _ = 2 * Sm * (Su * Bed R) * (1 + X) * D3 := by ring
  have huv :
      u + v ≤
        2 * Sm *
          (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
          (1 + X) * D3 := by
    calc
      u + v ≤
          2 * Sm * (Sg * (Bd R + Sd) * Be R) *
              (1 + X) * D3 +
            2 * Sm * (Su * Bed R) * (1 + X) * D3 :=
        add_le_add huLin hvLin
      _ =
          2 * Sm *
            (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
            (1 + X) * D3 := by ring
  let Z : ℝ :=
    B0 R * (1 + A) * (D3 + D2) + B1 R * A4 * D3
  have hZ : 0 ≤ Z := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (hK R hR) (add_nonneg zero_le_one hA))
        (add_nonneg hD3 hD2))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (hK R hR) hCj) hR) hA4)
        hD3)
  have hlo :
      K R * D3 ≤ K R * (1 + A) * (D3 + D2) := by
    have hs : D3 ≤ (1 + A) * (D3 + D2) := by
      calc
        D3 ≤ D3 + D2 := le_add_of_nonneg_right hD2
        _ ≤ (1 + A) * (D3 + D2) := by
          calc
            D3 + D2 = 1 * (D3 + D2) := (one_mul _).symm
            _ ≤ (1 + A) * (D3 + D2) :=
              mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right hA) (add_nonneg hD3 hD2)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hs (hK R hR)
  have hscale : 2 * (u + v) ≤ Z := by
    calc
      2 * (u + v) ≤
          4 * Sm *
            (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
            (1 + X) * D3 :=
        calc
          2 * (u + v) ≤
              2 * (2 * Sm *
                (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
                (1 + X) * D3) :=
            mul_le_mul_of_nonneg_left huv (by norm_num : (0 : ℝ) ≤ 2)
          _ =
              4 * Sm *
                (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
                (1 + X) * D3 := by ring
      _ = K R * D3 + (K R * Cj * R) * A4 * D3 := by
        simp only [K, X]
        ring
      _ ≤ K R * (1 + A) * (D3 + D2) +
            (K R * Cj * R) * A4 * D3 :=
        add_le_add hlo
          (le_refl ((K R * Cj * R) * A4 * D3))
      _ = Z := by rfl
  exact hDAraw.trans
    (pow_le_pow_left₀
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg hu0 hv0))
      hscale 2)

theorem RicciDeTurckLowOrder.exists_symmetricRicciTerm_covariantJetNormSq_tame_difference_bound
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
          (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 :=
by
  obtain ⟨Ks, hKs, hsymm⟩ :=
    exists_ccInputSlotSymm_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨ρA, BA0, BA1, hρA, hBA0, hBA1, haa⟩ :=
    exists_ricciQuadraticConnectionArm_fourthOrder_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨BD0, BD1, hBD0, hBD1, hda⟩ :=
    exists_ricciConnectionDerivativeArm_fourthOrder_tame_difference_bound (I := I) (M := M) hDim g
  let Cs : ℝ := Real.sqrt (2 * Ks)
  have hCs : 0 ≤ Cs := Real.sqrt_nonneg _
  have hCsSq : Cs ^ 2 = 2 * Ks := by
    simpa only [Cs] using
      Real.sq_sqrt (mul_nonneg (by norm_num) hKs)
  let B0 : ℝ → ℝ := fun R => Cs * (BA0 R + BD0 R)
  let B1 : ℝ → ℝ := fun R => Cs * (BA1 R + BD1 R)
  refine ⟨ρA, B0, B1, hρA, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hCs
      (add_nonneg (hBA0 R hR) (hBD0 R hR))
  · intro R hR
    exact mul_nonneg hCs
      (add_nonneg (hBA1 R hR) (hBD1 R hR))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn
    s hs
  have hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith only [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP4 : covariantJetNormSq (I := I) (M := M) g 4 P ≤ A4 ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g T) hs2).trans hT4
  have hQ4 : covariantJetNormSq (I := I) (M := M) g 4 Q ≤ A4 ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g U) hs2).trans hU4
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρA := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn)
  have hQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρA := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn)
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  let SA : ℝ :=
    BA0 R * (1 + A) * (D3 + D2 + N) +
      BA1 R * A4 * (D3 + N)
  let SD : ℝ :=
    BD0 R * (1 + A) * (D3 + D2) +
      BD1 R * A4 * D3
  have hSA0 : 0 ≤ SA := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (hBA0 R hR) (by linarith))
        (by linarith))
      (mul_nonneg
        (mul_nonneg (hBA1 R hR) hA4)
        (add_nonneg hD3 hN))
  have hSD0 : 0 ≤ SD := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (hBD0 R hR) (by linarith))
        (add_nonneg hD3 hD2))
      (mul_nonneg
        (mul_nonneg (hBD1 R hR) hA4) hD3)
  have hAA :
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) ≤ SA ^ 2 := by
    simpa only [SA] using
      haa gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        R A A4 D2 D3 N hR hA hA4 hD2 hD3 hN
        hP2 hQ2 hP4 hQ4 hPQ3 hPn hQn hPQn
  have hDA :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) ≤
        SD ^ 2 := by
    simpa only [SD] using
      hda gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ
        R A A4 D2 D3 hR hA hA4 hD2 hD3
        hP2 hQ2 hP4 hQ4 hPQ3
  have hlowT :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P =
        ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT +
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P := rfl
  have hlowU :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU +
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q := rfl
  have hlow :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) := by
    rw [hlowT, hlowU]
    abel
  have hgood :
      RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        ccInputSlotSymm (I := I) (M := M) g
          ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) := by
    change
      ccInputSlotSymm (I := I) (M := M) g
            (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P) -
          ccInputSlotSymm (I := I) (M := M) g
            (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q) =
        _
    rw [ccInputSlotSymm_sub, hlow]
  let W : ℝ :=
    (BA0 R + BD0 R) * (1 + A) * (D4 + D3 + D2 + N) +
      (BA1 R + BD1 R) * A4 * (D3 + N)
  have hLAA :
      (1 + A) * (D3 + D2 + N) ≤
        (1 + A) * (D4 + D3 + D2 + N) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hLDA :
      (1 + A) * (D3 + D2) ≤
        (1 + A) * (D4 + D3 + D2 + N) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hHDA :
      A4 * D3 ≤ A4 * (D3 + N) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hN) hA4
  have hSAle :
      SA ≤
        BA0 R * ((1 + A) * (D4 + D3 + D2 + N)) +
          BA1 R * (A4 * (D3 + N)) := by
    simp only [SA]
    exact add_le_add
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hLAA (hBA0 R hR))
      (by
        ring_nf
        exact le_rfl)
  have hSDle :
      SD ≤
        BD0 R * ((1 + A) * (D4 + D3 + D2 + N)) +
          BD1 R * (A4 * (D3 + N)) := by
    simp only [SD]
    exact add_le_add
      (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hLDA (hBD0 R hR))
      (by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hHDA (hBD1 R hR))
  have hsum : SA + SD ≤ W := by
    calc
      SA + SD ≤
          (BA0 R * ((1 + A) * (D4 + D3 + D2 + N)) +
              BA1 R * (A4 * (D3 + N))) +
            (BD0 R * ((1 + A) * (D4 + D3 + D2 + N)) +
              BD1 R * (A4 * (D3 + N))) :=
        add_le_add hSAle hSDle
      _ = W := by
        simp only [W]
        ring
  have hW0 : 0 ≤ W := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (add_nonneg (hBA0 R hR) (hBD0 R hR))
          (by linarith))
        (by linarith))
      (mul_nonneg
        (mul_nonneg
          (add_nonneg (hBA1 R hR) (hBD1 R hR)) hA4)
        (add_nonneg hD3 hN))
  rw [show
      RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U) =
        RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q by
      rw [hgmT, hgmU, hcP, hcQ],
    hgood]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccInputSlotSymm (I := I) (M := M) g
          ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q))) ≤
      Ks * covariantJetNormSq (I := I) (M := M) g 2
        ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) :=
      hsymm _
    _ ≤ Ks * (2 * (SA ^ 2 + SD ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hKs
      refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
      exact mul_le_mul_of_nonneg_left (add_le_add hAA hDA) (by norm_num)
    _ ≤ Ks * (2 * (SA + SD) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sq_add_sq_le_sq_add_of_nonneg hSA0 hSD0) (by norm_num)) hKs
    _ ≤ Ks * (2 * W ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg hSA0 hSD0) hsum 2) (by norm_num)) hKs
    _ = (Cs * W) ^ 2 := by
      conv_rhs => rw [mul_pow, hCsSq]
      ring
    _ =
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
      simp only [B0, B1, W]
      apply congrArg (fun x : ℝ => x ^ 2)
      ring

private theorem exists_ricciQuadraticConnectionArm_thirdOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
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
          (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gU) ≤
        (B R * (1 + A) ^ 2 * (D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρb, Fb, hρb, hFb, htraceB⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨ρd, Fd, hρd, hFd, htraceD⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Bk, hBk, hkerB⟩ :=
    exists_ricciQuadraticConnectionKernel_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hkerD⟩ :=
    exists_ricciQuadraticConnectionKernel_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  let Cs : ℝ := Real.sqrt (2 * Ca)
  let B : ℝ → ℝ := fun R => Cs * (Fd * Bk R + Fb * Bd R)
  have hCs : 0 ≤ Cs := Real.sqrt_nonneg _
  have hCsSq : Cs ^ 2 = 2 * Ca := by
    simpa only [Cs] using Real.sq_sqrt (mul_nonneg (by norm_num) hCa)
  refine ⟨min ρb ρd, B, lt_min hρb hρd, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hCs
      (add_nonneg
        (mul_nonneg hFd (hBk R hR))
        (mul_nonneg hFb (hBd R hR)))
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTn hUn hTUn
  have hTb := hTn.trans (min_le_left ρb ρd)
  have hUb := hUn.trans (min_le_left ρb ρd)
  have hTd := hTn.trans (min_le_right ρb ρd)
  have hUd := hUn.trans (min_le_right ρb ρd)
  let FT := ricciCometricFourTraceCastG0 (I := I) g gT
  let FU := ricciCometricFourTraceCastG0 (I := I) g gU
  let KT := ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gT
  let KU := ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gU
  have hFU : covariantJetNormSq (I := I) (M := M) g 2 FU ≤ Fb ^ 2 :=
    htraceB U gU hUtie hUb
  have hFTU : covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
      (Fd * N) ^ 2 := by
    refine (htraceD T U gT gU hTtie hUtie hTd hUd).trans ?_
    exact pow_le_pow_left₀
      (mul_nonneg hFd (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hTUn hFd) 2
  have hKT : covariantJetNormSq (I := I) (M := M) g 2 KT ≤
      (Bk R * (1 + A) ^ 2) ^ 2 :=
    hkerB gT T hT hTtie hδ_le hδ0 hδT hδZ
      R A hR hA hT2 hT3
  have hKTU : covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) ≤
      (Bd R * (1 + A) * (D3 + D2 + A * D2)) ^ 2 :=
    hkerD gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  have heq :
      ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gT -
          ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gU =
        ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT +
          ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU) := by
    simp only [ricciConnectionDifferenceQuadraticArm, FT, FU, KT, KU, operatorFieldComposition_sub_left,
      operatorFieldComposition_sub_right]
    module
  let Q : ℝ := 1 + A
  let S : ℝ := D3 + D2 + N
  let x : ℝ := Cs * Fd * Bk R * N * Q ^ 2
  let y : ℝ := Cs * Fb * Bd R * Q * (D3 + D2 + A * D2)
  have hQ : 0 ≤ Q := by simp only [Q]; exact add_nonneg zero_le_one hA
  have hS : 0 ≤ S := by simp only [S]; exact add_nonneg (add_nonneg hD3 hD2) hN
  have hx0 : 0 ≤ x := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCs hFd) (hBk R hR)) hN)
      (sq_nonneg Q)
  have hy0 : 0 ≤ y := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCs hFb) (hBd R hR)) hQ)
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hterm1 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT) ≤
        Ca * (Fd * N) ^ 2 * (Bk R * Q ^ 2) ^ 2 := by
    refine (happ (FT - FU) KT).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hFTU hCa) (by simpa only [Q] using hKT)
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g KT)
      (mul_nonneg hCa (sq_nonneg _))
  have hterm2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU)) ≤
        Ca * Fb ^ 2 *
          (Bd R * Q * (D3 + D2 + A * D2)) ^ 2 := by
    refine (happ FU (KT - KU)).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hFU hCa) (by simpa only [Q] using hKTU)
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (KT - KU))
      (mul_nonneg hCa (sq_nonneg Fb))
  rw [heq]
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 (FT - FU) KT +
            ccOperatorFieldComp (I := I) (M := M) g 2 4 2 FU (KT - KU)) ≤
        x ^ 2 + y ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have hx : 2 * (Ca * (Fd * N) ^ 2 * (Bk R * Q ^ 2) ^ 2) =
        x ^ 2 := by
      simp only [x, mul_pow, hCsSq]
      ring
    have hy : 2 * (Ca * Fb ^ 2 *
        (Bd R * Q * (D3 + D2 + A * D2)) ^ 2) = y ^ 2 := by
      simp only [y, mul_pow, hCsSq]
      ring
    rw [← hx, ← hy]
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hterm1 (by norm_num))
      (mul_le_mul_of_nonneg_left hterm2 (by norm_num))
  refine hsum.trans ((sq_add_sq_le_sq_add_of_nonneg hx0 hy0).trans ?_)
  have hNle : N ≤ S := by
    simp only [S]
    calc
      N ≤ D2 + N := le_add_of_nonneg_left hD2
      _ ≤ D3 + (D2 + N) := le_add_of_nonneg_left hD3
      _ = D3 + D2 + N := by ring
  have hinner : D3 + D2 + A * D2 ≤ Q * S := by
    simp only [Q, S]
    calc
      D3 + D2 + A * D2 ≤ D3 + D2 + A * D2 +
          (N + A * D3 + A * N) :=
        le_add_of_nonneg_right
          (add_nonneg (add_nonneg hN (mul_nonneg hA hD3)) (mul_nonneg hA hN))
      _ = (1 + A) * (D3 + D2 + N) := by ring
  have hxle : x ≤ Cs * Fd * Bk R * Q ^ 2 * S := by
    calc
      x = (Cs * Fd * Bk R * Q ^ 2) * N := by
        simp only [x]
        ring
      _ ≤ (Cs * Fd * Bk R * Q ^ 2) * S :=
        mul_le_mul_of_nonneg_left hNle
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCs hFd) (hBk R hR)) (sq_nonneg Q))
      _ = Cs * Fd * Bk R * Q ^ 2 * S := by ring
  have hyle : y ≤ Cs * Fb * Bd R * Q ^ 2 * S := by
    calc
      y ≤ (Cs * Fb * Bd R * Q) * (Q * S) :=
        mul_le_mul_of_nonneg_left hinner
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCs hFb) (hBd R hR)) hQ)
      _ = Cs * Fb * Bd R * Q ^ 2 * S := by ring
  have hxy : x + y ≤ B R * Q ^ 2 * S := by
    calc
      x + y ≤ Cs * Fd * Bk R * Q ^ 2 * S +
          Cs * Fb * Bd R * Q ^ 2 * S := add_le_add hxle hyle
      _ = B R * Q ^ 2 * S := by
        simp only [B]
        ring
  simpa only [Q, S] using
    pow_le_pow_left₀ (add_nonneg hx0 hy0) hxy 2

private theorem exists_ricciConnectionDerivativeArm_thirdOrder_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U) ≤
        (B R * (1 + A ^ 2) * D3) ^ 2 := by
  obtain ⟨Kd, hKd, hdagB⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bd, hBd, hdagD⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_tame_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Be, hBe, hslotB⟩ :=
    RicciDeTurckLowOrder.full_slot_sobolev_two_bound (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bed, hBed, hslotD⟩ :=
    exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, happG⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Kr, hKr, hdecomposition⟩ :=
    exists_kernelContractionMonomialField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happA⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 2 2
  let Sd : ℝ := Real.sqrt Kd
  let Sg : ℝ := Real.sqrt (2 * Cg)
  let Su : ℝ := Real.sqrt (Cg * Kd)
  let Sm : ℝ := Real.sqrt (2 * Ca * Kr)
  have hSd : 0 ≤ Sd := Real.sqrt_nonneg _
  have hSg : 0 ≤ Sg := Real.sqrt_nonneg _
  have hSu : 0 ≤ Su := Real.sqrt_nonneg _
  have hSm : 0 ≤ Sm := Real.sqrt_nonneg _
  have hSdSq : Sd ^ 2 = Kd := by
    simpa only [Sd] using Real.sq_sqrt hKd
  have hSgSq : Sg ^ 2 = 2 * Cg := by
    simpa only [Sg] using Real.sq_sqrt (mul_nonneg (by norm_num) hCg)
  have hSuSq : Su ^ 2 = Cg * Kd := by
    simpa only [Su] using Real.sq_sqrt (mul_nonneg hCg hKd)
  have hSmSq : Sm ^ 2 = 2 * Ca * Kr := by
    simpa only [Sm] using
      Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hCa) hKr)
  let B : ℝ → ℝ := fun R =>
    4 * Sm * (Sg * (Bd R + Sd) * Be R + Su * Bed R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (by norm_num) hSm)
      (add_nonneg
        (mul_nonneg
          (mul_nonneg hSg (add_nonneg (hBd R hR) hSd))
          (hBe R hR))
        (mul_nonneg hSu (hBed R hR)))
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3
  let X : ℝ := A ^ 2
  let Ap : ℝ := A
  have hAp : 0 ≤ Ap := by simpa only [Ap] using hA
  have hApSq : Ap ^ 2 = X := by simp only [Ap, X]
  have hX : 0 ≤ X := by simp only [X]; exact sq_nonneg A
  have hT3i : covariantJetNormSq (I := I) (M := M) g 3 T ≤ Ap ^ 2 := by
    simpa only [Ap] using hT3
  have hU3i : covariantJetNormSq (I := I) (M := M) g 3 U ≤ Ap ^ 2 := by
    simpa only [Ap] using hU3
  have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) (T - U)).trans hTU3
  have hdagU0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        Kd * (1 + Ap ^ 2) :=
    hdagB gU U hU hUtie hδ_le hδ0 hδU
      |>.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hU3i) hKd)
  have hdagU :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (Sd * (1 + Ap)) ^ 2 := by
    refine hdagU0.trans ?_
    rw [mul_pow, hSdSq]
    apply mul_le_mul_of_nonneg_left _ hKd
    calc
      1 + Ap ^ 2 ≤ 1 + Ap ^ 2 + 2 * Ap :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) hAp)
      _ = (1 + Ap) ^ 2 := by ring
  have hdagD0 :=
    hdagD gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R Ap D3 D3 hR hAp hD3 hD3
      hT2 hU2 hT3i hU3i hTU2 hTU3
  have hdagDiff :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
            RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (Bd R * (2 + Ap) * D3) ^ 2 := by
    simpa only [
      show D3 + D3 + Ap * D3 = (2 + Ap) * D3 by ring,
      mul_assoc] using hdagD0
  have hgradT :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 T) ≤ Ap ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g T).trans hT3i
  have hgradU :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 U) ≤ Ap ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g U).trans hU3i
  have hgradDiff :
      covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 (T - U)) ≤ D3 ^ 2 :=
    (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g (T - U)).trans hTU3
  let GT : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT)
      (covGrad (I := I) (M := M) g 0 2 T)
  let GU : SmoothCcTensor g 0 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 0 3 4
      (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
      (covGrad (I := I) (M := M) g 0 2 U)
  let x : ℝ := Sg * Bd R * Ap * (2 + Ap) * D3
  let y : ℝ := Sg * Sd * (1 + Ap) * D3
  let z : ℝ := Su * (1 + Ap) * Ap
  have hx0 : 0 ≤ x :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hSg (hBd R hR)) hAp)
          (add_nonneg (by norm_num) hAp))
      hD3
  have hy0 : 0 ≤ y :=
    mul_nonneg (mul_nonneg (mul_nonneg hSg hSd) (add_nonneg zero_le_one hAp)) hD3
  have hz0 : 0 ≤ z :=
    mul_nonneg (mul_nonneg hSu (add_nonneg zero_le_one hAp)) hAp
  have hGcomb :
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
            RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 T) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 (T - U)) =
        GT - GU := by
    simp only [GT, GU]
    rw [operatorFieldComposition_sub_left, covGrad_sub, operatorFieldComposition_sub_right]
    module
  have hGterm1 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
              RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
            (covGrad (I := I) (M := M) g 0 2 T)) ≤
        Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2 := by
    refine (happG _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hdagDiff hCg) hgradT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (covGrad (I := I) (M := M) g 0 2 T))
      (mul_nonneg hCg (sq_nonneg _))
  have hGterm2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
            (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
            (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
        Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2 := by
    refine (happG _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hdagU hCg) hgradDiff
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
        (covGrad (I := I) (M := M) g 0 2 (T - U)))
      (mul_nonneg hCg (sq_nonneg _))
  have hxSq :
      2 * (Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2) = x ^ 2 := by
    simp only [x, mul_pow, hSgSq]
    ring
  have hySq :
      2 * (Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2) = y ^ 2 := by
    simp only [y, mul_pow, hSgSq, hSdSq]
    ring
  have hGdiff : covariantJetNormSq (I := I) (M := M) g 2 (GT - GU) ≤
      (x + y) ^ 2 := by
    rw [← hGcomb]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
                (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT -
                  RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
                (covGrad (I := I) (M := M) g 0 2 T)) +
            covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 0 3 4
                (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
                (covGrad (I := I) (M := M) g 0 2 (T - U)))) ≤
          2 * (Cg * (Bd R * (2 + Ap) * D3) ^ 2 * Ap ^ 2 +
            Cg * (Sd * (1 + Ap)) ^ 2 * D3 ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hGterm1 hGterm2) (by norm_num)
      _ = x ^ 2 + y ^ 2 := by rw [← hxSq, ← hySq]; ring
      _ ≤ (x + y) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hx0 hy0
  have hGU : covariantJetNormSq (I := I) (M := M) g 2 GU ≤ z ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 GU ≤
          Cg * covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g 0 2 U) := by
        simpa only [GU] using happG
          (RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 U)
      _ ≤ Cg * (Sd * (1 + Ap)) ^ 2 * Ap ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hdagU hCg) hgradU
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
            (covGrad (I := I) (M := M) g 0 2 U))
          (mul_nonneg hCg (sq_nonneg _))
      _ = z ^ 2 := by
        simp only [z, mul_pow, hSdSq, hSuSq]
        ring
  let ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT)
  let EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU)
  have hET : covariantJetNormSq (I := I) (M := M) g 2 ET ≤ (Be R) ^ 2 := by
    simpa only [ET] using
      hslotB gT T hT hTtie hδ_le hδ0 hδT R hR hT2
  have hEdiff : covariantJetNormSq (I := I) (M := M) g 2 (ET - EU) ≤
      (Bed R * D3) ^ 2 := by
    simpa only [ET, EU] using
      hslotD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R D3 hR hD3 hT2 hU2 hTU2
  let u : ℝ := Sm * (x + y) * Be R
  let v : ℝ := Sm * z * Bed R * D3
  have hu0 : 0 ≤ u :=
    mul_nonneg (mul_nonneg hSm (add_nonneg hx0 hy0)) (hBe R hR)
  have hv0 : 0 ≤ v :=
    mul_nonneg (mul_nonneg (mul_nonneg hSm hz0) (hBed R hR)) hD3
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ) ≤
        (u + v) ^ 2 := by
    intro σ
    have hfT :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GT σ) ET := by rfl
    have hfU :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GU σ) EU := by rfl
    have hsplit :
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU σ =
          ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g (GT - GU) σ) ET +
            ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g GU σ) (ET - EU) := by
      rw [hfT, hfU, kernelContractionMonomialField_sub]
      exact operatorFieldComposition_sub (I := I) (M := M) g 2 2 2 _ _ _ _
    have hrDiff :
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g (GT - GU) σ) ≤
          Kr * (x + y) ^ 2 :=
      (hdecomposition (GT - GU) σ).trans
        (mul_le_mul_of_nonneg_left hGdiff hKr)
    have hrU :
        covariantJetNormSq (I := I) (M := M) g 2
            (decompositionKernelContractionMonomialField
              (I := I) (M := M) g g GU σ) ≤ Kr * z ^ 2 :=
      (hdecomposition GU σ).trans (mul_le_mul_of_nonneg_left hGU hKr)
    have hterm1 :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g (GT - GU) σ) ET) ≤
          Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2 := by
      refine (happA _ _).trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hrDiff hCa) hET
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g ET)
        (mul_nonneg hCa (mul_nonneg hKr (sq_nonneg _)))
    have hterm2 :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
              (decompositionKernelContractionMonomialField
                (I := I) (M := M) g g GU σ) (ET - EU)) ≤
          Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2 := by
      refine (happA _ _).trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hrU hCa) hEdiff
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (ET - EU))
        (mul_nonneg hCa (mul_nonneg hKr (sq_nonneg z)))
    have huSq :
        2 * (Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2) = u ^ 2 := by
      simp only [u, mul_pow, hSmSq]
      ring
    have hvSq :
        2 * (Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2) = v ^ 2 := by
      simp only [v, mul_pow, hSmSq]
      ring
    rw [hsplit]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
                (decompositionKernelContractionMonomialField
                  (I := I) (M := M) g g (GT - GU) σ) ET) +
            covariantJetNormSq (I := I) (M := M) g 2
              (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
                (decompositionKernelContractionMonomialField
                  (I := I) (M := M) g g GU σ) (ET - EU))) ≤
          2 * (Ca * (Kr * (x + y) ^ 2) * (Be R) ^ 2 +
            Ca * (Kr * z ^ 2) * (Bed R * D3) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ = u ^ 2 + v ^ 2 := by rw [← huSq, ← hvSq]; ring
      _ ≤ (u + v) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hu0 hv0
  have hDAT :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T =
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by rfl
  have hDAU :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U =
        RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by rfl
  have hsplit :
      RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U =
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) -
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
              RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap) := by
    rw [hDAT, hDAU]
    abel
  have hDAraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gU U) ≤
        (2 * (u + v)) ^ 2 := by
    rw [hsplit]
    refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 _ _).trans ?_
    have hpa := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
    have hpb := hmono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
                RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) +
            covariantJetNormSq (I := I) (M := M) g 2
              (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gT GT
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
                RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeContractionMonomial (I := I) (M := M) g gU GU
                  RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)) ≤
          2 * ((u + v) ^ 2 + (u + v) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hpa hpb) (by norm_num)
      _ = (2 * (u + v)) ^ 2 := by ring
  have hApLe : Ap ≤ (1 + X) / 2 := by
    rw [← hApSq]
    nlinarith only [sq_nonneg (Ap - 1)]
  have hfac1 : Ap * (2 + Ap) ≤ 2 * (1 + X) := by
    rw [show Ap * (2 + Ap) = 2 * Ap + X by rw [← hApSq]; ring]
    linarith only [hApLe]
  have hfac2 : 1 + Ap ≤ 2 * (1 + X) := by linarith only [hApLe, hX]
  have hfac3 : (1 + Ap) * Ap ≤ 2 * (1 + X) := by
    rw [show (1 + Ap) * Ap = Ap + X by rw [← hApSq]; ring]
    linarith only [hApLe, hX]
  have hxlin : x ≤ 2 * Sg * Bd R * (1 + X) * D3 := by
    calc
      x = Sg * Bd R * (Ap * (2 + Ap)) * D3 := by simp only [x]; ring
      _ ≤ Sg * Bd R * (2 * (1 + X)) * D3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac1
            (mul_nonneg hSg (hBd R hR))) hD3
      _ = 2 * Sg * Bd R * (1 + X) * D3 := by ring
  have hylin : y ≤ 2 * Sg * Sd * (1 + X) * D3 := by
    calc
      y ≤ Sg * Sd * (2 * (1 + X)) * D3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac2 (mul_nonneg hSg hSd)) hD3
      _ = 2 * Sg * Sd * (1 + X) * D3 := by ring
  have hzlin : z ≤ 2 * Su * (1 + X) := by
    calc
      z = Su * ((1 + Ap) * Ap) := by simp only [z]; ring
      _ ≤ Su * (2 * (1 + X)) := mul_le_mul_of_nonneg_left hfac3 hSu
      _ = 2 * Su * (1 + X) := by ring
  have hxy : x + y ≤
      2 * Sg * (Bd R + Sd) * (1 + X) * D3 := by
    calc
      x + y ≤ 2 * Sg * Bd R * (1 + X) * D3 +
          2 * Sg * Sd * (1 + X) * D3 := add_le_add hxlin hylin
      _ = 2 * Sg * (Bd R + Sd) * (1 + X) * D3 := by ring
  have huLin : u ≤
      2 * Sm * (Sg * (Bd R + Sd) * Be R) * (1 + X) * D3 := by
    calc
      u ≤ Sm * (2 * Sg * (Bd R + Sd) * (1 + X) * D3) * Be R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxy hSm) (hBe R hR)
      _ = 2 * Sm * (Sg * (Bd R + Sd) * Be R) *
          (1 + X) * D3 := by ring
  have hvLin : v ≤
      2 * Sm * (Su * Bed R) * (1 + X) * D3 := by
    calc
      v ≤ Sm * (2 * Su * (1 + X)) * Bed R * D3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hzlin hSm) (hBed R hR)) hD3
      _ = 2 * Sm * (Su * Bed R) * (1 + X) * D3 := by ring
  have huv : u + v ≤
      2 * Sm * (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
        (1 + X) * D3 := by
    calc
      u + v ≤
          2 * Sm * (Sg * (Bd R + Sd) * Be R) * (1 + X) * D3 +
            2 * Sm * (Su * Bed R) * (1 + X) * D3 :=
        add_le_add huLin hvLin
      _ = 2 * Sm * (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
          (1 + X) * D3 := by ring
  have hscale : 2 * (u + v) ≤ B R * (1 + X) * D3 := by
    calc
      2 * (u + v) ≤
          2 * (2 * Sm *
            (Sg * (Bd R + Sd) * Be R + Su * Bed R) *
            (1 + X) * D3) :=
        mul_le_mul_of_nonneg_left huv (by norm_num)
      _ = B R * (1 + X) * D3 := by
        simp only [B]
        ring
  simpa only [X] using hDAraw.trans
    (pow_le_pow_left₀
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg hu0 hv0))
      hscale 2)

theorem RicciDeTurckLowOrder.exists_symmetricRicciTerm_covariantJetNormSq_difference_bound
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
          (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) (s • T) -
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) (s • U)) ≤
        (B R * (1 + A ^ 2) * (D3 + D2 + N)) ^ 2 := by
  obtain ⟨Ks, hKs, hsymm⟩ :=
    exists_ccInputSlotSymm_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨ρA, BA, hρA, hBA, haa⟩ :=
    exists_ricciQuadraticConnectionArm_thirdOrder_tame_difference_bound (I := I) (M := M) hDim g
  obtain ⟨BD, hBD, hda⟩ :=
    exists_ricciConnectionDerivativeArm_thirdOrder_tame_difference_bound (I := I) (M := M) hDim g
  let Cs : ℝ := Real.sqrt (2 * Ks)
  let B : ℝ → ℝ := fun R => Cs * (2 * BA R + BD R)
  have hCs : 0 ≤ Cs := Real.sqrt_nonneg _
  have hCsSq : Cs ^ 2 = 2 * Ks := by
    simpa only [Cs] using
      Real.sq_sqrt (mul_nonneg (by norm_num) hKs)
  refine ⟨ρA, B, hρA, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hCs
      (add_nonneg (mul_nonneg (by norm_num) (hBA R hR)) (hBD R hR))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  set P : SmoothCcTensor g 0 2 := s • T
  set Q : SmoothCcTensor g 0 2 := s • U
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hs.1 hs.2 2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [Q, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2),
        abs_of_nonneg hs.1]
      ring
    simpa only [Q, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [show Q = s • U by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [show P = s • T by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [show Q = s • U by rfl, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      simp only [P, Q, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      simp only [P, Q, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρA := by
    rw [show P = s • T by rfl, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρA := by
    rw [show Q = s • U by rfl, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn)
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      simp only [P, Q, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  let S : ℝ := D3 + D2 + N
  let SA : ℝ := BA R * (1 + A) ^ 2 * S
  let SD : ℝ := BD R * (1 + A ^ 2) * D3
  have hS : 0 ≤ S := by
    simp only [S]
    exact add_nonneg (add_nonneg hD3 hD2) hN
  have hSA0 : 0 ≤ SA :=
    mul_nonneg (mul_nonneg (hBA R hR) (sq_nonneg _)) hS
  have hSD0 : 0 ≤ SD :=
    mul_nonneg
      (mul_nonneg (hBD R hR) (add_nonneg (by norm_num) (sq_nonneg A))) hD3
  have hAA : covariantJetNormSq (I := I) (M := M) g 2
      (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
        ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) ≤ SA ^ 2 := by
    simpa only [SA, S] using
      haa gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ R A D2 D3 N
        hR hA hD2 hD3 hN hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPn hQn hPQn
  have hDA : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
        RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) ≤ SD ^ 2 := by
    simpa only [SD] using
      hda gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ R A D3 hR hA hD3
        hP2 hQ2 hP3 hQ3 hPQ3
  have hlowT :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P =
        ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT +
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P := rfl
  have hlowU :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU +
          RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q := rfl
  have hlow :
      RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q) := by
    rw [hlowT, hlowU]
    abel
  have hgood :
      RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P -
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q =
        ccInputSlotSymm (I := I) (M := M) g
          ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) := by
    change ccInputSlotSymm (I := I) (M := M) g
          (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmT P) -
        ccInputSlotSymm (I := I) (M := M) g
          (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gmU Q) = _
    rw [ccInputSlotSymm_sub, hlow]
  have hfac : (1 + A) ^ 2 ≤ 2 * (1 + A ^ 2) := by
    nlinarith only [sq_nonneg (A - 1)]
  have hD3S : D3 ≤ S := by
    simp only [S]
    calc
      D3 ≤ D3 + (D2 + N) := le_add_of_nonneg_right (add_nonneg hD2 hN)
      _ = D3 + D2 + N := by ring
  let W : ℝ := (2 * BA R + BD R) * (1 + A ^ 2) * S
  have hSAle : SA ≤ 2 * BA R * (1 + A ^ 2) * S := by
    simp only [SA]
    calc
      BA R * (1 + A) ^ 2 * S ≤ BA R * (2 * (1 + A ^ 2)) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac (hBA R hR)) hS
      _ = 2 * BA R * (1 + A ^ 2) * S := by ring
  have hSDle : SD ≤ BD R * (1 + A ^ 2) * S := by
    simp only [SD]
    exact mul_le_mul_of_nonneg_left hD3S
      (mul_nonneg (hBD R hR) (add_nonneg (by norm_num) (sq_nonneg A)))
  have hsum : SA + SD ≤ W := by
    calc
      SA + SD ≤ 2 * BA R * (1 + A ^ 2) * S +
          BD R * (1 + A ^ 2) * S := add_le_add hSAle hSDle
      _ = W := by simp only [W]; ring
  have hW0 : 0 ≤ W := by
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (hBA R hR)) (hBD R hR))
        (add_nonneg (by norm_num) (sq_nonneg A))) hS
  rw [hgood]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccInputSlotSymm (I := I) (M := M) g
          ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
              ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
            (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
              RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q))) ≤
      Ks * covariantJetNormSq (I := I) (M := M) g 2
        ((ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmT -
            ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gmU) +
          (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmT P -
            RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gmU Q)) := hsymm _
    _ ≤ Ks * (2 * (SA ^ 2 + SD ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hKs
      exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans
        (mul_le_mul_of_nonneg_left (add_le_add hAA hDA) (by norm_num))
    _ ≤ Ks * (2 * (SA + SD) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sq_add_sq_le_sq_add_of_nonneg hSA0 hSD0) (by norm_num)) hKs
    _ ≤ Ks * (2 * W ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg hSA0 hSD0) hsum 2) (by norm_num)) hKs
    _ = (Cs * W) ^ 2 := by
      conv_rhs => rw [mul_pow, hCsSq]
      ring
    _ = (B R * (1 + A ^ 2) * (D3 + D2 + N)) ^ 2 := by
      simp only [B, W, S]
      apply congrArg (fun x : ℝ => x ^ 2)
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
