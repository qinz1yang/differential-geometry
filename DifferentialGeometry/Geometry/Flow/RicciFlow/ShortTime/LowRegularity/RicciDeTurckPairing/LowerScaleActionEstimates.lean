import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderPathIntegralBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.ZeroStateForcing

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left ccTensorToHs ccTensorToHs_coeff metricPrincipalDefectCurvCoeff)
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
  (ricciDeTurckRemainderFirstOrderPathIntegral)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

noncomputable def pathIntegralLowerScaleActionCoefficients
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowerScaleActionCoefficients g where
  zeroOrderCoefficient := affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
      g T hT hδ_lt hδ hδZ +
    metricPrincipalDefectCurvCoeff (I := I) g g g
  firstOrderCoefficient := lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ +
    ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
      g g T 0 hδ_lt hδ hδ_lt hδZ
  secondOrderCoefficient := (lowerScaleActionCoefficients (I := I) (M := M)
    g g T hδ_lt hδ hδZ).secondOrderCoefficient

theorem exists_pathIntegralLowerScaleZeroCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let A := pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient ≤ (B R) ^ 2 := by
  obtain ⟨ρ, Bz, hρ, hBz, hz⟩ :=
    exists_affineLowOrderZeroCoefficientPathIntegral_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricPrincipalDefectCurvCoeff (I := I) g g g)
  let L : ℝ → ℝ := fun R => 2 * (Bz R ^ 2 + J)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg (Bz R)) hJ)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn
  dsimp only
  have hzero := hz T hT hδ_le hδ0 hδT hδZ R hR hT2 hTn
  rw [pathIntegralLowerScaleActionCoefficients]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) +
        covariantJetNormSq (I := I) (M := M) g 2
          (metricPrincipalDefectCurvCoeff (I := I) g g g)) ≤
      2 * (Bz R ^ 2 + J) :=
        mul_le_mul_of_nonneg_left (add_le_add hzero le_rfl) (by norm_num)
    _ = L R := by rfl
    _ = B R ^ 2 := by
      simpa only [B] using (Real.sq_sqrt (hL R hR)).symm

theorem exists_pathIntegralLowerScaleOneCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      covariantJetNormSq (I := I) (M := M) g 2 F.firstOrderCoefficient ≤
        (B R * (1 + A ^ 2) ^ 3) ^ 2 := by
  obtain ⟨ρ, Bl, hρ, hBl, hnew⟩ :=
    exists_lowOrderFirstDerivativePathIntegral_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨K, hK, hold⟩ := exists_lowerScaleAction_coefficient_bound (I := I) (M := M) hDim g
  let L : ℝ → ℝ := fun R => 2 * (2 * Bl R ^ 2 + K)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg (Bl R))) hK)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  let X : ℝ := 1 + A ^ 2
  have hX0 : 0 ≤ X := add_nonneg (by norm_num) (sq_nonneg A)
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith [sq_nonneg A]
  have hX16 : X ^ 1 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by omega)
  have hXpow : X ≤ X ^ 6 := by simpa only [pow_one] using hX16
  have hlin : (1 + A) ^ 2 ≤ 2 * X ^ 6 := by
    calc
      (1 + A) ^ 2 ≤ 2 * X := by
        simp only [X]
        nlinarith [sq_nonneg (A - 1)]
      _ ≤ 2 * X ^ 6 := mul_le_mul_of_nonneg_left hXpow (by norm_num)
  have hn := hnew T hT hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3 hTn
  have hn' : covariantJetNormSq (I := I) (M := M) g 2
      (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
      2 * Bl R ^ 2 * X ^ 6 := by
    calc
      _ ≤ (Bl R * (1 + A)) ^ 2 := hn
      _ = Bl R ^ 2 * (1 + A) ^ 2 := by ring
      _ ≤ Bl R ^ 2 * (2 * X ^ 6) :=
        mul_le_mul_of_nonneg_left hlin (sq_nonneg (Bl R))
      _ = 2 * Bl R ^ 2 * X ^ 6 := by ring
  have holdSum := hold T hT hδ_le hδ0 hδT hδZ
  dsimp only at holdSum
  let F₀ : LowerScaleActionCoefficients g := lowerScaleActionCoefficients (I := I) (M := M)
    g g T (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
  have holdC1 : covariantJetNormSq (I := I) (M := M) g 2 F₀.firstOrderCoefficient ≤
      K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 := by
    have hC0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F₀.zeroOrderCoefficient
    simpa only [F₀] using
      (show covariantJetNormSq (I := I) (M := M) g 2 F₀.firstOrderCoefficient ≤
          K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 by
        nlinarith [holdSum])
  have hstate :
      (1 + covariantJetNormSq (I := I) (M := M) g 3 T) ^ 6 ≤ X ^ 6 := by
    exact pow_le_pow_left₀
      (by linarith [covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T])
      (by simpa only [X] using add_le_add le_rfl hT3) 6
  have holdC1' : covariantJetNormSq (I := I) (M := M) g 2 F₀.firstOrderCoefficient ≤
      K * X ^ 6 :=
    holdC1.trans (mul_le_mul_of_nonneg_left hstate hK)
  have holdPath : covariantJetNormSq (I := I) (M := M) g 2
      (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
        g g T 0 (lt_of_le_of_lt hδ_le (by norm_num)) hδT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδZ) ≤
      K * X ^ 6 := by
    simpa only [F₀, lowerScaleActionCoefficients] using holdC1'
  rw [pathIntegralLowerScaleActionCoefficients]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) +
        covariantJetNormSq (I := I) (M := M) g 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
            g g T 0 (lt_of_le_of_lt hδ_le (by norm_num)) hδT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)) ≤
      2 * (2 * Bl R ^ 2 * X ^ 6 + K * X ^ 6) :=
        mul_le_mul_of_nonneg_left (add_le_add hn' holdPath) (by norm_num)
    _ = L R * X ^ 6 := by simp only [L]; ring
    _ = (B R * X ^ 3) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      rw [mul_pow, hBR]
      ring

theorem exists_pathIntegralLowerScaleCoefficients_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      covariantJetNormSq (I := I) (M := M) g 2 F.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 F.firstOrderCoefficient ≤
        (B R * (1 + A ^ 2) ^ 3) ^ 2 := by
  obtain ⟨ρ0, B0, hρ0, hB0, hC0⟩ :=
    exists_pathIntegralLowerScaleZeroCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ1, B1, hρ1, hB1, hC1⟩ :=
    exists_pathIntegralLowerScaleOneCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ0 ρ1
  let L : ℝ → ℝ := fun R => B0 R ^ 2 + B1 R ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρ0 hρ1
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact add_nonneg (sq_nonneg (B0 R)) (sq_nonneg (B1 R))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  have h0 := hC0 T hT hδ_le hδ0 hδT hδZ R hR hT2
    (hTn.trans (min_le_left _ _))
  have h1 := hC1 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
    (hTn.trans (min_le_right _ _))
  let X : ℝ := 1 + A ^ 2
  have hX1 : 1 ≤ X := by simp only [X]; nlinarith [sq_nonneg A]
  have hX16 : X ^ 1 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by omega)
  have hXpow : X ≤ X ^ 6 := by simpa only [pow_one] using hX16
  have hX6 : 1 ≤ X ^ 6 := hX1.trans hXpow
  have h0' : covariantJetNormSq (I := I) (M := M) g 2
      (pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).zeroOrderCoefficient ≤
      B0 R ^ 2 * X ^ 6 := by
    calc
      _ ≤ B0 R ^ 2 := h0
      _ = B0 R ^ 2 * 1 := by ring
      _ ≤ B0 R ^ 2 * X ^ 6 :=
        mul_le_mul_of_nonneg_left hX6 (sq_nonneg (B0 R))
  calc
    covariantJetNormSq (I := I) (M := M) g 2
          (pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).zeroOrderCoefficient +
        covariantJetNormSq (I := I) (M := M) g 2
          (pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).firstOrderCoefficient ≤
      B0 R ^ 2 * X ^ 6 + (B1 R * X ^ 3) ^ 2 := add_le_add h0' h1
    _ = L R * X ^ 6 := by simp only [L]; ring
    _ = (B R * X ^ 3) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      rw [mul_pow, hBR]
      ring

theorem exists_pathIntegralLowerScaleFirstOrderAction_crossOrder_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      let F := pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      (∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (F.firstOrderAction (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            covariantJetNormSq (I := I) (M := M) g 3 W) ∧
      ∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 1
            (F.firstOrderAction (I := I) (M := M) W) ≤
          (B R * (1 + A ^ 2) ^ 3) ^ 2 *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨ρ, Bc, hρ, hBc, hcoeff⟩ :=
    exists_pathIntegralLowerScaleCoefficients_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhigh⟩ := exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ := exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let C : ℝ := Ch + Cl
  let B : ℝ → ℝ := fun R => C * Bc R
  have hC : 0 ≤ C := add_nonneg hCh hCl
  refine ⟨ρ, B, hρ, fun R hR => mul_nonneg hC (hBc R hR), ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  dsimp only
  let F := pathIntegralLowerScaleActionCoefficients (I := I) (M := M) g T hT
    (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
  let X : ℝ := 1 + A ^ 2
  let Q : ℝ := Bc R * X ^ 3
  have hX : 0 ≤ X := add_nonneg (by norm_num) (sq_nonneg A)
  have hQ : 0 ≤ Q := mul_nonneg (hBc R hR) (pow_nonneg hX 3)
  have hcoef : covariantJetNormSq (I := I) (M := M) g 2 F.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 F.firstOrderCoefficient ≤ Q ^ 2 := by
    simpa only [F, Q, X] using
      hcoeff T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  constructor
  · intro W
    let D : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hJW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq : D ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hhigh F W Q D hQ hD hcoef (by rw [hDsq])
    have hlead : Ch * Q * D ≤ C * Q * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCl) hQ) hD
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (F.firstOrderAction (I := I) (M := M) W) ≤ (Ch * Q * D) ^ 2 := hraw
      _ ≤ (C * Q * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCh hQ) hD) hlead 2
      _ = (B R * X ^ 3) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show C * Q * D = B R * X ^ 3 * D by
          simp only [B, Q]; ring, mul_pow, hDsq]
  · intro W
    let D : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hJW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq : D ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hJW
    have hraw := hlow F W Q D hQ hD hcoef (by rw [hDsq])
    have hlead : Cl * Q * D ≤ C * Q * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCh) hQ) hD
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (F.firstOrderAction (I := I) (M := M) W) ≤ (Cl * Q * D) ^ 2 := hraw
      _ ≤ (C * Q * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCl hQ) hD) hlead 2
      _ = (B R * X ^ 3) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show C * Q * D = B R * X ^ 3 * D by
          simp only [B, Q]; ring, mul_pow, hDsq]

noncomputable def affineLowerScaleActionCoefficients
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowerScaleActionCoefficients g where
  zeroOrderCoefficient := affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
      g T hT hδ_lt hδ hδZ +
    metricPrincipalDefectCurvCoeff (I := I) g g g
  firstOrderCoefficient := lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ
  secondOrderCoefficient := 0

theorem affineLowerScaleActionCoefficients_apply_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lowerScaleActionCoefficients (I := I) (M := M)
          g g T hδ_lt hδ hδZ).zeroOrderCoefficient T =
      (affineLowerScaleActionCoefficients (I := I) (M := M)
        g T hT hδ_lt hδ hδZ).firstOrderAction (I := I) (M := M) T := by
  rw [RicciDeTurckLowOrder.zeroOrderCoefficient_eq (I := I) (M := M)
    g g T hδ_lt hδ hδZ]
  rw [LowerScaleActionCoefficients.firstOrderAction]
  simp only [affineLowerScaleActionCoefficients, operatorFieldApplication_add_left]
  have hself := lowerScalePathIntegral_apply_affine_decomposition (I := I) (M := M) g T hT hδ_lt hδ hδZ
  rw [hself]
  abel

theorem exists_affineLowerScaleActionCoefficients_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 Ca : ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ Ca ∧
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
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := affineLowerScaleActionCoefficients (I := I) (M := M) g T hT
        (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ
      let AU := affineLowerScaleActionCoefficients (I := I) (M := M) g U hU
        (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ
      let Q0 := B0 * (1 + R) * (D2 + N)
      let Q1 := B1 R * (1 + A) * (D3 + D2 + A * D2 + N)
      ‖AT.firstOrderActionThirdToSecondOrder (I := I) (M := M) - AU.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
          Ca * Real.sqrt (Q0 ^ 2 + Q1 ^ 2) ∧
        ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          Ca * Real.sqrt (Q0 ^ 2 + Q1 ^ 2) := by
  obtain ⟨ρ0, B0, hρ0, hB0, hzero⟩ :=
    exists_affineLowOrderZeroCoefficientPathIntegral_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρ1, B1, hρ1, hB1, hone⟩ :=
    exists_lowOrderFirstDerivativePathIntegral_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, hact⟩ := exists_firstOrderAction_spectralSobolev_difference_bounds (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ0 ρ1
  refine ⟨ρ, B0, Ca, B1, lt_min hρ0 hρ1, hB0, hCa, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  dsimp only
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let AT : LowerScaleActionCoefficients g :=
    affineLowerScaleActionCoefficients (I := I) (M := M) g T hT hδ_lt hδT hδZ
  let AU : LowerScaleActionCoefficients g :=
    affineLowerScaleActionCoefficients (I := I) (M := M) g U hU hδ_lt hδU hδZ
  let Q0 : ℝ := B0 * (1 + R) * (D2 + N)
  let Q1 : ℝ := B1 R * (1 + A) * (D3 + D2 + A * D2 + N)
  let Q : ℝ := Q0 ^ 2 + Q1 ^ 2
  let Qt : ℝ := Real.sqrt Q
  have hM0 := hzero T U hT hU hδ_le hδT hδU hδZ
    R D2 N hR hD2 hN hT2 hU2 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hone T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hQ0 : 0 ≤ Q0 :=
    mul_nonneg (mul_nonneg hB0 (add_nonneg (by norm_num) hR))
      (add_nonneg hD2 hN)
  have hQ1 : 0 ≤ Q1 :=
    mul_nonneg (mul_nonneg (hB1 R hR) (add_nonneg (by norm_num) hA))
      (add_nonneg (add_nonneg (add_nonneg hD3 hD2)
        (mul_nonneg hA hD2)) hN)
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg Q0) (sq_nonneg Q1)
  have hQt : 0 ≤ Qt := Real.sqrt_nonneg _
  have hC0eq : AT.zeroOrderCoefficient - AU.zeroOrderCoefficient =
      affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT hδ_lt hδT hδZ -
        affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g U hU hδ_lt hδU hδZ := by
    simp only [AT, AU, affineLowerScaleActionCoefficients]
    module
  have hj0 : covariantJetNormSq (I := I) (M := M) g 2 (AT.zeroOrderCoefficient - AU.zeroOrderCoefficient) ≤
      Q0 ^ 2 := by
    rw [hC0eq]
    simpa only [Q0] using hM0
  have hj1 : covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) ≤
      Q1 ^ 2 := by
    simpa only [AT, AU, affineLowerScaleActionCoefficients, Q1] using hM1
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 (AT.zeroOrderCoefficient - AU.zeroOrderCoefficient) +
          covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) ≤
        Qt ^ 2 := by
    calc
      _ ≤ Q0 ^ 2 + Q1 ^ 2 := add_le_add hj0 hj1
      _ = Qt ^ 2 := by
        change Q = Real.sqrt Q ^ 2
        exact (Real.sq_sqrt hQ).symm
  have hop := hact AT AU Qt hQt hcoeff
  simpa only [AT, AU, Qt, Q, Q0, Q1] using hop

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gFibreOpBound_zero
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem tensorHsInclusion_ccTensorToHs_two_three
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine tensorHs.ext ?_
  funext i
  simp only [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

theorem sqrt_mul_sq_of_nonneg
    (q d : ℝ) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    Real.sqrt (q * d ^ 2) = Real.sqrt q * d := by
  rw [Real.sqrt_mul hq, Real.sqrt_sq hd]

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
