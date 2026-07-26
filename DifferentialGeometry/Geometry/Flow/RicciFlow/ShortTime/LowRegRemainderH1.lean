import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegForcingH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegPathLower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegPathSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm

/-!
# Low-regularity Ricci--DeTurck remainder estimates

This file subtracts the fixed background connection Laplacian from the
low-regularity Ricci--DeTurck forcing estimates. The zero-order estimate is
closed at `H2 -> H0`, and `rem_h1_of_bounds` gives the conditional mixed
`H3 -> H1` assembly.  The remaining frontier is unconditional integral-product
control of the concrete lower path coefficients.
-/

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- After subtracting the fixed background connection Laplacian, the
zero-order Ricci--DeTurck remainder difference is uniformly controlled by the
spectral `H2` metric difference. -/
theorem rem_h0_lip {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₁ k₂ : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        ((deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
            deTurckRHSSectionBg (I := I) gBase (gSeq k₂)) -
          rawTensorConnLapSmooth (I := I) gBase 0 2
            (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
              metricCcTensor (I := I) (M := M) gBase (gSeq k₂)))‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ)
          (metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
            metricCcTensor (I := I) (M := M) gBase (gSeq k₂))‖ := by
  obtain ⟨Crhs, hCrhs, hrhs⟩ := rhs_h0_lip (I := I) (M := M) gBase gSeq D hD
  refine ⟨Crhs + 1, add_nonneg hCrhs zero_le_one, ?_⟩
  intro k₁ k₂
  let U : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase (gSeq k₁) -
      metricCcTensor (I := I) (M := M) gBase (gSeq k₂)
  let S : SmoothCcTensor gBase 0 2 :=
    deTurckRHSSectionBg (I := I) gBase (gSeq k₁) -
      deTurckRHSSectionBg (I := I) gBase (gSeq k₂)
  have hrhs' : ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ ≤
      Crhs * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by
    simpa only [S, U] using hrhs k₁ k₂
  have hlap := smoothCcToTensorHs_rawTensorConnLapSmooth_le
    (I := I) (M := M) gBase (0 : ℝ) U
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
      (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
    ‖ccTensorToHs (I := I) (M := M) gBase 2 ((0 : ℝ) + 2) U‖ at hlap
  have hlap' : ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by
    have h02 : (0 : ℝ) + 2 = 2 := by norm_num
    rw [h02] at hlap
    exact hlap
  change ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
      (S - rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ ≤
    (Crhs + 1) * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖
  have hsub : ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
        (S - rawTensorConnLapSmooth (I := I) gBase 0 2 U) =
      ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S -
        ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U) := by
    have hneg : ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (-rawTensorConnLapSmooth (I := I) gBase 0 2 U) =
        -ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U) := by
      rw [show -rawTensorConnLapSmooth (I := I) gBase 0 2 U =
          (-1 : ℝ) • rawTensorConnLapSmooth (I := I) gBase 0 2 U by simp,
        ccTensorToHs_smul]
      simp
    rw [sub_eq_add_neg, ccTensorToHs_add, hneg]
    rfl
  rw [hsub]
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S -
        ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖
        ≤ ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ) S‖ +
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (0 : ℝ)
            (rawTensorConnLapSmooth (I := I) gBase 0 2 U)‖ := norm_sub_le _ _
    _ ≤ Crhs * ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ +
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ :=
      add_le_add hrhs' hlap'
    _ = (Crhs + 1) *
          ‖ccTensorToHs (I := I) (M := M) gBase 2 (2 : ℝ) U‖ := by ring

-- `unusedVariables` only inspects syntactic dependency in the conclusion and
-- therefore flags the sufficient bound hypotheses below, although the proof
-- consumes each of them to establish that conclusion.
set_option linter.unusedVariables false in
/-- In dimension three, the exact Ricci--DeTurck path decomposition gives the
mixed `H3 -> H1` remainder estimate once the concrete zero- and one-order path
coefficients have uniform low-regularity bounds.  The only `H3` coefficient is
the spectral `H2` ball radius. -/
theorem rem_h1_of_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ Ctop Clow Ccoef : ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧ 0 ≤ Clow ∧ 0 ≤ Ccoef ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        {R : ℝ} (hR : 0 ≤ R) (hRρ : R ≤ ρ)
        (hT : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R)
        (hT' : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R)
        (B₀ B₀' B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₀' : 0 ≤ B₀') (hB₁ : 0 ≤ B₁)
        (hΦ₀ : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ_lt hδ hδ'_lt hδ').toSection x) ≤ B₀ ^ 2)
        (hΦ₀' : ‖covGrad (I := I) (M := M) g₀ 2 2
          (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ')‖ ≤ B₀')
        (hΦ₁ : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ_lt hδ hδ'_lt hδ').toSection x) ≤ B₁ ^ 2)
        (hΦ₁' : (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 j
            (rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ_lt hδ hδ'_lt hδ')‖ ^ 2) ≤ B₁ ^ 2),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          ((realizedRHSArm (I := I) g₀ g_bg T
                hδ_lt hδ -
              realizedRHSArm (I := I) g₀ g_bg T'
                hδ'_lt hδ') -
            rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤
          Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) (T - T')‖ +
            (Clow + Ccoef * (B₀ + B₀' + B₁)) *
              ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, Clow, hρ, hCtop, hClow, htop⟩ :=
    top_path_ball_h1 (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Ccoef, hCcoef, hlower⟩ := lower_coeff_h1 (I := I) (M := M) hDim g₀
  refine ⟨ρ, Ctop, Clow, Ccoef, hρ, hCtop, hClow, hCcoef, ?_⟩
  intro T T' hTsymm hT'symm δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT'
    B₀ B₀' B₁ hB₀ hB₀' hB₁ hΦ₀ hΦ₀' hΦ₁ hΦ₁'
  let U : SmoothCcTensor g₀ 0 2 := T - T'
  let Φ₀ : SmoothCcTensor g₀ 2 2 :=
    rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  let Φ₁ : SmoothCcTensor g₀ 3 2 :=
    rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  let Φ₂ : SmoothCcTensor g₀ 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hpath :
      realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ -
          realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ' =
        appCc (I := I) (M := M) g₀ 2 2 Φ₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 U) +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (iteratedCovGrad (I := I) g₀ 0 2 1 U) +
          appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U) := by
    simpa only [U, Φ₀, Φ₁, Φ₂] using
      rhsArm_sub_eq_paths (I := I) (M := M) g₀ g_bg T T'
        hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  have hiter₀ : iteratedCovGrad (I := I) g₀ 0 2 0 U = U := by
    rw [iteratedCovGrad_zero]
  have hiter₁ : iteratedCovGrad (I := I) g₀ 0 2 1 U =
      covGrad (I := I) (M := M) g₀ 0 2 U := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter₀, hiter₁] at hpath
  have hlower' :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
        (appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (covGrad (I := I) (M := M) g₀ 0 2 U))‖ ≤
        Ccoef * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
    apply hlower Φ₀ Φ₁ U B₀ B₀' B₁ hB₀ hB₀' hB₁
    · simpa only [Φ₀] using hΦ₀
    · simpa only [Φ₀] using hΦ₀'
    · simpa only [Φ₁] using hΦ₁
    · simpa only [Φ₁] using hΦ₁'
  have htop' :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
        (appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
          rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
        Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
    simpa only [U, Φ₂] using
      htop T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT' U
  rw [hpath]
  let Slow : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
      appCc (I := I) (M := M) g₀ 3 2 Φ₁
        (covGrad (I := I) (M := M) g₀ 0 2 U)
  let Stop : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 4 2 Φ₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g₀ 0 2 U
  have hsplit :
      (appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (covGrad (I := I) (M := M) g₀ 0 2 U) +
        appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U)) -
          rawTensorConnLapSmooth (I := I) g₀ 0 2 U = Slow + Stop := by
    simp only [Slow, Stop]
    abel
  rw [hsplit, ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) Slow‖ +
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) Stop‖ := norm_add_le _ _
    _ ≤ Ccoef * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ +
        (Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖) := by
      apply add_le_add
      · simpa only [Slow] using hlower'
      · simpa only [Stop] using htop'
    _ = Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          (Clow + Ccoef * (B₀ + B₀' + B₁)) *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by ring

-- The hypotheses below are sufficient bounds used only in the proof, so the
-- syntactic unused-variable linter cannot see their dependency in the result.
set_option linter.unusedVariables false in
/-- The viable conditional mixed `H3 -> H1` remainder estimate.  The concrete
lower path coefficients are controlled only by their intrinsic `L2` jets:
`H1` for the order-zero arm and `H2` for the order-one arm.  Thus the sole
coefficient multiplying the `H3` metric difference is the small `H2` ball
radius. -/
theorem rem_h1_of_jets
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ Ctop Clow Ccoef : ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧ 0 ≤ Clow ∧ 0 ≤ Ccoef ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        {R : ℝ} (hR : 0 ≤ R) (hRρ : R ≤ ρ)
        (hT : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R)
        (hT' : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R)
        (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
        (hΦ₀ : (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ_lt hδ hδ'_lt hδ')‖ ^ 2) ≤ A₀ ^ 2)
        (hΦ₁ : (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 j
            (rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ_lt hδ hδ'_lt hδ')‖ ^ 2) ≤ A₁ ^ 2),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          ((realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ -
              realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ') -
            rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤
          Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) (T - T')‖ +
            (Clow + Ccoef * (A₀ + A₁)) *
              ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, Clow, hρ, hCtop, hClow, htop⟩ :=
    top_path_ball_h1 (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Ccoef, hCcoef, hlower⟩ := lower_jet_h1 (I := I) (M := M) hDim g₀
  refine ⟨ρ, Ctop, Clow, Ccoef, hρ, hCtop, hClow, hCcoef, ?_⟩
  intro T T' hTsymm hT'symm δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT'
    A₀ A₁ hA₀ hA₁ hΦ₀ hΦ₁
  let U : SmoothCcTensor g₀ 0 2 := T - T'
  let Φ₀ : SmoothCcTensor g₀ 2 2 :=
    rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  let Φ₁ : SmoothCcTensor g₀ 3 2 :=
    rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  let Φ₂ : SmoothCcTensor g₀ 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hpath :
      realizedRHSArm (I := I) g₀ g_bg T hδ_lt hδ -
          realizedRHSArm (I := I) g₀ g_bg T' hδ'_lt hδ' =
        appCc (I := I) (M := M) g₀ 2 2 Φ₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 U) +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (iteratedCovGrad (I := I) g₀ 0 2 1 U) +
          appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U) := by
    simpa only [U, Φ₀, Φ₁, Φ₂] using
      rhsArm_sub_eq_paths (I := I) (M := M) g₀ g_bg T T'
        hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  have hiter₀ : iteratedCovGrad (I := I) g₀ 0 2 0 U = U := by
    rw [iteratedCovGrad_zero]
  have hiter₁ : iteratedCovGrad (I := I) g₀ 0 2 1 U =
      covGrad (I := I) (M := M) g₀ 0 2 U := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter₀, hiter₁] at hpath
  have hlower' :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
        (appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (covGrad (I := I) (M := M) g₀ 0 2 U))‖ ≤
        Ccoef * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
    apply hlower Φ₀ Φ₁ U A₀ A₁ hA₀ hA₁
    · simpa only [Φ₀] using hΦ₀
    · simpa only [Φ₁] using hΦ₁
  have htop' :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
        (appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
          rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
        Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
    simpa only [U, Φ₂] using
      htop T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT' U
  rw [hpath]
  let Slow : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
      appCc (I := I) (M := M) g₀ 3 2 Φ₁
        (covGrad (I := I) (M := M) g₀ 0 2 U)
  let Stop : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 4 2 Φ₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g₀ 0 2 U
  have hsplit :
      (appCc (I := I) (M := M) g₀ 2 2 Φ₀ U +
          appCc (I := I) (M := M) g₀ 3 2 Φ₁
            (covGrad (I := I) (M := M) g₀ 0 2 U) +
        appCc (I := I) (M := M) g₀ 4 2 Φ₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 U)) -
          rawTensorConnLapSmooth (I := I) g₀ 0 2 U = Slow + Stop := by
    simp only [Slow, Stop]
    abel
  rw [hsplit, ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) Slow‖ +
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ) Stop‖ := norm_add_le _ _
    _ ≤ Ccoef * (A₀ + A₁) *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ +
        (Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖) := by
      apply add_le_add
      · simpa only [Slow] using hlower'
      · simpa only [Stop] using htop'
    _ = Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
          (Clow + Ccoef * (A₀ + A₁)) *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow
