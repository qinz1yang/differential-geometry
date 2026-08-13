import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeDifferenceEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PhiMetSymmetry
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSThreeArmCancel
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def edgeLowerArm (g : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  operatorFieldApply (I := I) (M := M) g 2 2 C₀ W +
    operatorFieldApply (I := I) (M := M) g 3 2 C₁
      (iteratedCovGrad (I := I) g 0 2 1 W)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem edgeZeroBound (g : SmoothRiemannianMetric I M) :
    metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) 0 := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0, ccTensorBilinSymm_smul]
  simp only [zero_mul, abs_zero, le_refl]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem edgeZeroSymm (g : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        smoothCcTensorBilinForm (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : Real) • (0 : SmoothCcTensor g 0 2) := (zero_smul Real _).symm
  rw [h0]
  simp only [ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, zero_mul]

def edgeMetric (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    {δ : Real}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) δ) (s : Real) :
    SmoothRiemannianMetric I M :=
  realizedFam (I := I) g W 0 hδ (edgeZeroBound (I := I) (M := M) g) s

def edgeCarry0 (g g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  (deTurckLieCoeffField (I := I) (M := M) g g g_bg +
      lieCorr0Field (I := I) (M := M) g g g_bg) +
    phiMetCurvCoeff (I := I) g g_bg g

def edgeCarry1 (g g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  deTurckLieArm1Coeff (I := I) (M := M) g g g_bg

def edgeQuad0 (g g1 g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  (-2 : Real) •
      linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g g1 +
    ((deTurckLieCoeffField (I := I) (M := M) g g1 g_bg +
        lieCorr0Field (I := I) (M := M) g g1 g_bg) +
      phiMetCurvCoeff (I := I) g g_bg g1) -
    edgeCarry0 (I := I) (M := M) g g_bg

def edgeQuad1 (g g1 g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 2 :=
  (-2 : Real) •
      linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g g1 +
    deTurckLieArm1Coeff (I := I) (M := M) g g1 g_bg -
    edgeCarry1 (I := I) (M := M) g g_bg

def edgeCarryArm (g g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  edgeLowerArm (I := I) (M := M) g
    (edgeCarry0 (I := I) (M := M) g g_bg)
    (edgeCarry1 (I := I) (M := M) g g_bg) W

def edgeQuadArm (g g1 g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  edgeLowerArm (I := I) (M := M) g
    (edgeQuad0 (I := I) (M := M) g g1 g_bg)
    (edgeQuad1 (I := I) (M := M) g g1 g_bg) W

theorem edgeTop_split
    (g g_bg g1 : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg g1)
        (iteratedCovGrad (I := I) g 0 2 2 W) =
      (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricArm (I := I) (M := M) g g1 W) +
        operatorFieldApply (I := I) (M := M) g 2 2
          (phiMetCurvCoeff (I := I) g g_bg g1) W := by
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 W =
      operatorFieldApply (I := I) (M := M) g 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 W) := by
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
      (I := I) (M := M) g W x v
  rw [show deTurckPhiMetTotal (I := I) (M := M) g g_bg g1 =
      ricciArmPrincipalCoeffPure (I := I) (M := M) g g1 +
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg g1 -
          ricciArmPrincipalCoeffPure (I := I) (M := M) g g1) by abel]
  rw [appCc_add_left,
    phiMet_curv_fold (I := I) (M := M) g g_bg g1 W,
    iteratedCovGrad_zero, deTurckPrincipalCometricArm,
    deTurckPrincipalCometricCoeff, appCc_sub_left, hlap]
  abel

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
private theorem edgeLower_add
    (g : SmoothRiemannianMetric I M)
    (C0 D0 : SmoothCcTensor g 2 2) (C1 D1 : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) :
    edgeLowerArm (I := I) (M := M) g (C0 + D0) (C1 + D1) W =
      edgeLowerArm (I := I) (M := M) g C0 C1 W +
        edgeLowerArm (I := I) (M := M) g D0 D1 W := by
  simp only [edgeLowerArm, appCc_add_left]
  abel

def edgeCoreArm (g g₁ : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  (rawTensorConnLapSmooth (I := I) g 0 2 W +
      deTurckPrincipalCometricArm (I := I) (M := M) g g₁ W) +
    edgeLowerArm (I := I) (M := M) g C₀ C₁ W

theorem edgeSlope_split
    (g g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x v w =
        smoothCcTensorBilinForm (I := I) g W x w v)
    {δ : Real} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g W) δ)
    (x : M) (v w : TangentSpace I x) {s : Real} (hs : s ∈ Set.Ioo (0 : Real) 1) :
    DeTurckCoefficients.rhsSumSlope (I := I) g g_bg W 0
        hδ_lt hδ (show (0 : Real) < 1 by norm_num)
        (edgeZeroBound (I := I) (M := M) g) x v w s =
      unitModel (I := I) (M := M) g 2
        ((rawTensorConnLapSmooth (I := I) g 0 2 W +
            deTurckPrincipalCometricArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hδ s) W) +
          (edgeCarryArm (I := I) (M := M) g g_bg W +
            edgeQuadArm (I := I) (M := M) g
              (edgeMetric (I := I) (M := M) g W hδ s) g_bg W)) x ![v, w] := by
  let gs : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g W hδ s
  let R0 : SmoothCcTensor g 2 2 :=
    DeTurckCoefficients.rhsLow0Coeff (I := I) (M := M)
      g g_bg W 0 hδ (edgeZeroBound (I := I) (M := M) g) s
  let R1 : SmoothCcTensor g 3 2 :=
    DeTurckCoefficients.rhsLow1Coeff (I := I) (M := M)
      g g_bg W 0 hδ (edgeZeroBound (I := I) (M := M) g) s
  have hlow0 : R0 + phiMetCurvCoeff (I := I) g g_bg gs =
      edgeCarry0 (I := I) (M := M) g g_bg +
        edgeQuad0 (I := I) (M := M) g gs g_bg := by
    simp only [R0, gs, edgeMetric, DeTurckCoefficients.rhsLow0Coeff,
      linearizedRicciConnDiffOrder0Coeff, edgeCarry0, edgeQuad0]
    abel
  have hlow1 : R1 =
      edgeCarry1 (I := I) (M := M) g g_bg +
        edgeQuad1 (I := I) (M := M) g gs g_bg := by
    simp only [R1, gs, edgeMetric, DeTurckCoefficients.rhsLow1Coeff,
      linearizedRicciConnDiffOrder1Coeff, edgeCarry1, edgeQuad1]
    abel
  have htop := edgeTop_split (I := I) (M := M) g g_bg gs W
  have hsmooth :
      operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
          operatorFieldApply (I := I) (M := M) g 3 2 R1
            (iteratedCovGrad (I := I) g 0 2 1 W) +
          operatorFieldApply (I := I) (M := M) g 4 2
            (deTurckPhiMetTotal (I := I) (M := M) g g_bg gs)
            (iteratedCovGrad (I := I) g 0 2 2 W) =
        (rawTensorConnLapSmooth (I := I) g 0 2 W +
            deTurckPrincipalCometricArm (I := I) (M := M) g gs W) +
          (edgeCarryArm (I := I) (M := M) g g_bg W +
            edgeQuadArm (I := I) (M := M) g gs g_bg W) := by
    rw [htop]
    calc
      operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
            operatorFieldApply (I := I) (M := M) g 3 2 R1
              (iteratedCovGrad (I := I) g 0 2 1 W) +
            ((rawTensorConnLapSmooth (I := I) g 0 2 W +
                deTurckPrincipalCometricArm (I := I) (M := M) g gs W) +
              operatorFieldApply (I := I) (M := M) g 2 2
                (phiMetCurvCoeff (I := I) g g_bg gs) W) =
          (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricArm (I := I) (M := M) g gs W) +
            edgeLowerArm (I := I) (M := M) g
              (R0 + phiMetCurvCoeff (I := I) g g_bg gs) R1 W := by
                simp only [edgeLowerArm, appCc_add_left]
                abel
      _ = (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricArm (I := I) (M := M) g gs W) +
            edgeLowerArm (I := I) (M := M) g
              (edgeCarry0 (I := I) (M := M) g g_bg +
                edgeQuad0 (I := I) (M := M) g gs g_bg)
              (edgeCarry1 (I := I) (M := M) g g_bg +
                edgeQuad1 (I := I) (M := M) g gs g_bg) W := by
                  rw [hlow0, hlow1]
      _ = (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricArm (I := I) (M := M) g gs W) +
            (edgeCarryArm (I := I) (M := M) g g_bg W +
              edgeQuadArm (I := I) (M := M) g gs g_bg W) := by
                  rw [edgeLower_add]
                  rfl
  have hslope := DeTurckCoefficients.rhsSlope_eq_arms
    (I := I) g g_bg W 0 hWsymm (edgeZeroSymm (I := I) (M := M) g)
      hδ_lt hδ (show (0 : Real) < 1 by norm_num)
      (edgeZeroBound (I := I) (M := M) g) x v w hs
  simp only [sub_zero, iteratedCovGrad_zero] at hslope
  rw [hslope]
  change unitModel (I := I) (M := M) g 2
      (operatorFieldApply (I := I) (M := M) g 2 2 R0 W +
        operatorFieldApply (I := I) (M := M) g 3 2 R1
          (iteratedCovGrad (I := I) g 0 2 1 W) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (deTurckPhiMetTotal (I := I) (M := M) g g_bg gs)
          (iteratedCovGrad (I := I) g 0 2 2 W)) x ![v, w] = _
  rw [hsmooth]

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
theorem edgeLower_pair_le
    (g : SmoothRiemannianMetric I M)
    (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
    (W : SmoothCcTensor g 0 2) {B₀ B₁ : Real}
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hC₀ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
        (C₀.toSection x) ≤ B₀ ^ 2)
    (hC₁ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x
        (C₁.toSection x) ≤ B₁ ^ 2) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (edgeLowerArm (I := I) (M := M) g C₀ C₁ W).toFun ≤
      (1 / 4 : Real) *
          ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        (B₀ + B₁ ^ 2) * ‖W‖ ^ 2 := by
  let D : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 W
  let U₀ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 C₀ W
  let U₁ : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 C₁ D
  have hU₀ : ‖U₀‖ ≤ B₀ * ‖W‖ := by
    dsimp only [U₀]
    exact operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 2 2 C₀ W B₀ hB₀ hC₀
  have hU₁ : ‖U₁‖ ≤ B₁ * ‖D‖ := by
    dsimp only [U₁]
    exact operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 3 2 C₁ D B₁ hB₁ hC₁
  have hpair₀ :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₀.toFun ≤
        B₀ * ‖W‖ ^ 2 := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W U₀]
    calc
      ⟪W, U₀⟫ ≤ ‖W‖ * ‖U₀‖ := real_inner_le_norm W U₀
      _ ≤ ‖W‖ * (B₀ * ‖W‖) :=
        mul_le_mul_of_nonneg_left hU₀ (norm_nonneg W)
      _ = B₀ * ‖W‖ ^ 2 := by ring
  have hpair₁ :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₁.toFun ≤
        B₁ * ‖W‖ * ‖D‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W U₁]
    calc
      ⟪W, U₁⟫ ≤ ‖W‖ * ‖U₁‖ := real_inner_le_norm W U₁
      _ ≤ ‖W‖ * (B₁ * ‖D‖) :=
        mul_le_mul_of_nonneg_left hU₁ (norm_nonneg W)
      _ = B₁ * ‖W‖ * ‖D‖ := by ring
  have hyoung :
      B₁ * ‖W‖ * ‖D‖ ≤
        (1 / 4 : Real) * ‖D‖ ^ 2 + B₁ ^ 2 * ‖W‖ ^ 2 := by
    nlinarith [sq_nonneg ((1 / 2 : Real) * ‖D‖ - B₁ * ‖W‖)]
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (edgeLowerArm (I := I) (M := M) g C₀ C₁ W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₀.toFun +
          tensorL2Inner (I := I) (M := M) g 0 2 W.toFun U₁.toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (edgeLowerArm (I := I) (M := M) g C₀ C₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W U₀,
      ← SmoothCcTensor.inner_def (I := I) (M := M) W U₁]
    simp only [edgeLowerArm, U₀, U₁, D, inner_add_right]
  rw [hadd]
  dsimp only [D] at hyoung ⊢
  nlinarith

theorem edgeCore_pair_le [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (C₀ : SmoothCcTensor g 2 2) (C₁ : SmoothCcTensor g 3 2)
        (W : SmoothCcTensor g 0 2) {B₀ B₁ δ : Real},
        0 ≤ B₀ → 0 ≤ B₁ → δ < 1 / 2 → 0 ≤ δ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g.inner y v w +
            ccTensorBilinSymm (I := I) g W y v w) →
        metricCauchySchwarzBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g W) δ →
        ccTensor02Symm (I := I) (M := M) g W = W →
        δ / (1 - δ) + C * δ ≤ 1 / 2 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
            (C₀.toSection x) ≤ B₀ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
            (C₁.toSection x) ≤ B₁ ^ 2) →
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (edgeCoreArm (I := I) (M := M) g g₁ C₀ C₁ W).toFun ≤
          -(1 / 4 : Real) *
              ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
            (B₀ + B₁ ^ 2) * ‖W‖ ^ 2 := by
  obtain ⟨C, hC, hprincipal⟩ := edgePrincipal_half (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro g₁ C₀ C₁ W B₀ B₁ δ hB₀ hB₁ hδ hδ0 htie hbound hsymm hsmall hC₀ hC₁
  have hp := hprincipal g₁ W hδ hδ0 htie hbound hsymm hsmall
  rw [SmoothCcTensor.norm_toL2] at hp
  have hlo := edgeLower_pair_le (I := I) (M := M)
    g C₀ C₁ W hB₀ hB₁ hC₀ hC₁
  have hadd :
      tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
          (edgeCoreArm (I := I) (M := M) g g₁ C₀ C₁ W).toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (rawTensorConnLapSmooth (I := I) g 0 2 W +
              deTurckPrincipalCometricArm (I := I) (M := M) g g₁ W).toFun +
          tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
            (edgeLowerArm (I := I) (M := M) g C₀ C₁ W).toFun := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) W
      (edgeCoreArm (I := I) (M := M) g g₁ C₀ C₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (rawTensorConnLapSmooth (I := I) g 0 2 W +
          deTurckPrincipalCometricArm (I := I) (M := M) g g₁ W),
      ← SmoothCcTensor.inner_def (I := I) (M := M) W
        (edgeLowerArm (I := I) (M := M) g C₀ C₁ W)]
    simp only [edgeCoreArm, inner_add_right]
  rw [hadd]
  nlinarith

end Spectral
end Analysis
end DifferentialGeometry

end
