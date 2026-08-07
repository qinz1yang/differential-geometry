import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmCoefficientContractionBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianAppCcCommutation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace r s I y)]
      (x : M) :
    NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x


private lemma cometricDoubleTraceField_iteratedCovGrad_norm_le
    (g₀ : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g₀ 0 2) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)‖ ≤
      (if i = 0 then ‖DeTurck.cometricDoubleTraceField (I := I) g₀ 2‖ else 0) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ (i : ℝ) T₀‖) := by
  rcases i with _ | k
  · rw [iteratedCovGrad_zero, if_pos rfl]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ) T₀‖ by
        linarith [norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ) T₀)])
      (norm_nonneg (DeTurck.cometricDoubleTraceField (I := I) g₀ 2))
  · have hzero : iteratedCovGrad (I := I) g₀ 4 2 (k + 1)
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2) = 0 :=
      iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g₀ 4 2
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) k
    rw [if_neg (Nat.succ_ne_zero k), hzero, norm_zero, zero_mul]

private theorem arm_commutator_Hs_family_tame [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ CEcomm : ℕ → ℝ, (∀ j, 0 ≤ CEcomm j) ∧
      ∀ (j : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (S : SmoothCcTensor g₀ 0 2)
        (_hSfam : ∃ p : ℕ, S = oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)) S) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball))
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 S))‖ ≤
          CEcomm j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by
  classical
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  set Cbr : ℕ → ℝ := fun m =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ m).choose with hCbrdef
  have hCbr_nn : ∀ m, 0 ≤ Cbr m :=
    fun m => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ m).choose_spec.1
  have hCbr : ∀ (m : ℕ) (Z : SmoothCcTensor g₀ 0 2),
      ∑ j ∈ Finset.range (m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Z‖ ≤
        Cbr m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) Z‖ :=
    fun m Z => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀
      m).choose_spec.2 Z
  obtain ⟨Ktame, hKtame_nn, hKtame⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_l2_tame_generic (I := I) (M := M) g₀ a (by omega)
      (mul_nonneg (hCbr_nn (a + 2)) hR₀) (show (1 : ℝ) / 3 < 1 by norm_num)
  obtain ⟨Kptc2, hKptc2_nn, hKptc2⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ 2
  obtain ⟨Kptc3, hKptc3_nn, hKptc3⟩ :=
    exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g₀ 3
  set BDT : ℝ := ‖DeTurck.cometricDoubleTraceField (I := I) g₀ 2‖ with hBDT
  set KcDT : ℕ → ℝ := fun i => if i = 0 then BDT else 0 with hKcDT
  have hKcDT_nn : ∀ i, 0 ≤ KcDT i := by
    intro i; rw [hKcDT]; dsimp only; split_ifs with h
    · exact norm_nonneg _
    · exact le_refl 0
  obtain ⟨Cm4in, hCm4in_nn, hCm4in⟩ :=
    coeffContract_iteratedCovGrad_jet_bound (I := I) (M := M) g₀ a ha_super hR₀ 4 4 2 2 (by omega)
      (by omega)
      (fun i => Ktame (i + 2)) (fun i => hKtame_nn _) (fun l => Cbr (l + 2)) (fun l => hCbr_nn _)
  obtain ⟨Cm56in, hCm56in_nn, hCm56in⟩ :=
    coeffContract_iteratedCovGrad_jet_bound (I := I) (M := M) g₀ a ha_super hR₀ 5 4 1 3 (by omega)
      (by omega)
      (fun i => Real.sqrt (Module.finrank ℝ E) * Ktame (i + 1))
      (fun i => mul_nonneg (Real.sqrt_nonneg _) (hKtame_nn _)) (fun l => Cbr (l + 3))
      (fun l => hCbr_nn _)
  obtain ⟨CE2, hCE2_nn, hCE2⟩ :=
    coeffContract_Hs_bound (I := I) (M := M) g₀ a ha_super hR₀ 4 0 2 (by omega) (by omega)
      Ktame hKtame_nn (fun l => Kptc2 (1 + l) * Cbr (l + 2))
      (fun l => mul_nonneg (hKptc2_nn _) (hCbr_nn _))
  obtain ⟨CE3, hCE3_nn, hCE3⟩ :=
    coeffContract_Hs_bound (I := I) (M := M) g₀ a ha_super hR₀ 4 0 2 (by omega) (by omega)
      Ktame hKtame_nn (fun l => Kptc3 l * Cbr (l + 2))
      (fun l => mul_nonneg (hKptc3_nn _) (hCbr_nn _))
  obtain ⟨CE4, hCE4_nn, hCE4⟩ :=
    coeffContract_Hs_bound (I := I) (M := M) g₀ a ha_super hR₀ 4 0 3 (by omega) (by omega)
      KcDT hKcDT_nn Cm4in hCm4in_nn
  obtain ⟨CE56, hCE56_nn, hCE56⟩ :=
    coeffContract_Hs_bound (I := I) (M := M) g₀ a ha_super hR₀ 4 0 3 (by omega) (by omega)
      KcDT hKcDT_nn Cm56in hCm56in_nn
  refine ⟨fun j => CE2 j + CE3 j + CE4 j + CE56 j + CE56 j,
    fun j => by have := hCE2_nn j; have := hCE3_nn j; have := hCE4_nn j; have := hCE56_nn j; linarith, ?_⟩
  intro j T₀ hball S hSfam
  obtain ⟨p, rfl⟩ := hSfam
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) with hg₁
  set C := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hC
  set DT₂ := DeTurck.cometricDoubleTraceField (I := I) g₀ 2 with hDT₂
  set S := oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀ with hSdef
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w :=
    fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) y v w
  have hδC : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hjetball : ∀ jj : ℕ, jj ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 jj T₀‖ ≤ Cbr (a + 2) *
    R₀ := by
    intro jj hjj
    have hsum := hCbr (a + 2) T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ ≤ R₀ := by
      rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by push_cast; ring) T₀]; exact hball
    have hmem : jj ∈ Finset.range (a + 2 + 1) := Finset.mem_range.mpr (by omega)
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 jj T₀‖ ≤
        ∑ k ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k T₀‖ :=
      Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k T₀‖)
        (fun k _ => norm_nonneg _) hmem
    exact le_trans hsingle (le_trans hsum (mul_le_mul_of_nonneg_left hcast (hCbr_nn _)))
  have hCtame : ∀ i, ‖iteratedCovGrad (I := I) g₀ 4 2 i C‖ ≤
      Ktame i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ (i : ℝ) T₀‖) :=
    hKtame g₁ T₀ hδ_le hδC htie hjetball
  set W2 : SmoothCcTensor g₀ 0 4 :=
    covGrad (I := I) (M := M) g₀ 0 3 (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S) with hW2def
  set W3 : SmoothCcTensor g₀ 0 4 :=
    pointwiseTensorCurv (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) with hW3def
  set Φ4 : SmoothCcTensor g₀ 4 4 :=
    covGrad (I := I) (M := M) g₀ 4 3 (covGrad (I := I) (M := M) g₀ 4 2 C) with hΦ4def
  set Wdata : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hWdatadef
  set Wdata3 : SmoothCcTensor g₀ 0 5 :=
    covGrad (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) with hWdata3def
  set Φ5 : SmoothCcTensor g₀ 5 4 :=
    slotExtend (I := I) (M := M) g₀ 4 3 (covGrad (I := I) (M := M) g₀ 4 2 C) with hΦ5def
  set Φ6 : SmoothCcTensor g₀ 5 4 :=
    covGrad (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C) with hΦ6def
  set t4 : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 4 2 DT₂
      (operatorFieldApply (I := I) (M := M) g₀ 4 4 Φ4 Wdata) with ht4def
  set t5 : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 4 2 DT₂
      (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ5 Wdata3) with ht5def
  set t6 : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 4 2 DT₂
      (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ6 Wdata3) with ht6def
  set t2 : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 4 2 C W2 with ht2def
  set t3 : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 4 2 C W3 with ht3def
  have hDTjet : ∀ i, ‖iteratedCovGrad (I := I) g₀ 4 2 i DT₂‖ ≤
      KcDT i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 0 : ℕ) : ℝ) T₀‖) := by
    intro i
    have hBDT' : BDT = ‖DeTurck.cometricDoubleTraceField (I := I) g₀ 2‖ := by
      rw [hBDT, hDT₂]
    simpa only [hDT₂, hKcDT, hBDT', Nat.add_zero] using
      (cometricDoubleTraceField_iteratedCovGrad_norm_le (I := I) (M := M) g₀ T₀ i)
  have hΦ4jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ 4 4 i Φ4‖ ≤
      Ktame (i + 2) * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ) T₀‖) := by
    intro i
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 4 4 i Φ4‖ = ‖iteratedCovGrad (I := I) g₀ 4 2 (2 + i)
      C‖ := by
      rw [hΦ4def]; exact iteratedCovGrad_norm_comp (I := I) g₀ 4 2 2 i C
    rw [hcomp, show (2 + i : ℕ) = (i + 2 : ℕ) from by omega]
    exact hCtame (i + 2)
  have hΦslot : ∀ (i : ℕ) (Ψ : SmoothCcTensor g₀ 5 4)
      (hcov : ‖iteratedCovGrad (I := I) g₀ 5 4 i Ψ‖ ≤ Real.sqrt (Module.finrank ℝ E) *
        ‖iteratedCovGrad (I := I) g₀ 4 2 (1 + i) C‖),
      ‖iteratedCovGrad (I := I) g₀ 5 4 i Ψ‖ ≤
        Real.sqrt (Module.finrank ℝ E) * Ktame (i + 1) *
          (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖) := by
    intro i Ψ hcov
    rw [show (1 + i : ℕ) = (i + 1 : ℕ) from by omega] at hcov
    refine le_trans hcov ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCtame (i + 1)) (Real.sqrt_nonneg _)
  have hΦ5jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ 5 4 i Φ5‖ ≤
      Real.sqrt (Module.finrank ℝ E) * Ktame (i + 1) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖) := by
    intro i
    refine hΦslot i Φ5 ?_
    rw [hΦ5def]
    refine le_trans (iteratedCovGrad_slotExtend_norm_le (I := I) g₀ 4 3 i
      (covGrad (I := I) (M := M) g₀ 4 2 C)) (le_of_eq ?_)
    have heq : ‖iteratedCovGrad (I := I) g₀ 4 3 i (covGrad (I := I) (M := M) g₀ 4 2 C)‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 (1 + i) C‖ := iteratedCovGrad_norm_comp (I := I) g₀ 4 2 1 i
          C
    rw [heq]
  have hΦ6jet : ∀ i, ‖iteratedCovGrad (I := I) g₀ 5 4 i Φ6‖ ≤
      Real.sqrt (Module.finrank ℝ E) * Ktame (i + 1) *
        (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ) T₀‖) := by
    intro i
    refine hΦslot i Φ6 ?_
    have heq : ‖iteratedCovGrad (I := I) g₀ 5 4 i Φ6‖ =
        ‖iteratedCovGrad (I := I) g₀ 5 3 (1 + i) (slotExtend (I := I) (M := M) g₀ 4 2 C)‖ := by
      rw [hΦ6def]; exact iteratedCovGrad_norm_comp (I := I) g₀ 5 3 1 i
        (slotExtend (I := I) (M := M) g₀ 4 2 C)
    rw [heq]
    exact iteratedCovGrad_slotExtend_norm_le (I := I) g₀ 4 2 (1 + i) C
  have hSjet : ∀ (m : ℕ), ‖iteratedCovGrad (I := I) g₀ 0 2 m S‖ ≤
      Cbr m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) S‖ := by
    intro m
    refine le_trans ?_ (hCbr m S)
    exact Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hWdata : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l Wdata‖ ≤
      Cbr (l + 2) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    have heq : ‖iteratedCovGrad (I := I) g₀ 0 4 l Wdata‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + l) S‖ := by
      rw [hWdatadef]; exact iteratedCovGrad_norm_comp (I := I) g₀ 0 2 2 l S
    rw [heq, show (2 + l : ℕ) = (l + 2 : ℕ) from by omega]
    exact hSjet (l + 2)
  have hWdata3 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 5 l Wdata3‖ ≤
      Cbr (l + 3) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ := by
    intro l
    have heq : ‖iteratedCovGrad (I := I) g₀ 0 5 l Wdata3‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (3 + l) S‖ := iteratedCovGrad_norm_comp (I := I) g₀ 0 2 3 l
          S
    rw [heq, show (3 + l : ℕ) = (l + 3 : ℕ) from by omega]
    exact hSjet (l + 3)
  have hW2 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l W2‖ ≤
      (Kptc2 (1 + l) * Cbr (l + 2)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    have hcomp : ‖iteratedCovGrad (I := I) g₀ 0 4 l W2‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 3 (1 + l)
          (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)‖ := by
      rw [hW2def]
      exact iteratedCovGrad_norm_comp (I := I) g₀ 0 3 1 l
        (pointwiseTensorCurv (I := I) (M := M) g₀ 2 S)
    rw [hcomp]
    refine le_trans (hKptc2 (1 + l) S) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hKptc2_nn _)
    rw [show (1 + l + 2 : ℕ) = (l + 2) + 1 from by omega]
    exact hCbr (l + 2) S
  have hW3 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l W3‖ ≤
      (Kptc3 l * Cbr (l + 2)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 2 : ℕ) : ℝ) S‖ := by
    intro l
    refine le_trans (hKptc3 l (covGrad (I := I) (M := M) g₀ 0 2 S)) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hKptc3_nn _)
    have hstep : (∑ a ∈ Finset.range (l + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 3 a (covGrad (I := I) (M := M) g₀ 0 2 S)‖) ≤
        ∑ k ∈ Finset.range (l + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖ := by
      have heq : (∑ a ∈ Finset.range (l + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 3 a (covGrad (I := I) (M := M) g₀ 0 2 S)‖) =
          ∑ a ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 (a + 1) S‖ := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        have hac : ‖iteratedCovGrad (I := I) g₀ 0 3 a (covGrad (I := I) (M := M) g₀ 0 2 S)‖ =
            ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + a) S‖ := iteratedCovGrad_norm_comp (I := I) g₀ 0 2
              1 a S
        rw [hac, show (1 + a : ℕ) = (a + 1 : ℕ) from by omega]
      rw [heq]
      have hsr := Finset.sum_range_succ' (fun k => ‖iteratedCovGrad (I := I) g₀ 0 2 k S‖) (l + 2)
      have h0 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 0 S‖ := norm_nonneg _
      linarith [hsr, h0]
    refine le_trans hstep ?_
    exact hCbr (l + 2) S
  have hINNER4 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l
        (operatorFieldApply (I := I) (M := M) g₀ 4 4 Φ4 Wdata)‖ ≤
      Cm4in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm4in p T₀ hball Φ4 hΦ4jet Wdata hWdata l
  have hINNER5 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l
        (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ5 Wdata3)‖ ≤
      Cm56in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm56in p T₀ hball Φ5 hΦ5jet Wdata3 hWdata3 l
  have hINNER6 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 4 l
        (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ6 Wdata3)‖ ≤
      Cm56in l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + 3 : ℕ) : ℝ) S‖ :=
    fun l => hCm56in p T₀ hball Φ6 hΦ6jet Wdata3 hWdata3 l
  have hbt2 := hCE2 p T₀ hball C hCtame W2 hW2 j
  have hbt3 := hCE3 p T₀ hball C hCtame W3 hW3 j
  have hbt4 := hCE4 p T₀ hball DT₂ hDTjet (operatorFieldApply (I := I) (M := M) g₀ 4 4 Φ4 Wdata)
    hINNER4 j
  have hbt5 := hCE56 p T₀ hball DT₂ hDTjet (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ5 Wdata3)
    hINNER5 j
  have hbt6 := hCE56 p T₀ hball DT₂ hDTjet (operatorFieldApply (I := I) (M := M) g₀ 5 4 Φ6 Wdata3)
    hINNER6 j
  have hdecomp : rawTensorConnLapSmooth (I := I) g₀ 0 2
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) -
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)
        =
      t2 + t3 + t4 + t5 + t6 := by
    have he : rawTensorConnLapSmooth (I := I) g₀ 0 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 C (iteratedCovGrad (I := I) g₀ 0 2 2 S)) =
        operatorFieldApply (I := I) (M := M) g₀ 4 2 C
            (iteratedCovGrad (I := I) g₀ 0 2 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) +
          t2 + t3 + t4 + t5 + t6 := by
      rw [rawConnLap_appCc_iteratedCovGrad_two_comm (I := I) g₀ 2 2 C S]
    change rawTensorConnLapSmooth (I := I) g₀ 0 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 C (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
      operatorFieldApply (I := I) (M := M) g₀ 4 2 C
        (iteratedCovGrad (I := I) g₀ 0 2 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) =
      t2 + t3 + t4 + t5 + t6
    rw [he]; abel
  rw [hdecomp]
  have htri : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) (t2 + t3 + t4 + t5 + t6)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t2‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t3‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t4‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t5‖ +
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t6‖ := by
    rw [smoothCcToTensorHs_add, smoothCcToTensorHs_add, smoothCcToTensorHs_add,
      smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ (le_refl _)
    exact norm_add_le _ _
  have hcast : ((j : ℕ) : ℝ) = (j : ℝ) := by norm_num
  have hQS_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := norm_nonneg _
  refine le_trans htri ?_
  have e2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t2‖ ≤
      CE2 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by rw [← hcast];
                                                                                    exact hbt2
  have e3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t3‖ ≤
      CE3 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by rw [← hcast];
                                                                                    exact hbt3
  have e4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t4‖ ≤
      CE4 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by rw [← hcast];
                                                                                    exact hbt4
  have e5 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t5‖ ≤
      CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by rw [← hcast];
                                                                                     exact hbt5
  have e6 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t6‖ ≤
      CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by rw [← hcast];
                                                                                     exact hbt6
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t2‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t3‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t4‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t5‖ +
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (j : ℝ) t6‖
      ≤ CE2 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE3 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE4 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ +
          CE56 j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by
        refine add_le_add (add_le_add (add_le_add (add_le_add e2 e3) e4) e5) e6
    _ = (CE2 j + CE3 j + CE4 j + CE56 j + CE56 j) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ) S‖ := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem arm_covGrad_coeffLower_l2_tame [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (S : SmoothCcTensor g₀ 0 2),
        ‖operatorFieldApply (I := I) (M := M) g₀ 4 3
            (covGrad (I := I) (M := M) g₀ 4 2
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball))))
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)‖ ≤
          Cgrad * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
  classical
  letI inst03 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst23 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  obtain ⟨Cpo, hCpo_nn, hCpo⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨Cenv, hCenv_nn, hCenv⟩ :=
    norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one (I := I) (M := M) g₀
  have hm_super : 2 * (2 * (Module.finrank ℝ E / 2 + 1) + 1) ≤ a + 2 := by omega
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_iteratedCovGrad_fiberNormSq_le_smoothCcToTensorHs_sq (I := I) (M := M) g₀ 1 (a + 2)
      hm_super
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hδ_nn : 0 ≤ δ := delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hδ_half : δ < 1 / 2 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1 / 2)
  set R : ℝ := Cq * R₀ with hR_def
  have hR_nn : 0 ≤ R := mul_nonneg hCq_nn hR₀
  set Bsq : ℝ := Cpo 1 * ((Module.finrank ℝ E : ℝ) ^ 2 + (Cenv * (1 + R)) ^ 2) with hBsq_def
  have hBsq_nn : 0 ≤ Bsq := mul_nonneg (hCpo_nn 1) (by positivity)
  set B : ℝ := Real.sqrt Bsq with hB_def
  have hB_nn : 0 ≤ B := Real.sqrt_nonneg _
  have hBsqeq : B ^ 2 = Bsq := Real.sq_sqrt hBsq_nn
  refine ⟨B * (1 + Cj0), mul_nonneg hB_nn (by linarith [hCj0_nn]), fun T₀ hball S => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) with hg₁_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w :=
    fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) y v w
  have hδC : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hHsle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ ≤ R₀ := by
    rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by push_cast; ring) T₀]
    exact hball
  have hjet_x : ∀ x : M, ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R := by
    intro x
    have hc2 := hCq T₀ x
    have hrfns_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x) ≤ R ^ 2 := by
      refine le_trans hc2 ?_
      rw [hR_def, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hHsle 2) (sq_nonneg Cq)
    rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      (iteratedCovGrad (I := I) g₀ 0 2 1 T₀)]
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T₀).toSection x))
        ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hrfns_le
      _ = R := Real.sqrt_sq hR_nn
  have hΦ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 3 x
      ((covGrad (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤ B ^ 2 := by
    intro x
    have hperord := hCpo g₁ 1 x
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hperord
    have hj0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 :=
      riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T₀ hδ_half hδ_nn htie hδC x
    have hj1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        (Cenv * (1 + R)) ^ 2 := by
      have henv := hCenv g₁ T₀ hδ_half hδ_nn htie hδC x hR_nn (hjet_x x)
      rw [pow_one, norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
        (iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁))] at henv
      have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 3 x
        ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)
      have key : riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
          (Cenv * (1 + R)) ^ 2 := by
        nlinarith [henv, Real.sq_sqrt hnn, Real.sqrt_nonneg
          (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
            ((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)),
          mul_nonneg hCenv_nn (by linarith [hR_nn] : (0 : ℝ) ≤ 1 + R)]
      exact key
    refine le_trans hperord ?_
    rw [hBsqeq, hBsq_def]
    exact mul_le_mul_of_nonneg_left (add_le_add hj0 hj1) (hCpo_nn 1)
  refine le_trans (operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left (I := I) (M := M) g₀
    4 3
    (covGrad (I := I) (M := M) g₀ 4 2 (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) B hB_nn hΦ) ?_
  have hjet := hCj0 S
  have hdrop := smoothCcToTensorHs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
  have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ :=
    smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
  have hΔ0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    rw [← hdrop_congr]; exact hdrop
  have h2jet : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
      (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by
    nlinarith [hjet, hΔ0, hmono, hCj0_nn,
      norm_nonneg (smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S),
      mul_le_mul_of_nonneg_left hmono hCj0_nn]
  calc B * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖
      ≤ B * ((1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖) :=
        mul_le_mul_of_nonneg_left h2jet hB_nn
    _ = B * (1 + Cj0) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma appCc_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ - operatorFieldApply (I := I) (M := M) g r s Φ
        W₂ := by
  have h : operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) +
      operatorFieldApply (I := I) (M := M) g r s Φ W₂ = operatorFieldApply (I := I) (M := M) g r s Φ
        W₁ := by
    rw [← appCc_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma deTurckPrincipalCometricArm_sub (g₀ g₁ : SmoothRiemannianMetric I M)
    (u v : SmoothCcTensor g₀ 0 2) :
    deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ (u - v) =
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u -
        deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ v := by
  rw [deTurckPrincipalCometricArm, deTurckPrincipalCometricArm, deTurckPrincipalCometricArm,
    iteratedCovGrad_sub, appCc_sub_right]

private lemma smoothCcToTensorHs_subCross (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (u v : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (u - v) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ u - smoothCcToTensorHs (I := I) (M := M) g₀ σ
        v := by
  refine tensorHs.ext (funext fun i => ?_)
  simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff, smoothCcToTensorHs_coeff,
    map_add, map_neg, tensorL2Coeff_eq_inner, inner_add_right, inner_neg_right]

omit [I.Boundaryless] in
private lemma rawConnLap_oneMinusConnLap_comm [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) =
      oneMinusConnLapSmooth (I := I) g₀ 0 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, rawTensorConnLapSmooth_sub]

private lemma principalArm_zero_order_algebra {x c p d q m : ℝ}
    (hx : x ≤ c * (p + d * q)) (hm : c * d ≤ m) (hq : 0 ≤ q) :
    x ≤ c * p + m * q := by
  calc x ≤ c * (p + d * q) := hx
    _ = c * p + (c * d) * q := by ring
    _ ≤ c * p + m * q := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hm hq)

private lemma norm_le_add_of_sq_eq_sq_add_sq {z a b u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hz : z ^ 2 = a ^ 2 + b ^ 2)
    (ha : a ^ 2 ≤ u ^ 2) (hb : b ^ 2 ≤ v ^ 2) :
    z ≤ u + v := by
  refine le_of_sq_le_sq ?_ (add_nonneg hu hv)
  rw [hz]
  nlinarith [ha, hb, mul_nonneg hu hv]

theorem deTurckPrincipalCometricArm_realize_Hs_norm_succ_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hδ_nn : 0 ≤ δ :=
    delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  have hCE_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) := deTurckArmFibreConst_nonneg _
  set CEκ : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) with hCEκ_def
  have hCEκ_nn : 0 ≤ CEκ := by rw [hCEκ_def]; positivity
  obtain ⟨CEcomm, hCEcomm_nn, hCEcomm⟩ :=
    arm_commutator_Hs_family_tame (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cgrad, hCgrad_nn, hCgrad⟩ :=
    arm_covGrad_coeffLower_l2_tame (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cj0, hCj0_nn, hCj0⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 0
  obtain ⟨Cj1, hCj1_nn, hCj1⟩ := iteratedCovGrad_le_connLap_add (I := I) (M := M) g₀ 1
  set Mbase : ℝ := CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) + CEκ * Cj0 + 1 with hMbase_def
  have hMbase_nn : 0 ≤ Mbase := by rw [hMbase_def]; positivity
  set ClowerFn : ℕ → ℝ := fun j => Mbase + ∑ i ∈ Finset.range j, CEcomm i with hClowerFn_def
  have hClowerFn_nn : ∀ j, 0 ≤ ClowerFn j := fun j => by
    rw [hClowerFn_def]
    exact add_nonneg hMbase_nn (Finset.sum_nonneg fun i _ => hCEcomm_nn i)
  refine ⟨fun m => ClowerFn (m + 1), fun m => hClowerFn_nn (m + 1), fun m T₀ hball => ?_⟩
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) with hg₁_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := fun y v w =>
    tensorSectionRealizeMetric_inner (I := I) g₀ T₀ hδ_lt1 (hδ_fibre T₀ hball) y v w
  have hδC : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hcoeff : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 := fun x =>
    riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T₀) htie hδ_lt1 hδ_nn hδC x
  have hG : ∀ (j : ℕ) (S : SmoothCcTensor g₀ 0 2),
      (∃ p : ℕ, S = oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀) →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
        CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
          ClowerFn j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 1 : ℕ) : ℝ) S‖ := by
    have hG0 : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            ClowerFn 0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := by
      intro S
      have hHs0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ =
          ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ := by
        rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num, smoothCcToTensorHs_zero_norm_eq,
          SmoothCcTensor.norm_toL2]
      have harm := arm_l2_le (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T₀) htie
        hδ_lt1 hδ_nn hδC S
      have hjet := hCj0 S
      have hP0_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := norm_nonneg _
      have hQ1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      rw [hHs0]
      have hClf0 : ClowerFn 0 = Mbase := by
        rw [hClowerFn_def]; simp
      rw [hClf0]
      have hstep : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
          CEκ * (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖) :=
        le_trans harm (by
          have := mul_le_mul_of_nonneg_left hjet hCEκ_nn
          rwa [hCEκ_def] at this ⊢)
      have hMbase_ge : CEκ * Cj0 ≤ Mbase := by rw [hMbase_def]; nlinarith [hCEκ_nn, hCj0_nn]
      exact principalArm_zero_order_algebra hstep hMbase_ge hQ1_nn
    have hG1 : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
            ClowerFn 1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ := by
      intro S
      set C := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ with hCdef
      set Q := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 + 1 : ℕ) : ℝ) S‖ with hQ_def
      set P := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ with hP_def
      have hQ_nn : 0 ≤ Q := norm_nonneg _
      have hP_nn : 0 ≤ P := norm_nonneg _
      have ha2 := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad (I := I) (M := M) g₀ 0
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)
      simp only [oneMinusConnLapSmoothIter_zero] at ha2
      rw [smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
          (show ((2 * 0 + 1 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) by norm_num)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S),
        SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at ha2
      have hA2jet := hCj0 S
      have hdrop := smoothCcToTensorHs_rawConnLap_order_le (I := I) (M := M) g₀ 0 S
      have hdrop_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 2 : ℕ) : ℝ) S‖ = Q :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
      have hmono01 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ ≤ Q :=
        smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀ (by push_cast; norm_num) S
      have hΔ0_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ ≤ Q := by rw [← hdrop_congr]; exact hdrop
      have hA2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤ (1 + Cj0) * Q := by
        have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ ≤
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℕ) : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ +
              Cj0 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 + 1 : ℕ) : ℝ) S‖ := hA2jet
        nlinarith [h1, hΔ0_le, hmono01, hCj0_nn, hQ_nn,
          mul_le_mul_of_nonneg_left hmono01 hCj0_nn]
      have ha_bound : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ≤
          CEκ * (1 + Cj0) * Q := by
        have harm := arm_l2_le (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T₀) htie
          hδ_lt1 hδ_nn hδC S
        calc ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖
            ≤ CEκ * ‖iteratedCovGrad (I := I) g₀ 0 2 2 S‖ := harm
          _ ≤ CEκ * ((1 + Cj0) * Q) := mul_le_mul_of_nonneg_left hA2_le hCEκ_nn
          _ = CEκ * (1 + Cj0) * Q := by ring
      have hcov3 : covGrad (I := I) (M := M) g₀ 0 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          iteratedCovGrad (I := I) g₀ 0 2 3 S :=
        (iteratedCovGrad_succ g₀ 0 2 2 S).symm
      have hcov : covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) =
          operatorFieldApply (I := I) (M := M) g₀ 4 3 (covGrad (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) +
            operatorFieldApply (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 3 S) := by
        rw [deTurckPrincipalCometricArm, ← hCdef, covGrad_operatorFieldApply_eq, hcov3]
      have hgrad := hCgrad T₀ hball S
      have hgrad_congr : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 : ℕ) : ℝ) S‖ = Q :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) S
      rw [hgrad_congr] at hgrad
      have hprinc := arm_covGrad_slotExtend_l2_le (I := I) (M := M) g₀ g₁ hκ_nn hcoeff S
      have hA3jet := hCj1 S
      have hA3_le : ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ ≤ P + Cj1 * Q := hA3jet
      have hb_bound : ‖covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤
          CEκ * P + (Cgrad + CEκ * Cj1) * Q := by
        rw [hcov]
        refine le_trans (norm_add_le _ _) ?_
        have hprinc' : ‖operatorFieldApply (I := I) (M := M) g₀ 5 3
          (slotExtend (I := I) (M := M) g₀ 4 2 C)
              (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖ ≤ CEκ * P + CEκ * Cj1 * Q := by
          calc ‖operatorFieldApply (I := I) (M := M) g₀ 5 3 (slotExtend (I := I) (M := M) g₀ 4 2 C)
                (iteratedCovGrad (I := I) g₀ 0 2 3 S)‖
              ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := hprinc
            _ = CEκ * ‖iteratedCovGrad (I := I) g₀ 0 2 3 S‖ := by rw [hCEκ_def]
            _ ≤ CEκ * (P + Cj1 * Q) := mul_le_mul_of_nonneg_left hA3_le hCEκ_nn
            _ = CEκ * P + CEκ * Cj1 * Q := by ring
        have hdist : Cgrad * Q + (CEκ * P + CEκ * Cj1 * Q) =
            CEκ * P + (Cgrad + CEκ * Cj1) * Q := by ring
        linarith [hgrad, hprinc', hdist]
      have hClf1_ge : CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) ≤ ClowerFn 1 := by
        have h1 : Mbase ≤ ClowerFn 1 := by
          simp only [hClowerFn_def, Finset.sum_range_one]
          linarith [hCEcomm_nn 0]
        have h2 : CEκ * (1 + Cj0) + (Cgrad + CEκ * Cj1) ≤ Mbase := by
          rw [hMbase_def]; linarith [mul_nonneg hCEκ_nn hCj0_nn]
        linarith [h1, h2]
      set α := CEκ * (1 + Cj0) with hα_def
      set β := Cgrad + CEκ * Cj1 with hβ_def
      have hα_nn : 0 ≤ α := mul_nonneg hCEκ_nn (by linarith [hCj0_nn])
      have hβ_nn : 0 ≤ β := add_nonneg hCgrad_nn (mul_nonneg hCEκ_nn hCj1_nn)
      have ha_sq : ‖deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S‖ ^ 2 ≤ (α * Q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ha_bound 2
      have hb_sq : ‖covGrad (I := I) (M := M) g₀ 0 2
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ^ 2 ≤
          (CEκ * P + β * Q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb_bound 2
      have hfinal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖ ≤ CEκ * P + (α + β) * Q := by
        calc
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖
              ≤ α * Q + (CEκ * P + β * Q) :=
            norm_le_add_of_sq_eq_sq_add_sq
              (mul_nonneg hα_nn hQ_nn)
              (add_nonneg (mul_nonneg hCEκ_nn hP_nn) (mul_nonneg hβ_nn hQ_nn))
              ha2 ha_sq hb_sq
          _ = CEκ * P + (α + β) * Q := by ring
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)‖
          ≤ CEκ * P + (α + β) * Q := hfinal
        _ ≤ CEκ * P + ClowerFn 1 * Q := by
            have hmul := mul_le_mul_of_nonneg_right hClf1_ge hQ_nn
            linarith [hmul]
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      match j, IH with
      | 0, _ => exact fun S _ => hG0 S
      | 1, _ => exact fun S _ => hG1 S
      | (i + 2), IH =>
        have ih := IH i (by omega)
        intro S hSfam
        have hA3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S)
        have hLarm : oneMinusConnLapSmooth (I := I) g₀ 0 2
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) -
              (rawTensorConnLapSmooth (I := I) g₀ 0 2
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) -
                deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁
                  (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) := by
          rw [oneMinusConnLapSmooth, oneMinusConnLapSmooth, deTurckPrincipalCometricArm_sub]
          abel
        rw [hA3, hLarm, smoothCcToTensorHs_subCross]
        refine le_trans (norm_sub_le _ _) ?_
        have hih := ih (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
          (by obtain ⟨p, hp⟩ := hSfam;
              exact ⟨p + 1, by rw [hp, oneMinusConnLapSmoothIter_succ]⟩)
        have hcommΔ := rawConnLap_oneMinusConnLap_comm (I := I) (M := M) g₀ S
        have hA3Δ := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ i
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)
        have hprinc : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 : ℕ) : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)‖ := by
          rw [hcommΔ, ← hA3Δ]
        have hA3S := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap (I := I) (M := M) g₀ (i + 1)
          S
        have hlower : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 1 : ℕ) : ℝ)
              (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by
          rw [← hA3S]
        rw [hprinc, hlower] at hih
        have hE := hCEcomm i T₀ hball S hSfam
        have hcast_goal : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 2 + 1 : ℕ) : ℝ) S‖ =
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
          smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
        rw [hcast_goal]
        have hQ3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ :=
          norm_nonneg _
        have hCl_rec : ClowerFn i + CEcomm i ≤ ClowerFn (i + 2) := by
          have hsub : ∑ k ∈ Finset.range i, CEcomm k + CEcomm i ≤
              ∑ k ∈ Finset.range (i + 2), CEcomm k := by
            calc ∑ k ∈ Finset.range i, CEcomm k + CEcomm i
                = ∑ k ∈ Finset.range (i + 1), CEcomm k := (Finset.sum_range_succ CEcomm i).symm
              _ ≤ ∑ k ∈ Finset.range (i + 2), CEcomm k :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.range_mono (by omega)) (fun k _ _ => hCEcomm_nn k)
          simp only [hClowerFn_def]
          linarith [hsub]
        refine le_trans (add_le_add hih hE) ?_
        have hmul := mul_le_mul_of_nonneg_right hCl_rec hQ3_nn
        have hdist : ClowerFn i *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ +
            CEcomm i * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ =
            (ClowerFn i + CEcomm i) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + 3 : ℕ) : ℝ) S‖ := by ring
        linarith [hmul, hdist]
  have hchild := hG (m + 1) T₀ ⟨0, rfl⟩
  have hcast1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ T₀)‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcast2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcast3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  rw [hcast1, hcast2, hcast3] at hchild
  exact hchild

theorem deTurckPrincipalCometricArm_realize_Hs_norm_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cl0, hCl0_nn, hbase⟩ :=
    arm_realize_Hs_norm_zero_le (I := I) (M := M) g₀ a hR₀ hδ_le hδ_fibre
  obtain ⟨Cls, hCls_nn, hstep⟩ :=
    deTurckPrincipalCometricArm_realize_Hs_norm_succ_le (I := I) (M := M) g₀ a
      ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun m => match m with
    | 0 => Cl0
    | (k + 1) => Cls k, fun m => ?_, fun m T₀ hball => ?_⟩
  · match m with
    | 0 => exact hCl0_nn
    | (k + 1) => exact hCls_nn k
  · match m with
    | 0 =>
      have h0 : ((0 : ℕ) : ℝ) = (0 : ℝ) := by norm_num
      have hb := hbase T₀ hball
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ h0
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) T₀)
      have hnormR := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ h0
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
      have hnormT := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (0 : ℝ) + 1 by rw [h0]) T₀
      rw [hnormL, hnormR, hnormT]
      exact hb
    | (k + 1) =>
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hs := hstep k T₀ hball
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hcast
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) T₀)
      have hnormR := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hcast
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
      have hnormT := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by rw [hcast]; ring) T₀
      rw [hnormL, hnormR, hnormT]
      exact hs

theorem deTurckPrincipalCometricArm_Hs_inner_le [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (φ : SmoothCcTensor g₀ 0 2),
        (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
            (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)) : ℝ) ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := by
  obtain ⟨Clower, hCl_nn, hnorm⟩ :=
    deTurckPrincipalCometricArm_realize_Hs_norm_le (I := I) (M := M) g₀ a
      ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hCl_nn, fun m T₀ hball φ => ?_⟩
  have hCS := real_inner_le_norm
    (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
    (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀))
  have hb := hnorm m T₀ hball
  have hφ_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := norm_nonneg _
  calc (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ)
        (smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀)) : ℝ)
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ := hCS
    _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ *
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖) :=
        mul_le_mul_of_nonneg_left hb hφ_nn
    _ = deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ +
          Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) φ‖ := by ring

end Spectral
end Analysis
end DifferentialGeometry

end
