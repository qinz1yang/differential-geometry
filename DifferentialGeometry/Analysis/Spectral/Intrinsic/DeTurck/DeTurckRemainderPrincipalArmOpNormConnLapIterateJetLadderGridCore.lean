import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCometricDoubleTraceTransport
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCurvatureCommutatorJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadderCoefficientFieldSobolevEnvelope
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
  [T2Space M] [SigmaCompactSpace M]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)


lemma bal_gridcore (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
    (q j dc d₂ dw : ℕ) (hdc : dc ≤ 1) (hd₂ : d₂ ≤ 2)
    (hdw : dw ≤ Module.finrank ℝ E / 2 + 3)
    (hdw' : Module.finrank ℝ E / 2 + 1 ≤ dw)
    {sz : ℕ} (Z : SmoothCcTensor g₀ 0 sz)
    (sc : ℕ → ℕ) (Cf : (i : ℕ) → SmoothCcTensor g₀ 2 (sc i))
    (cC cCS : ℕ → ℝ) (hcC_nn : ∀ i, 0 ≤ cC i) (hcCS_nn : ∀ i, 0 ≤ cCS i)
    (hCL2 : ∀ i, ‖Cf i‖ ≤ cC i *
      (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((dc + i + 2 * q + 2 : ℕ) : ℝ) T₀‖))
    (hCsup : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) ≤
        (cCS i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((dc + i + (Module.finrank ℝ E / 2 + 2) + 2 * q + 1 : ℕ) : ℝ) T₀‖)) ^ 2)
    (sd : ℕ → ℕ) (Df : (l : ℕ) → SmoothCcTensor g₀ 0 (sd l))
    (cD cDS : ℕ → ℝ) (hcD_nn : ∀ l, 0 ≤ cD l) (_hcDS_nn : ∀ l, 0 ≤ cDS l)
    (hDL2 : ∀ l, ‖Df l‖ ≤ cD l *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + d₂ : ℕ) : ℝ) T₀‖)
    (hDsup : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (cDS l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dw : ℕ) : ℝ) T₀‖) ^ 2)
    (G : ℝ) (hG : 0 ≤ G)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      G * ∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) :
    ‖Z‖ ≤ Real.sqrt (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
        (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
          ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) *
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  set w : ℕ := n / 2 + 2 with hw_def
  set γ' : ℕ := j + 2 * q + 3 with hγ_def
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hfT_ball : ∀ k, k ≤ a + 2 → fT k ≤ R₀ := by
    intro k hk
    have h1 : fT k ≤ fT (a + 2) := hfT_mono hk
    have h2 : fT (a + 2) = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact le_trans h1 hball
  set SApred : ℕ → Prop := fun i => dc + i + w + 2 * q + 1 ≤ a + 2 with hSA_def
  have hSAdec : DecidablePred SApred := fun i => by
    rw [hSA_def]
    infer_instance
  set c1 : ℝ := G * ∑ i ∈ (Finset.range (j + 1)).filter SApred,
    (cCS i * (1 + R₀)) ^ 2 with hc1_def
  have hc1_nn : 0 ≤ c1 :=
    mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  set c2 : ℕ → ℝ := fun i => G * (if SApred i then 0 else
    ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) with hc2_def
  have hc2_nn : ∀ i, 0 ≤ c2 i := by
    intro i
    rw [hc2_def]
    dsimp only
    split_ifs with h
    · simp
    · exact mul_nonneg hG (Finset.sum_nonneg (fun l _ => sq_nonneg _))
  have hpt2 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 sz x (Z.toSection x) ≤
      (∑ l ∈ Finset.range (j + 1),
        c1 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)) +
      ∑ i ∈ Finset.range (j + 1),
        c2 i * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) := by
    intro x
    refine le_trans (hpt x) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (j + 1)) SApred]
    have hSApart : ∑ i ∈ (Finset.range (j + 1)).filter SApred,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        (∑ i ∈ (Finset.range (j + 1)).filter SApred, (cCS i * (1 + R₀)) ^ 2) *
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiSA : SApred i := (Finset.mem_filter.mp hi).2
      have hCf_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
          ((Cf i).toSection x) ≤ (cCS i * (1 + R₀)) ^ 2 := by
        refine le_trans (hCsup i x) ?_
        have hf_le : fT (dc + i + w + 2 * q + 1) ≤ R₀ := hfT_ball _ hiSA
        have h1 : cCS i * (1 + fT (dc + i + w + 2 * q + 1)) ≤ cCS i * (1 + R₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (hcCS_nn i)
          linarith
        refine pow_le_pow_left₀ ?_ h1 2
        have := hfT_nn (dc + i + w + 2 * q + 1)
        have := hcCS_nn i
        positivity
      have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
          ∑ l ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      have hD_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (sd l) x _)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
          ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_right hCf_le hD_nn
        _ ≤ (cCS i * (1 + R₀)) ^ 2 *
            ∑ l ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) :=
            mul_le_mul_of_nonneg_left hDsum_le (sq_nonneg _)
    have hSBpart : ∑ i ∈ (Finset.range (j + 1)).filter (fun i => ¬ SApred i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
        ∑ i ∈ Finset.range (j + 1),
          (if SApred i then 0 else
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum (fun i hi => ?_)
      split_ifs with h
      · simp
      · have hDsum_le : ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x) ≤
            ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hDsup l x)
        have hC_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x
            ((Cf i).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (sc i) x _
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (sd l) x ((Df l).toSection x)
            ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2 :=
              mul_le_mul_of_nonneg_left hDsum_le hC_nn
          _ = (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (sc i) x ((Cf i).toSection x) := by
              ring
    have hGmul := mul_le_mul_of_nonneg_left (add_le_add hSApart hSBpart) hG
    refine le_trans hGmul (le_of_eq ?_)
    rw [mul_add]
    congr 1
    · rw [← Finset.mul_sum, hc1_def]
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc2_def]
      dsimp only
      ring
  have hL2 := tensorL2NormSq_le_of_pointwise_fiberNormSq_le_two_sum (I := I) (M := M) g₀ Z (j + 1)
    (j + 1)
    (fun _ => c1) c2 (fun _ => hc1_nn) hc2_nn
    (fun _ => 0) sd Df (fun _ => 2) sc Cf hpt2
  have hSAfinal : ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
        (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
    have hc1_le : c1 ≤ G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 := by
      rw [hc1_def]
      refine mul_le_mul_of_nonneg_left ?_ hG
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => sq_nonneg _)
    have hterm : ∀ l ∈ Finset.range (j + 1), ‖Df l‖ ^ 2 ≤ (cD l) ^ 2 * fT γ' ^ 2 := by
      intro l hl
      have hlj := Finset.mem_range.mp hl
      have h1 : ‖Df l‖ ≤ cD l * fT γ' := by
        refine le_trans (hDL2 l) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hcD_nn l)
        exact hfT_mono (by omega)
      calc ‖Df l‖ ^ 2 ≤ (cD l * fT γ') ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (cD l) ^ 2 * fT γ' ^ 2 := by ring
    calc ∑ l ∈ Finset.range (j + 1), c1 * ‖Df l‖ ^ 2
        ≤ ∑ l ∈ Finset.range (j + 1),
            (G * ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
              ((cD l) ^ 2 * fT γ' ^ 2) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul hc1_le (hterm l hl) (sq_nonneg _) ?_
          exact mul_nonneg hG (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
            (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hSBfinal : ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
      (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
    have hterm : ∀ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2 ≤
        G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2) *
          fT γ' ^ 2) := by
      intro i hi
      have hij := Finset.mem_range.mp hi
      rw [hc2_def]
      dsimp only
      split_ifs with hSA
      · have h0 : G * 0 * ‖Cf i‖ ^ 2 = 0 := by ring
        rw [h0]
        have : (0:ℝ) ≤ G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
            (1 + R₀) ^ 2) * fT γ' ^ 2) := by positivity
        linarith
      · have hSB : ¬ (dc + i + w + 2 * q + 1 ≤ a + 2) := hSA
        have hcell : ∀ l ∈ Finset.range (j + 1 - i),
            (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2 ≤
              (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          intro l hl
          have hlj := Finset.mem_range.mp hl
          have hCf : ‖Cf i‖ ≤ cC i * (1 + fT (dc + i + 2 * q + 2)) := hCL2 i
          have hscore : fT (l + dw) * (1 + fT (dc + i + 2 * q + 2)) ≤ (1 + R₀) * fT γ' := by
            have hu_le : l + dw ≤ γ' := by omega
            have h1 : fT (l + dw) * 1 = fT (l + dw) := by ring
            have h2 : fT (l + dw) ≤ fT γ' := hfT_mono hu_le
            have h3 : fT (l + dw) * fT (dc + i + 2 * q + 2) ≤ R₀ * fT γ' := by
              have := tensorHs_norm_mul_le_ball_mul_tensorHs (I := I) (M := M) g₀ a hR₀ T₀ hball
                (u := l + dw) (v := dc + i + 2 * q + 2) (γ := γ')
                (by omega) (by omega) (Or.inl hu_le)
              exact this
            calc fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))
                = fT (l + dw) + fT (l + dw) * fT (dc + i + 2 * q + 2) := by ring
              _ ≤ fT γ' + R₀ * fT γ' := add_le_add h2 h3
              _ = (1 + R₀) * fT γ' := by ring
          have hprod : fT (l + dw) * ‖Cf i‖ ≤ cDS l * 0 + cC i * ((1 + R₀) * fT γ') := by
            have h1 : fT (l + dw) * ‖Cf i‖ ≤
                fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) :=
              mul_le_mul_of_nonneg_left hCf (hfT_nn _)
            have h2 : fT (l + dw) * (cC i * (1 + fT (dc + i + 2 * q + 2))) =
                cC i * (fT (l + dw) * (1 + fT (dc + i + 2 * q + 2))) := by ring
            rw [h2] at h1
            refine le_trans h1 ?_
            have h3 := mul_le_mul_of_nonneg_left hscore (hcC_nn i)
            linarith
          have hprod' : fT (l + dw) * ‖Cf i‖ ≤ cC i * ((1 + R₀) * fT γ') := by
            linarith [hprod]
          have hboth_nn : 0 ≤ fT (l + dw) * ‖Cf i‖ :=
            mul_nonneg (hfT_nn _) (norm_nonneg _)
          have hsq := pow_le_pow_left₀ hboth_nn hprod' 2
          calc (cDS l * fT (l + dw)) ^ 2 * ‖Cf i‖ ^ 2
              = (cDS l) ^ 2 * (fT (l + dw) * ‖Cf i‖) ^ 2 := by ring
            _ ≤ (cDS l) ^ 2 * (cC i * ((1 + R₀) * fT γ')) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
            _ = (cDS l) ^ 2 * ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by ring
        have hsum : (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2 ≤
            (∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2)) := by
          rw [Finset.sum_mul]
          refine le_trans (Finset.sum_le_sum hcell) ?_
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun y hy => Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega))
            (fun l _ _ => sq_nonneg _)
        calc G * (∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
            ‖Cf i‖ ^ 2
            = G * ((∑ l ∈ Finset.range (j + 1 - i), (cDS l * fT (l + dw)) ^ 2) *
              ‖Cf i‖ ^ 2) := by ring
          _ ≤ G * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              ((cC i) ^ 2 * ((1 + R₀) ^ 2 * fT γ' ^ 2))) :=
              mul_le_mul_of_nonneg_left hsum hG
          _ = G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := by ring
    calc ∑ i ∈ Finset.range (j + 1), c2 i * ‖Cf i‖ ^ 2
        ≤ ∑ i ∈ Finset.range (j + 1),
            G * ((cC i) ^ 2 * ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) *
              (1 + R₀) ^ 2) * fT γ' ^ 2) := Finset.sum_le_sum hterm
      _ = (G * (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
            ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) * fT γ' ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have htot : ‖Z‖ ^ 2 ≤ (G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2))) * fT γ' ^ 2 := by
    refine le_trans hL2 ?_
    have := add_le_add hSAfinal hSBfinal
    refine le_trans this (le_of_eq ?_)
    ring
  have hCB_nn : 0 ≤ G * ((∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2) *
      (∑ l ∈ Finset.range (j + 1), (cD l) ^ 2) +
      (∑ i ∈ Finset.range (j + 1), (cC i) ^ 2) *
        ((∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2) * (1 + R₀) ^ 2)) := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cCS i * (1 + R₀)) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h2 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cD l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h3 : 0 ≤ ∑ i ∈ Finset.range (j + 1), (cC i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h4 : 0 ≤ ∑ l ∈ Finset.range (j + 1), (cDS l) ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have h5 : (0:ℝ) ≤ (1 + R₀) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 h2, mul_nonneg h3 (mul_nonneg h4 h5)]
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (hfT_nn γ'))
  rw [mul_pow, Real.sq_sqrt hCB_nn]
  exact htot

end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
