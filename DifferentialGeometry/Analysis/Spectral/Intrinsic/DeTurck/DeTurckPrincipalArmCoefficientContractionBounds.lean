import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSobolevBounds
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

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
private lemma jet_fibreNormSq_sup_le (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ Cemb : ℕ → ℝ, (∀ l, 0 ≤ Cemb l) ∧ ∀ (Ψ : SmoothCcTensor g₀ r s) (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
          ((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x) ≤
        Cemb l * (∑ m ∈ Finset.range (4 * (Module.finrank ℝ E / 2 + 1) + 1),
          ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖) ^ 2 := by
  classical
  set K := Module.finrank ℝ E / 2 + 1 with hK
  have hK2 : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK]; omega
  have hstep : ∀ l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (Ψ : SmoothCcTensor g₀ r s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
          ((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x) ≤
        c * (∑ m ∈ Finset.range (4 * K + 1),
          ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖) ^ 2 := by
    intro l
    obtain ⟨Ce, hCe_pos, hCe⟩ :=
      tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ r (s + l) K 0 hK2
    obtain ⟨Cr, hCr_nn, hCr⟩ :=
      exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ r (s + l) (2 * K)
    refine ⟨(Ce * Cr) ^ 2, by positivity, fun Ψ x => ?_⟩
    letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace r (s + l) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ r (s + l)
    set Sum4K : ℝ := ∑ m ∈ Finset.range (4 * K + 1),
      ‖iteratedCovGrad (I := I) g₀ r s (l + m) Ψ‖ with hSum4K
    have hSum4K_nn : 0 ≤ Sum4K := Finset.sum_nonneg (fun m _ => norm_nonneg _)
    have hrevsum : (∑ j ∈ Finset.range (2 * (2 * K) + 1),
        tensorL2Norm (I := I) (M := M) g₀ r ((s + l) + j)
          (iteratedCovGrad (I := I) g₀ r (s + l) j
            (iteratedCovGrad (I := I) g₀ r s l Ψ)).toFun) = Sum4K := by
      rw [hSum4K, show 2 * (2 * K) + 1 = 4 * K + 1 by ring]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← SmoothCcTensor.norm_def]
      exact iteratedCovGrad_norm_comp (I := I) g₀ r s l m Ψ
    have hrev := hCr (iteratedCovGrad (I := I) g₀ r s l Ψ)
    rw [hrevsum] at hrev
    have hemb := hCe (iteratedCovGrad (I := I) g₀ r s l Ψ) x
    have hns : riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x) =
        ‖((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x :
          Tensor0SBundle.TensorRSSpace r (s + l) I x)‖ ^ 2 := by
      rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x,
        Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r (s + l) x _)]
    rw [hns]
    have hchain : ‖((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x :
          Tensor0SBundle.TensorRSSpace r (s + l) I x)‖ ≤ Ce * Cr * Sum4K := by
      calc ‖((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x :
              Tensor0SBundle.TensorRSSpace r (s + l) I x)‖
          ≤ Ce * ‖DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := r) (s := s + l) (2 * K)
              (iteratedCovGrad (I := I) g₀ r s l Ψ)‖ := hemb
        _ ≤ Ce * (Cr * Sum4K) := mul_le_mul_of_nonneg_left hrev hCe_pos.le
        _ = Ce * Cr * Sum4K := by ring
    calc ‖((iteratedCovGrad (I := I) g₀ r s l Ψ).toSection x :
            Tensor0SBundle.TensorRSSpace r (s + l) I x)‖ ^ 2
        ≤ (Ce * Cr * Sum4K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hchain 2
      _ = (Ce * Cr) ^ 2 * Sum4K ^ 2 := by ring
  choose Cemb hCemb_nn hCemb using hstep
  exact ⟨Cemb, hCemb_nn, fun Ψ l x => hCemb l Ψ x⟩

lemma coeffContract_iteratedCovGrad_jet_bound [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (b₀ s₀ dc dd : ℕ) (hdc : dc ≤ 2) (hdd : dd ≤ 3)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (Kw : ℕ → ℝ) (hKw_nn : ∀ l, 0 ≤ Kw l) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (_hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (Φ : SmoothCcTensor g₀ b₀ s₀)
        (_hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ≤
          Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
        (W : SmoothCcTensor g₀ 0 b₀)
        (_hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
          Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖)
        (q : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ≤
          Cm q * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((q + 3 : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
  classical
  set n := Module.finrank ℝ E with hn
  set K := n / 2 + 1 with hKdef
  set t := 2 * n + 5 with htdef
  obtain ⟨CembΦ, hCembΦ_nn, hCembΦ⟩ := jet_fibreNormSq_sup_le (I := I) (M := M) g₀ b₀ s₀
  obtain ⟨CembW, hCembW_nn, hCembW⟩ := jet_fibreNormSq_sup_le (I := I) (M := M) g₀ 0 b₀
  set KballΦ : ℕ → ℝ := fun i => CembΦ i *
    (∑ m ∈ Finset.range (4 * K + 1), Kc (i + m) * (1 + R₀)) ^ 2 with hKballΦ
  have hKballΦ_nn : ∀ i, 0 ≤ KballΦ i := fun i => mul_nonneg (hCembΦ_nn i) (sq_nonneg _)
  set DW : ℕ → ℝ := fun k => ∑ l ∈ Finset.range (k + 1),
    CembW l * (∑ m ∈ Finset.range (4 * K + 1), Kw (l + m)) ^ 2 with hDW
  have hDW_nn : ∀ k, 0 ≤ DW k := fun k => Finset.sum_nonneg
    (fun l _ => mul_nonneg (hCembW_nn l) (sq_nonneg _))
  set S1 : ℕ → ℝ := fun q => ∑ i ∈ (Finset.range (q + 1)).filter (· ≤ t),
    KballΦ i * ∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2 with hS1
  set S2 : ℕ → ℝ := fun q => ∑ i ∈ (Finset.range (q + 1)).filter (fun i => ¬ i ≤ t),
    DW (q - i) * (Kc i) ^ 2 * (1 + R₀) ^ 2 with hS2
  have hS1_nn : ∀ q, 0 ≤ S1 q := fun q => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hKballΦ_nn i) (Finset.sum_nonneg (fun l _ => sq_nonneg _)))
  have hS2_nn : ∀ q, 0 ≤ S2 q := fun q => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hDW_nn _) (sq_nonneg _)) (sq_nonneg _))
  refine ⟨fun q => Real.sqrt (diagonalGridGrowthFactor (E := E) q * (S1 q + S2 q)),
    fun q => Real.sqrt_nonneg _, ?_⟩
  intro p T₀ hball Φ hΦ W hW q
  set f : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖ with hf
  have hf_nn : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have hlc : ∀ k, f (k + 1) ^ 2 ≤ f (k + 2) * f k := fun k => hs_logConvex (I := I) (M := M) g₀ T₀ k
  have hmono : ∀ {k k' : ℕ}, k ≤ k' → f k ≤ f k' := by
    intro k k' hk
    exact smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀ (by exact_mod_cast hk) T₀
  have hballf : ∀ k, k ≤ a + 2 → f k ≤ R₀ := by
    intro k hk
    refine le_trans (smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀
      (show ((k : ℕ) : ℝ) ≤ (a : ℝ) + 2 by exact_mod_cast hk) T₀) hball
  have hfam : ∀ σ : ℕ, ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((σ : ℕ) : ℝ)
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ = f (σ + 2 * p) :=
    fun σ => hs_norm_family_shift (I := I) (M := M) g₀ T₀ p σ
  set supΦsq : ℕ → ℝ := fun i => CembΦ i *
    (∑ m ∈ Finset.range (4 * K + 1), ‖iteratedCovGrad (I := I) g₀ b₀ s₀ (i + m) Φ‖) ^ 2 with hsupΦsq
  set supWsq : ℕ → ℝ := fun l => CembW l *
    (∑ m ∈ Finset.range (4 * K + 1), ‖iteratedCovGrad (I := I) g₀ 0 b₀ (l + m) W‖) ^ 2 with hsupWsq
  have hsupΦsq_nn : ∀ i, 0 ≤ supΦsq i := fun i => mul_nonneg (hCembΦ_nn i) (sq_nonneg _)
  have hsupWsq_nn : ∀ l, 0 ≤ supWsq l := fun l => mul_nonneg (hCembW_nn l) (sq_nonneg _)
  have hΦpt : ∀ i x, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
      ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x) ≤ supΦsq i := hCembΦ Φ
  have hWpt : ∀ l x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
      ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) ≤ supWsq l := hCembW W
  have hWl2 : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 ≤ (Kw l) ^ 2 * f (l + dd + 2 * p) ^
    2 := by
    intro l
    have h := hW l
    rw [hfam (l + dd)] at h
    have : ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 ≤ (Kw l * f (l + dd + 2 * p)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [this]
  have hΦl2 : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 ≤ (Kc i) ^ 2 * (1 + f (i + dc)) ^
    2 := by
    intro i
    have : ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 ≤ (Kc i * (1 + f (i + dc))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hΦ i) 2
    nlinarith [this]
  have hsupΦ_region1 : ∀ i, i ≤ t → supΦsq i ≤ KballΦ i := by
    intro i hi
    rw [hsupΦsq, hKballΦ]
    refine mul_le_mul_of_nonneg_left ?_ (hCembΦ_nn i)
    refine pow_le_pow_left₀ (Finset.sum_nonneg (fun m _ => norm_nonneg _)) ?_ 2
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm4 : m ≤ 4 * K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hbound : i + m + dc ≤ a + 2 := by omega
    have hfle : f (i + m + dc) ≤ R₀ := hballf _ hbound
    calc ‖iteratedCovGrad (I := I) g₀ b₀ s₀ (i + m) Φ‖
        ≤ Kc (i + m) * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + m + dc : ℕ) : ℝ) T₀‖) :=
          hΦ (i + m)
      _ ≤ Kc (i + m) * (1 + R₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
          have : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + m + dc : ℕ) : ℝ) T₀‖ = f
            (i + m + dc) := rfl
          rw [this]; linarith [hfle]
  have hsupWsum_region2 : ∀ (q i : ℕ), t < i →
      (∑ l ∈ Finset.range (q + 1 - i), supWsq l) ≤ DW (q - i) * f (q - i + 4 * K + dd + 2 * p) ^
        2 := by
    intro q i hi
    rw [hDW, Finset.sum_mul]
    by_cases hle : i ≤ q
    · have hrange : q + 1 - i = (q - i) + 1 := by omega
      rw [hrange]
      refine Finset.sum_le_sum (fun l hl => ?_)
      have hlqi : l ≤ q - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [hsupWsq]
      have hstep1 : (∑ m ∈ Finset.range (4 * K + 1), ‖iteratedCovGrad (I := I) g₀ 0 b₀ (l + m) W‖) ≤
          (∑ m ∈ Finset.range (4 * K + 1), Kw (l + m)) * f (q - i + 4 * K + dd + 2 * p) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hm4 : m ≤ 4 * K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have hWlm := hW (l + m)
        rw [hfam (l + m + dd)] at hWlm
        refine le_trans hWlm ?_
        refine mul_le_mul_of_nonneg_left (hmono ?_) (hKw_nn _)
        omega
      calc CembW l * (∑ m ∈ Finset.range (4 * K + 1), ‖iteratedCovGrad (I := I) g₀ 0 b₀ (l + m) W‖)
             ^ 2
          ≤ CembW l * ((∑ m ∈ Finset.range (4 * K + 1), Kw (l + m)) * f
            (q - i + 4 * K + dd + 2 * p)) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (hCembW_nn l)
            refine pow_le_pow_left₀ (Finset.sum_nonneg (fun m _ => norm_nonneg _)) hstep1 2
        _ = CembW l * (∑ m ∈ Finset.range (4 * K + 1), Kw (l + m)) ^ 2 * f
          (q - i + 4 * K + dd + 2 * p) ^ 2 := by
            ring
    · have : q + 1 - i = 0 := by omega
      rw [this, Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_nonneg (fun l _ =>
        mul_nonneg (mul_nonneg (hCembW_nn l) (sq_nonneg _)) (sq_nonneg _))
  have hintW : ∀ l, ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
      ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
    intro l
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0 (b₀ + l)]
  have hintΦ : ∀ i, ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
      ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by
    intro i
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ b₀ (s₀ + i)]
  rw [hfam (q + 3)]
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀ with
    hμ
  have hG_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  set flt1 := (Finset.range (q + 1)).filter (· ≤ t) with hflt1
  set flt2 := (Finset.range (q + 1)).filter (fun i => ¬ i ≤ t) with hflt2
  set FW : M → ℝ := fun x => diagonalGridGrowthFactor (E := E) q *
    ((∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
          ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) +
      (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x))) with hFW
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
      ((iteratedCovGrad (I := I) g₀ 0 s₀ q
        (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)).toSection x) ≤ FW x := by
    intro x
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I)
      (M := M) g₀ b₀ s₀ Φ W q x) ?_
    simp only [hFW]
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (q + 1)) (· ≤ t)]
    refine add_le_add ?_ ?_
    · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hΦpt i x)
        (Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (b₀ + l)
          x _)))
    · refine Finset.sum_le_sum (fun i _ => ?_)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun l _ => hWpt l x))
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ b₀ (s₀ + i) x _)
  have hint1 : MeasureTheory.Integrable (fun x => ∑ i ∈ flt1, supΦsq i *
      ∑ l ∈ Finset.range (q + 1 - i), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
        ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum _ (fun i _ =>
      (MeasureTheory.integrable_finset_sum _ (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
          (iteratedCovGrad (I := I) g₀ 0 b₀ l W))).const_mul _)
  have hint2 : MeasureTheory.Integrable (fun x => ∑ i ∈ flt2,
      (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
        ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum _ (fun i _ =>
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ b₀ (s₀ + i)
        (iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ)).const_mul _)
  have hFint : MeasureTheory.Integrable FW μ := by
    simp only [hFW]; exact (hint1.add hint2).const_mul _
  have hnormsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (s₀ + q)
    (iteratedCovGrad (I := I) g₀ 0 s₀ q (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)) FW
      hFint hpt
  have hF1eq : (∫ x, (∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
          ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x)) ∂μ) =
      ∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
      (MeasureTheory.integrable_finset_sum _ (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
          (iteratedCovGrad (I := I) g₀ 0 b₀ l W))).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum _ (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (b₀ + l)
        (iteratedCovGrad (I := I) g₀ 0 b₀ l W))]
    exact congrArg _ (Finset.sum_congr rfl (fun l _ => hintW l))
  have hF2eq : (∫ x, (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)) ∂μ) =
      ∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ b₀ (s₀ + i)
        (iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ)).const_mul _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_const_mul, hintΦ i]
  have hintFW : ∫ x, FW x ∂μ = diagonalGridGrowthFactor (E := E) q *
      ((∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l
        W‖ ^ 2) +
       (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
          ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2)) := by
    simp only [hFW]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hint1 hint2, hF1eq, hF2eq]
  have hReg1 : (∑ i ∈ flt1, supΦsq i * ∑ l ∈ Finset.range (q + 1 - i),
        ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) ≤ S1 q * f (q + 3 + 2 * p) ^ 2 := by
    rw [hS1, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hit : i ≤ t := (Finset.mem_filter.mp hi).2
    have hile : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    have hdata : (∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) ≤
        (∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      have hlle : l ≤ q - i := by have hlr := Finset.mem_range.mp hl; omega
      refine le_trans (hWl2 l) ?_
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hf_nn _) (hmono ?_) 2) (sq_nonneg _)
      omega
    calc supΦsq i * ∑ l ∈ Finset.range (q + 1 - i), ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2
        ≤ KballΦ i * ((∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2) := by
          refine mul_le_mul (hsupΦ_region1 i hit) hdata
            (Finset.sum_nonneg (fun l _ => sq_nonneg _)) (hKballΦ_nn i)
      _ = KballΦ i * (∑ l ∈ Finset.range (q + 1 - i), (Kw l) ^ 2) * f (q + 3 + 2 * p) ^ 2 := by ring
  have hReg2 : (∑ i ∈ flt2, (∑ l ∈ Finset.range (q + 1 - i), supWsq l) *
        ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2) ≤ S2 q * f (q + 3 + 2 * p) ^ 2 := by
    rw [hS2, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hit : t < i := by
      have := (Finset.mem_filter.mp hi).2; omega
    have hile : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    have hβγ : q - i + 4 * K + dd + 2 * p ≤ q + 3 + 2 * p := by omega
    have hαγ : i + dc ≤ q + 3 + 2 * p := by omega
    have hsum_ok : (i + dc) + (q - i + 4 * K + dd + 2 * p) ≤ (a + 2) + (q + 3 + 2 * p) := by omega
    have hinterp : f (i + dc) * f (q - i + 4 * K + dd + 2 * p) ≤ R₀ * f (q + 3 + 2 * p) :=
      hs_extreme_interp hf_nn hlc hmono hballf hαγ hβγ hsum_ok
    have hfβγ : f (q - i + 4 * K + dd + 2 * p) ≤ f (q + 3 + 2 * p) := hmono hβγ
    have hexpand : (1 + f (i + dc)) ^ 2 * f (q - i + 4 * K + dd + 2 * p) ^ 2 ≤
        (1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2 := by
      have hABB : f (i + dc) * f (q - i + 4 * K + dd + 2 * p) * f (q - i + 4 * K + dd + 2 * p) ≤
          R₀ * f (q + 3 + 2 * p) * f (q + 3 + 2 * p) :=
        mul_le_mul hinterp hfβγ (hf_nn _) (mul_nonneg hR₀ (hf_nn _))
      have hABAB : (f (i + dc) * f (q - i + 4 * K + dd + 2 * p)) ^ 2 ≤ (R₀ * f (q + 3 + 2 * p)) ^
        2 :=
        pow_le_pow_left₀ (mul_nonneg (hf_nn _) (hf_nn _)) hinterp 2
      have hBB : f (q - i + 4 * K + dd + 2 * p) ^ 2 ≤ f (q + 3 + 2 * p) ^ 2 :=
        pow_le_pow_left₀ (hf_nn _) hfβγ 2
      nlinarith [hABB, hABAB, hBB]
    calc (∑ l ∈ Finset.range (q + 1 - i), supWsq l) * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
        ≤ (DW (q - i) * f (q - i + 4 * K + dd + 2 * p) ^ 2) *
          ((Kc i) ^ 2 * (1 + f (i + dc)) ^ 2) := by
          refine mul_le_mul (hsupWsum_region2 q i hit) (hΦl2 i) (sq_nonneg _)
            (mul_nonneg (hDW_nn _) (sq_nonneg _))
      _ = DW (q - i) * (Kc i) ^ 2 *
            ((1 + f (i + dc)) ^ 2 * f (q - i + 4 * K + dd + 2 * p) ^ 2) := by ring
      _ ≤ DW (q - i) * (Kc i) ^ 2 * ((1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2) :=
          mul_le_mul_of_nonneg_left hexpand (mul_nonneg (hDW_nn _) (sq_nonneg _))
      _ = DW (q - i) * (Kc i) ^ 2 * (1 + R₀) ^ 2 * f (q + 3 + 2 * p) ^ 2 := by ring
  have hfinalsq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
    (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
      (diagonalGridGrowthFactor (E := E) q * (S1 q + S2 q)) * f (q + 3 + 2 * p) ^ 2 := by
    refine le_trans hnormsq (le_trans (le_of_eq hintFW) ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    rw [add_mul]
    exact add_le_add hReg1 hReg2
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (hf_nn _))
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hG_nn (add_nonneg (hS1_nn q) (hS2_nn q)))]
  exact hfinalsq

lemma coeffContract_Hs_bound [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (b₀ dc dd : ℕ) (hdc : dc ≤ 2) (hdd : dd ≤ 3)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (Kw : ℕ → ℝ) (hKw_nn : ∀ l, 0 ≤ Kw l) :
    ∃ CE : ℕ → ℝ, (∀ j, 0 ≤ CE j) ∧
      ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (_hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (Φ : SmoothCcTensor g₀ b₀ 2)
        (_hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ 2 i Φ‖ ≤
          Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
        (W : SmoothCcTensor g₀ 0 b₀)
        (_hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
          Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖)
        (j : ℕ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ ≤
          CE j * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
  classical
  obtain ⟨Cm, hCm_nn, hCm⟩ :=
    coeffContract_iteratedCovGrad_jet_bound (I := I) (M := M) g₀ a ha hR₀ b₀ 2 dc dd hdc hdd Kc
      hKc_nn Kw hKw_nn
  have hstep : ∀ j, ∃ c, 0 ≤ c ∧ ∀ (p : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
      (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
      (Φ : SmoothCcTensor g₀ b₀ 2)
      (hΦ : ∀ i, ‖iteratedCovGrad (I := I) g₀ b₀ 2 i Φ‖ ≤
        Kc i * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((i + dc : ℕ) : ℝ) T₀‖))
      (W : SmoothCcTensor g₀ 0 b₀)
      (hW : ∀ l, ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ≤
        Kw l * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((l + dd : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ ≤
        c * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
    intro j
    obtain ⟨C1, hC1_nn, hC1⟩ := exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general g₀ j
    refine ⟨C1 * ∑ q ∈ Finset.range (j + 1), Cm q,
      mul_nonneg hC1_nn (Finset.sum_nonneg (fun q _ => hCm_nn q)),
      fun p T₀ hball Φ hΦ W hW => ?_⟩
    have hjet := hCm p T₀ hball Φ hΦ W hW
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖
        ≤ C1 * ∑ q ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)‖ :=
          hC1 (operatorFieldApply (I := I) (M := M) g₀ b₀ 2 Φ W)
      _ ≤ C1 * ∑ q ∈ Finset.range (j + 1), Cm q *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q hq => ?_)) hC1_nn
          have hqj : q ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
          refine le_trans (hjet q) (mul_le_mul_of_nonneg_left ?_ (hCm_nn q))
          exact smoothCcToTensorHs_norm_mono (I := I) (M := M) g₀
            (by exact_mod_cast (by omega : q + 3 ≤ j + 3)) _
      _ = C1 * (∑ q ∈ Finset.range (j + 1), Cm q) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 3 : ℕ) : ℝ)
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p T₀)‖ := by rw [← Finset.sum_mul]; ring
  choose CE hCE_nn hCE using hstep
  exact ⟨CE, hCE_nn, fun p T₀ hball Φ hΦ W hW j => hCE j p T₀ hball Φ hΦ W hW⟩

lemma iteratedCovGrad_slotExtend_norm_le (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g₀ r s Φ)‖ ≤
      Real.sqrt (Module.finrank ℝ E) * ‖iteratedCovGrad (I := I) g₀ r s i Φ‖ := by
  classical
  set F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
      ((iteratedCovGrad (I := I) g₀ r s i Φ).toSection x) with hF
  have hFint : MeasureTheory.Integrable F
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hF]
    exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r (s + i)
      (iteratedCovGrad (I := I) g₀ r s i Φ)).const_mul _
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
      ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g₀ r s Φ)).toSection x) ≤ F x :=
    fun x => rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ r s Φ i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ (r + 1)
    ((s + 1) + i) (iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g₀ r s Φ)) F hFint hpt
  have hint_eq : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i Φ).toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) =
      ‖iteratedCovGrad (I := I) g₀ r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r (s + i)]
  rw [hF, MeasureTheory.integral_const_mul, hint_eq] at hsq
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ))]
  exact hsq


end Spectral
end Analysis
end DifferentialGeometry

end
