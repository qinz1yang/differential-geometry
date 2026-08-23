import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeL2EigenProjection
import DifferentialGeometry.Analysis.ProjectedContractionFixedPoint
import Mathlib.Analysis.ODE.Gronwall
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import Mathlib.Topology.Algebra.InfiniteSum.Real
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DuhamelSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.PointwiseDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Modulus

section
open DifferentialGeometry.Analysis.Sobolev.CSupTensor
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

omit [BoundarylessManifold I M] in
theorem galerkinForcing_eq_galerkinCoordEmbed
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2) =
      galerkinCoordEmbed (I := I) (M := M) g₀ a (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1)) := by
  apply tensorHs.ext
  funext i
  rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · rw [if_pos hi, dif_pos hi]
    rfl
  · rw [if_neg hi, dif_neg hi]

omit [BoundarylessManifold I M] in
theorem continuousOn_galerkinForcing_field
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))
      (Set.Icc (0 : ℝ) T) := by
  have hcoord : ContinuousOn
      (fun t => (EuclideanSpace.equiv
          {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
        (fun j => U N t j.1)) (Set.Icc (0 : ℝ) T) := by
    apply (EuclideanSpace.equiv
      {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm.continuous.comp_continuousOn
    refine continuousOn_pi.2 (fun j => hUcont j.1 j.2)
  have hcomp : ContinuousOn
      (fun t => galerkinCoordEmbed (I := I) (M := M) g₀ a
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        ((EuclideanSpace.equiv
            {i // i ∈ eigenIdxFinset (I := I) (M := M) g₀ N} ℝ).symm
          (fun j => U N t j.1))) (Set.Icc (0 : ℝ) T) :=
    (galerkinCoordEmbed (I := I) (M := M) g₀ a
      (eigenIdxFinset (I := I) (M := M) g₀ N)).continuous.comp_continuousOn hcoord
  refine hcomp.congr (fun t _ => ?_)
  rw [galerkinForcing_eq_galerkinCoordEmbed]

theorem continuousOn_galerkinForcing
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N hUcont
    have hcoeff : ContinuousOn
        (fun t => (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))))
          (Set.Icc (0 : ℝ) T) :=
        (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.comp_continuousOn hN_cont
      simpa only [tensorHsCoeffL_apply] using hcoeff_cont
    refine hcoeff.congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_pos hi]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [deTurckGalerkinForcing_apply, if_neg hi]

theorem galerkinPerMode_eq_perModeConv
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U N t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N p.1 i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (continuousOn_galerkinForcing (I := I) (M := M) g₀ g_bg a ha_super U N hUcont i).restrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N x i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) = -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      simp only [NNReal.coe_mk, le_refl]
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => U N s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hUcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hUderiv s hs i hi
    have hforce_eq : fForce s = deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -(lam) * U N s i + deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hUinit i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

theorem perModeConv_timeL2_sub (lam : ℝ) (f₁ f₂ : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    perModeConv lam (fun s => f₁ s) t - perModeConv lam (fun s => f₂ s) t =
      perModeConv lam (fun s => (f₁ - f₂) s) t := by
  have hcongr : perModeConv lam (fun s => (f₁ - f₂) s) t =
      perModeConv lam (fun s => f₁ s - f₂ s) t :=
    perModeConv_timeL2_congr lam
      (by filter_upwards [Lp.coeFn_sub f₁ f₂] with r hr using hr) ht
  rw [hcongr]
  unfold perModeConv
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_kernel_mul_timeL2 lam t f₁ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)
    (intervalIntegrable_kernel_mul_timeL2 lam t f₂ 0 t
      ⟨le_rfl, le_trans ht.1 ht.2⟩ ht)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem tendsto_perModeConv_of_tendsto_timeL2 (lam : ℝ) (hlam : 0 ≤ lam)
    {fseq : ℕ → timeL2 ℝ T} {flim : timeL2 ℝ T}
    (hconv : Tendsto fseq atTop (𝓝 flim))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => perModeConv lam (fun s => (fseq N) s) t) atTop
      (𝓝 (perModeConv lam (fun s => flim s) t)) := by
  rcases le_or_gt 0 T with hT0 | hT0
  · rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε hε
    rcases eq_or_lt_of_le hT0 with hT00 | hTpos
    · have htval : t = 0 := by
        obtain ⟨ht1, ht2⟩ := ht
        rw [← hT00] at ht2
        exact le_antisymm ht2 ht1
      refine ⟨0, fun N _ => ?_⟩
      rw [htval]
      simp only [perModeConv_zero_left, dist_self]
      exact hε
    · set δ : ℝ := ε / (Real.sqrt T + 1) with hδ_def
      have hsqrt_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
      have hδ_pos : 0 < δ := by
        rw [hδ_def]; positivity
      obtain ⟨Nε, hNε⟩ := hconv δ hδ_pos
      refine ⟨Nε, fun N hN => ?_⟩
      have hdist : dist (fseq N) flim < δ := hNε N hN
      have hsub_eq :
          perModeConv lam (fun s => (fseq N) s) t - perModeConv lam (fun s => flim s) t =
            perModeConv lam (fun s => (fseq N - flim) s) t :=
        perModeConv_timeL2_sub lam (fseq N) flim ht
      have hbound : |perModeConv lam (fun s => (fseq N - flim) s) t| ≤
          Real.sqrt T * ‖fseq N - flim‖ :=
        abs_perModeConv_timeL2_le lam hlam (fseq N - flim) ht
      have hnorm : ‖fseq N - flim‖ < δ := by
        rw [← dist_eq_norm]; exact hdist
      rw [Real.dist_eq, hsub_eq]
      calc |perModeConv lam (fun s => (fseq N - flim) s) t|
          ≤ Real.sqrt T * ‖fseq N - flim‖ := hbound
        _ ≤ Real.sqrt T * δ :=
            mul_le_mul_of_nonneg_left (le_of_lt hnorm) hsqrt_nn
        _ < ε := by
            have hden : (0 : ℝ) < Real.sqrt T + 1 := by positivity
            rw [hδ_def,
              show Real.sqrt T * (ε / (Real.sqrt T + 1))
                = (Real.sqrt T * ε) / (Real.sqrt T + 1) by ring,
              div_lt_iff₀ hden]
            nlinarith [hsqrt_nn, hε]
  · have htval : t = 0 := by
      obtain ⟨ht1, ht2⟩ := ht
      have : t ≤ 0 := le_trans ht2 (le_of_lt hT0)
      exact le_antisymm this ht1
    rw [htval]
    simp only [perModeConv_zero_left]
    exact tendsto_const_nhds

theorem unifIntegrable_of_uniform_norm_bound {α β : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [NormedAddCommGroup β]
    {f : ℕ → α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) :
    UnifIntegrable f 2 μ := by
  refine unifIntegrable_of (by norm_num) (by norm_num) hf (fun ε hε => ?_)
  refine ⟨(max C 0).toNNReal + 1, fun n => ?_⟩
  have hzero : { x | (max C 0).toNNReal + 1 ≤ ‖f n x‖₊ }.indicator (f n) =ᵐ[μ] 0 := by
    filter_upwards [hC n] with x hx
    have hle : ‖f n x‖₊ < (max C 0).toNNReal + 1 := by
      have hxle : ‖f n x‖ ≤ (max C 0) := le_trans hx (le_max_left _ _)
      have : (‖f n x‖₊ : ℝ) ≤ (max C 0).toNNReal := by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]; exact hxle
      have hlt : (‖f n x‖₊ : ℝ) < ((max C 0).toNNReal : ℝ) + 1 := by linarith
      exact_mod_cast hlt
    rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, not_le]; exact hle)]
    rfl
  rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
  exact zero_le _

omit [BoundarylessManifold I M] in
private theorem tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ' σ'' : ℝ}
    (hσ'σ'' : σ' < σ'')
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0)) :
    Tendsto (fun n => ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  classical
  set ι := TensorEigenIdx (I := I) (M := M) g r s
  have hnormsq : ∀ n,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ ^ 2 =
        ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ((d n).coeff i) ^ 2 := by
    intro n
    have h := tensorHs.norm_sq_eq_tsum (I := I) (M := M)
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))
    rwa [tensorHsInclusion_coeff] at h
  have hsumm' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) :=
    fun n => tensorHs.weighted_summable_of_le (I := I) (M := M) hσ'σ''.le (d n)
  have hmass'' : ∀ n,
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2
        = ‖d n‖ ^ 2 :=
    fun n => (tensorHs.norm_sq_eq_tsum (I := I) (M := M) (d n)).symm
  suffices hsq : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖ ^ 2) atTop (𝓝 0) by
    have hnn : ∀ n,
        0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ := fun n => norm_nonneg _
    have hsqrt :
        Tendsto (fun n => Real.sqrt
          (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            hσ'σ''.le (d n)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr (fun n => ?_)
    rw [Real.sqrt_sq (hnn n)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hexp : σ' - σ'' < 0 := by linarith
  obtain ⟨Λ, hΛgt1, hΛtail⟩ :
      ∃ Λ : ℝ, 1 < Λ ∧ Λ ^ (σ' - σ'') * C ^ 2 < ε / 2 := by
    set δ : ℝ := (ε / 2) / (C ^ 2 + 1) with hδ_def
    have hδ_pos : 0 < δ := by
      have : (0 : ℝ) < C ^ 2 + 1 := by positivity
      rw [hδ_def]; positivity
    have htend : Tendsto (fun x : ℝ => x ^ (σ' - σ'')) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := σ'' - σ') (by linarith)
      rwa [show -(σ'' - σ') = σ' - σ'' by ring] at h
    have hev : ∀ᶠ x : ℝ in atTop, x ^ (σ' - σ'') < δ :=
      htend.eventually_lt_const hδ_pos
    obtain ⟨Λ, hΛ1, hΛδ⟩ := ((eventually_gt_atTop 1).and hev).exists
    refine ⟨Λ, hΛ1, ?_⟩
    have hΛδ_nn : 0 ≤ Λ ^ (σ' - σ'') := Real.rpow_nonneg (by linarith) _
    have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg C
    have h1 : Λ ^ (σ' - σ'') * C ^ 2 ≤ δ * C ^ 2 :=
      mul_le_mul_of_nonneg_right hΛδ.le hCsq_nn
    have h2 : δ * C ^ 2 < ε / 2 := by
      rw [hδ_def]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
      have hεpos : 0 < ε / 2 := by linarith
      nlinarith [hεpos, hCsq_nn]
    linarith
  set F : Finset ι :=
    (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset
    with hF_def
  have hmemF : ∀ i : ι, i ∈ F ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
    intro i; rw [hF_def, Set.Finite.mem_toFinset]; rfl
  have hcompl_bd : ∀ (n : ℕ) (i : ι), i ∉ F →
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
    intro n i hi
    have hΛle : Λ ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      by_contra hcon
      exact hi ((hmemF i).2 (lt_of_not_ge hcon))
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ' =
        tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
          tensorSobolevWeight (I := I) (M := M) i σ'' := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)]
      congr 1; ring
    have hratio : tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') ≤
        Λ ^ (σ' - σ'') := by
      unfold tensorSobolevWeight
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hΛle hexp.le
    have hw''_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
    have hcoeff_nn : 0 ≤ ((d n).coeff i) ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
            rw [hsplit]; ring
      _ ≤ Λ ^ (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
  have htail : ∀ n,
      ∑' i : { i : ι // i ∉ F },
          tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') * C ^ 2 := by
    intro n
    have hsub_summ' : Summable (fun i : { i : ι // i ∉ F } =>
        tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2) :=
      (hsumm' n).subtype _
    have hsub_summ'' : Summable (fun i : { i : ι // i ∉ F } =>
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2)) :=
      ((d n).weighted_summable.subtype _).mul_left _
    calc
      ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2
          ≤ ∑' i : { i : ι // i ∉ F },
              Λ ^ (σ' - σ'') *
                (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                  ((d n).coeff i) ^ 2) :=
            hsub_summ'.tsum_le_tsum
              (fun i => hcompl_bd n i.1 i.2) hsub_summ''
      _ = Λ ^ (σ' - σ'') *
            ∑' i : { i : ι // i ∉ F },
              tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2 :=
            (tsum_mul_left)
      _ ≤ Λ ^ (σ' - σ'') *
            ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
              ((d n).coeff i) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            refine ((d n).weighted_summable.subtype _).tsum_le_tsum_of_inj
              Subtype.val Subtype.val_injective (fun i _ => ?_) (fun i => le_refl _)
              (d n).weighted_summable
            have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
              tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
            positivity
      _ ≤ Λ ^ (σ' - σ'') * C ^ 2 := by
            rw [hmass'' n]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            have hnn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
            nlinarith [hCbd n, hnn, hC]
  have hfin0 : Tendsto (fun n =>
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (s := F)
      (f := fun i n => tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      (a := fun _ : ι => (0 : ℝ))
      (fun i _ => by
        have hc : Tendsto (fun n => ((d n).coeff i) ^ 2) atTop (𝓝 (0 ^ 2)) :=
          (hcoeff0 i).pow 2
        rw [show (0 : ℝ) ^ 2 = 0 by ring] at hc
        have := hc.const_mul (tensorSobolevWeight (I := I) (M := M) i σ')
        simpa using this)
    simpa using h
  rw [Metric.tendsto_atTop] at hfin0
  obtain ⟨N, hN⟩ := hfin0 (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hsplit_sum :
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) +
          ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 :=
    ((hsumm' n).sum_add_tsum_subtype_compl F).symm
  have hfin_lt : ∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 < ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
        ≤ |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2| :=
          le_abs_self _
      _ < ε / 2 := hd
  have htail_lt : ∑' i : { i : ι // i ∉ F },
      tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 < ε / 2 :=
    lt_of_le_of_lt (htail n) hΛtail
  have hbound : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 < ε := by
    rw [hnormsq n, hsplit_sum]
    linarith
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 := sq_nonneg _
  rwa [abs_of_nonneg hnn]

omit [BoundarylessManifold I M] in
theorem tendsto_finiteEigenComboHs_of_coeff_tendsto_of_succWeighted_bound
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (W : tensorHs (I := I) (M := M) g 0 2 σ) (B : ℝ)
    (hbound : ∀ N, ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 ≤ B)
    (hcoeff : ∀ i, Tendsto
        (fun N => (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i)
        atTop (𝓝 (W.coeff i))) :
    Tendsto (fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ)
      atTop (𝓝 W) := by
  classical
  set u : ℕ → tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    fun N => finiteEigenComboHs (I := I) (M := M) g (S N) (c N) (σ + 1) with hu_def
  have hu_coeff : ∀ N i, (u N).coeff i =
      (finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ).coeff i := by
    intro N i
    simp only [hu_def, finiteEigenComboHs_coeff]
  have hconv_coeff : ∀ i, Tendsto (fun N => (u N).coeff i) atTop (𝓝 (W.coeff i)) := by
    intro i
    exact (hcoeff i).congr (fun N => (hu_coeff N i).symm)
  have hu_normSq_le : ∀ N, ‖u N‖ ^ 2 ≤ B := by
    intro N
    have heq : ‖u N‖ ^ 2 = ∑ i ∈ S N,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 := by
      simp only [hu_def]
      rw [finiteEigenCombo_spectral_normSq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rfl
    rw [heq]; exact hbound N
  have hbd_finset : ∀ t : Finset (TensorEigenIdx (I := I) (M := M) g 0 2),
      ∑ i ∈ t, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 ≤ B := by
    intro t
    have hlim : Tendsto
        (fun N => ∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2)
        atTop
        (𝓝 (∑ i ∈ t,
          tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2)) := by
      refine tendsto_finset_sum t (fun i _ => ?_)
      exact ((hconv_coeff i).pow 2).const_mul _
    have hle : ∀ N, ∑ i ∈ t,
        tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2 ≤ B := by
      intro N
      calc ∑ i ∈ t,
            tensorSobolevWeight (I := I) (M := M) i (σ + 1) * ((u N).coeff i) ^ 2
          = ∑ i ∈ t, (if i ∈ S N then
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hu_coeff, finiteEigenComboHs_coeff]
            by_cases hi : i ∈ S N <;> simp [hi]
        _ = ∑ i ∈ t ∩ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_ite_mem t (S N) _
        _ ≤ ∑ i ∈ S N,
              tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (c N i) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
              (fun i _ _ => mul_nonneg
                (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
        _ ≤ B := hbound N
    exact le_of_tendsto' hlim hle
  have hnn : (0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) ≤
      fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2 :=
    fun i => mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _)
  have hWp_summ : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (W.coeff i) ^ 2) :=
    summable_of_sum_le hnn hbd_finset
  set Wp : tensorHs (I := I) (M := M) g 0 2 (σ + 1) :=
    ⟨W.coeff, hWp_summ⟩ with hWp_def
  have hWp_coeff : ∀ i, Wp.coeff i = W.coeff i := by
    intro i; rw [hWp_def]
  have hWp_normSq_le : ‖Wp‖ ^ 2 ≤ B := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) Wp]
    simp only [hWp_coeff]
    exact Real.tsum_le_of_sum_le hnn hbd_finset
  have hsubcoeff : ∀ (a b : tensorHs (I := I) (M := M) g 0 2 (σ + 1)) i,
      (a - b).coeff i = a.coeff i - b.coeff i := by
    intro a b i
    simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
  have hCbd : ∀ N, ‖u N - Wp‖ ≤ 2 * Real.sqrt B := by
    intro N
    have huN : ‖u N‖ ≤ Real.sqrt B := by
      calc ‖u N‖ = Real.sqrt (‖u N‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt (hu_normSq_le N)
    have hWpn : ‖Wp‖ ≤ Real.sqrt B := by
      calc ‖Wp‖ = Real.sqrt (‖Wp‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hWp_normSq_le
    calc ‖u N - Wp‖ ≤ ‖u N‖ + ‖Wp‖ := norm_sub_le _ _
      _ ≤ Real.sqrt B + Real.sqrt B := add_le_add huN hWpn
      _ = 2 * Real.sqrt B := by ring
  have hcoeff0 : ∀ i, Tendsto (fun N => (u N - Wp).coeff i) atTop (𝓝 0) := by
    intro i
    have h := (hconv_coeff i).sub_const (W.coeff i)
    rw [sub_self] at h
    refine h.congr (fun N => ?_)
    rw [hsubcoeff (u N) Wp i, hWp_coeff i]
  have hlt : (σ : ℝ) < σ + 1 := by linarith
  have hsqrtB_nn : (0 : ℝ) ≤ 2 * Real.sqrt B := by positivity
  have hhelper := tensorHs_norm_tendsto_zero_of_coeff_tendsto_of_uniform
    (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ' := σ) (σ'' := σ + 1)
    hlt (fun N => u N - Wp) hsqrtB_nn hCbd hcoeff0
  have hincl_uN : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N) = finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ := by
    intro N
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hu_coeff N i]
  have hincl_Wp :
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hlt.le Wp = W := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply, hWp_coeff i]
  have hincl_eq : ∀ N,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hlt.le (u N - Wp) =
        finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W := by
    intro N
    rw [map_sub, hincl_uN N, hincl_Wp]
  have hNorm : Tendsto
      (fun N => ‖finiteEigenComboHs (I := I) (M := M) g (S N) (c N) σ - W‖)
      atTop (𝓝 0) := by
    refine hhelper.congr (fun N => ?_)
    rw [hincl_eq N]
  have hSub := tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  exact tendsto_sub_nhds_zero_iff.mp hSub

theorem galerkinForcing_field_eq_maxRegDuhamel_projTruncation
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) (g := g₀) (a : ℝ) T N
          (nemytskii (I := I) (M := M)
            (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
              a ha_super)
            (TimeSobolev.ofContinuousOn
              (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))))) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set hLipC := deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set gforceN := nemytskii (I := I) (M := M) hLipC VN with hgforceN_def
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  refine Lp.ext ?_
  have hLco := timeModeCoeff_coeFn (I := I) (M := M) VN i
  have hVco : ⇑VN =ᵐ[timeMeasure T]
      (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hRco := timeModeCoeff_coeFn (I := I) (M := M)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (VN s)) :=
    nemytskii_coeFn (I := I) (M := M) hLipC VN
  have hPNforcing : ⇑(timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) =ᵐ[timeMeasure T]
      (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) := by
    filter_upwards [hPNco, hPproj, hgco, hVco] with s hs1 hs2 hs3 hs4
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff, deTurckGalerkinForcing_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi, if_pos hi, hs3, hs4]
    · rw [if_neg hi, if_neg hi]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun t => U N t i := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_pos hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam
          (fun s => deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N s i) t :=
      perModeConv_timeL2_congr lam hPNforcing htmem'
    have hgp := galerkinPerMode_eq_perModeConv (I := I) (M := M) g₀ g_bg a ha_super hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hi htmem'
    rw [← hlam_def] at hgp
    rw [hgp, hcongr1]
    refine perModeConv_timeL2_congr lam ?_ htmem'
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
    rw [Set.IccExtend_of_mem hT.le _ hs]
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun _ => (0 : ℝ) := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_neg hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam (fun _ => (0 : ℝ)) t := by
      refine perModeConv_timeL2_congr lam ?_ htmem'
      filter_upwards [hPNforcing] with s hs
      rw [hs, deTurckGalerkinForcing_apply, if_neg hi]
    rw [hcongr1]
    unfold perModeConv
    simp

theorem galerkinODE_solution_unique
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V' t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hinit : ∀ i ∈ S, V 0 i = V' 0 i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    V t i = V' t i := by
  classical
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordField_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  set e := EuclideanSpace.equiv {i // i ∈ S} ℝ with he_def
  set γ : (ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) →
      ℝ → EuclideanSpace ℝ {i // i ∈ S} :=
    fun W t => e.symm (fun j => W t j.1) with hγ_def
  have hcomp_j : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ)
      (j : {i // i ∈ S}), (γ W t) j = W t j.1 := by
    intro W t j; rfl
  have hembed : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ),
      galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ W t) =
        finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2) := by
    intro W t
    apply tensorHs.ext
    funext i'
    rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
    by_cases hi' : i' ∈ S
    · rw [dif_pos hi', if_pos hi']; rfl
    · rw [dif_neg hi', if_neg hi']
  have hγcont : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ i ∈ S, ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T)) →
      ContinuousOn (γ W) (Set.Icc (0 : ℝ) T) := by
    intro W hWcont
    exact e.symm.continuous.comp_continuousOn (continuousOn_pi.2 (fun j => hWcont j.1 j.2))
  have hγderiv : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => W r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt
      (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1) =
        galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t) := by
      apply e.injective
      ext j
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change _ = (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) j
      rw [galerkinCoordField_apply, hcomp_j, hembed]
    rw [hval] at hcomp
    exact hcomp
  have hlip_univ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith Klip (galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
        (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})) :=
    fun _ _ => hKlip.lipschitzOnWith
  have heqOn : Set.EqOn (γ V) (γ V') (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => galerkinCoordField (I := I) (M := M) g₀ g_bg a S)
      (s := fun _ => (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})))
      hlip_univ (hγcont V hVcont) (fun s hs => hγderiv V hVderiv s hs)
      (fun _ _ => Set.mem_univ _) (hγcont V' hV'cont) (fun s hs => hγderiv V' hV'deriv s hs)
      (fun _ _ => Set.mem_univ _) ?_
    apply e.injective
    ext j
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact hinit j.1 j.2
  have := heqOn ht
  have hj : (γ V t) ⟨i, hi⟩ = (γ V' t) ⟨i, hi⟩ := by rw [this]
  rw [hcomp_j, hcomp_j] at hj
  exact hj

end Spectral
end Analysis
end DifferentialGeometry
end
end

section
open DifferentialGeometry.Analysis.Sobolev.CSupTensor
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

theorem fatou_weighted_sq_mass_le {ι : Type*} (S : ℕ → Finset ι)
    (hS : Tendsto S atTop atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, Tendsto (fun N => v N i) atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finset_sum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hKsub : K ⊆ S N := hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤ ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKsub
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact le_trans hmono (hbound N)
    exact le_of_tendsto hlim hev
  refine ⟨summable_of_sum_le hnn hpartial, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hpartial

private theorem continuousOn_galerkinForcingSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N hUcont
    have hcoeff : ContinuousOn
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))))
          (Set.Icc (0 : ℝ) T) :=
        (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.comp_continuousOn hN_cont
      simpa only [tensorHsCoeffL_apply] using hcoeff_cont
    refine hcoeff.congr (fun t _ => ?_)
    rw [deTurckGalerkinForcingSymm_apply, if_pos hi]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [deTurckGalerkinForcingSymm_apply, if_neg hi]

private theorem galerkinPerMode_eq_perModeConvSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U N t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N hUcont
      i).restrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N x i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) = -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      simp only [NNReal.coe_mk, le_refl]
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => U N s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hUcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hUderiv s hs i hi
    have hforce_eq : fForce s = deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -(lam) * U N s i + deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hUinit i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

private noncomputable def galerkinCoordFieldSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} → EuclideanSpace ℝ {i // i ∈ S} :=
  fun w => galerkinCoordDiag (I := I) (M := M) g₀ S w +
    galerkinCoordRestrict (I := I) (M := M) g₀ a S
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))

private lemma galerkinCoordFieldSymm_apply
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) (j : {i // i ∈ S}) :
    (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S w) j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j +
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)).coeff j.1 := by
  change (galerkinCoordDiag (I := I) (M := M) g₀ S w) j +
    (galerkinCoordRestrict (I := I) (M := M) g₀ a S _) j = _
  rw [galerkinCoordDiag_apply, galerkinCoordRestrict_apply]

private theorem galerkinCoordFieldSymm_lipschitzWith
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ K : ℝ≥0, LipschitzWith K (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S) := by
  obtain ⟨K₀, hK₀⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  refine ⟨‖galerkinCoordDiag (I := I) (M := M) g₀ S‖₊ +
    ‖galerkinCoordRestrict (I := I) (M := M) g₀ a S‖₊ * K₀ *
      ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S‖₊, ?_⟩
  have hdiag : LipschitzWith ‖galerkinCoordDiag (I := I) (M := M) g₀ S‖₊
      (galerkinCoordDiag (I := I) (M := M) g₀ S) :=
    (galerkinCoordDiag (I := I) (M := M) g₀ S).lipschitz
  have hnonlin : LipschitzWith
      (‖galerkinCoordRestrict (I := I) (M := M) g₀ a S‖₊ * K₀ *
        ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S‖₊)
      (fun w => galerkinCoordRestrict (I := I) (M := M) g₀ a S
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))) :=
    ((galerkinCoordRestrict (I := I) (M := M) g₀ a S).lipschitz.comp hK₀).comp
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S).lipschitz
  exact hdiag.add hnonlin

private theorem galerkinODE_solution_uniqueSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (_hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V' t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hinit : ∀ i ∈ S, V 0 i = V' 0 i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    V t i = V' t i := by
  classical
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordFieldSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  set e := EuclideanSpace.equiv {i // i ∈ S} ℝ with he_def
  set γ : (ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) →
      ℝ → EuclideanSpace ℝ {i // i ∈ S} :=
    fun W t => e.symm (fun j => W t j.1) with hγ_def
  have hcomp_j : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ)
      (j : {i // i ∈ S}), (γ W t) j = W t j.1 := by
    intro W t j; rfl
  have hembed : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ),
      galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ W t) =
        finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2) := by
    intro W t
    apply tensorHs.ext
    funext i'
    rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
    by_cases hi' : i' ∈ S
    · rw [dif_pos hi', if_pos hi']; rfl
    · rw [dif_neg hi', if_neg hi']
  have hγcont : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ i ∈ S, ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T)) →
      ContinuousOn (γ W) (Set.Icc (0 : ℝ) T) := by
    intro W hWcont
    exact e.symm.continuous.comp_continuousOn (continuousOn_pi.2 (fun j => hWcont j.1 j.2))
  have hγderiv : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => W r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt
      (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1) =
        galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t) := by
      apply e.injective
      ext j
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change _ = (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t)) j
      rw [galerkinCoordFieldSymm_apply, hcomp_j, hembed]
    rw [hval] at hcomp
    exact hcomp
  have hlip_univ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith Klip (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S)
        (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})) :=
    fun _ _ => hKlip.lipschitzOnWith
  have heqOn : Set.EqOn (γ V) (γ V') (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S)
      (s := fun _ => (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})))
      hlip_univ (hγcont V hVcont) (fun s hs => hγderiv V hVderiv s hs)
      (fun _ _ => Set.mem_univ _) (hγcont V' hV'cont) (fun s hs => hγderiv V' hV'deriv s hs)
      (fun _ _ => Set.mem_univ _) ?_
    apply e.injective
    ext j
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact hinit j.1 j.2
  have := heqOn ht
  have hj : (γ V t) ⟨i, hi⟩ = (γ V' t) ⟨i, hi⟩ := by rw [this]
  rw [hcomp_j, hcomp_j] at hj
  exact hj

private theorem galerkinForcing_field_eq_maxRegDuhamel_projTruncationSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M)
            (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
              (g_bg := g_bg)
              a ha_super)
            (TimeSobolev.ofContinuousOn
              (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))))) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set hLipC := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set gforceN := nemytskii (I := I) (M := M) hLipC VN with hgforceN_def
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  refine Lp.ext ?_
  have hLco := timeModeCoeff_coeFn (I := I) (M := M) VN i
  have hVco : ⇑VN =ᵐ[timeMeasure T]
      (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hRco := timeModeCoeff_coeFn (I := I) (M := M)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (VN s)) :=
    nemytskii_coeFn (I := I) (M := M) hLipC VN
  have hPNforcing : ⇑(timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) =ᵐ[timeMeasure T]
      (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i) := by
    filter_upwards [hPNco, hPproj, hgco, hVco] with s hs1 hs2 hs3 hs4
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff,
      deTurckGalerkinForcingSymm_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi, if_pos hi, hs3, hs4]
    · rw [if_neg hi, if_neg hi]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun t => U N t i := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_pos hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam
          (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i) t :=
      perModeConv_timeL2_congr lam hPNforcing htmem'
    have hgp := galerkinPerMode_eq_perModeConvSymm (I := I) (M := M) g₀ g_bg a ha_super hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hi htmem'
    rw [← hlam_def] at hgp
    rw [hgp, hcongr1]
    refine perModeConv_timeL2_congr lam ?_ htmem'
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
    rw [Set.IccExtend_of_mem hT.le _ hs]
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun _ => (0 : ℝ) := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_neg hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam (fun _ => (0 : ℝ)) t := by
      refine perModeConv_timeL2_congr lam ?_ htmem'
      filter_upwards [hPNforcing] with s hs
      rw [hs, deTurckGalerkinForcingSymm_apply, if_neg hi]
    rw [hcongr1]
    unfold perModeConv
    simp

private noncomputable def deTurckForceShortTimeSymm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  (quasilinear_maxreg_solution_of_nemytskii (I := I) (M := M) g₀ a
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) a ha_super)).choose

private theorem deTurckForceShortTimeSymm_eq (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super =
      min 1 (min (1 / (64 * (((deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I)
              (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super).choose_spec.choose : ℝ) + 1) ^ 2))
        ((deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super /
            (2 * (‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ + 1))) ^ 2)) :=
  (quasilinear_maxreg_solution_of_nemytskii (I := I) (M := M) g₀ a
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) a ha_super)).choose_spec.1

private theorem symmForce_contraction_coeff_le_half (C₁ C₂ : ℝ≥0) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2)) :
    (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T_le : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 : (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) ≤
        (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T_le h1T
      have hρnn : (0:ℝ) ≤ 1 / (16 * ((C₁ : ℝ) + 1)) := by positivity
      gcongr
    refine le_trans hle ?_
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  linarith

private noncomputable def deTurckForceRetractedMapSymm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  fun F => nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super) hT
    (recenteredBallRetraction (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
      (deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) F)

private theorem deTurckForceRetractedMapSymm_apply (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT F =
      nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
          (g_bg := g_bg) a ha_super) hT
        (recenteredBallRetraction (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
          (deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) F) := rfl

private theorem deTurckForceRetractedMapSymm_eq_of_mem_ball
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT F =
      nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
          (g_bg := g_bg) a ha_super) hT F := by
  rw [deTurckForceRetractedMapSymm_apply, recenteredBallRetraction_eq_self_of_mem
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hF)]

private theorem deTurckForceRetractedMapSymm_dist_le_half
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (x y : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    ‖deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT x -
        deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT y‖ ≤
      (1 / 2) * ‖x - y‖ := by
  classical
  rw [deTurckForceShortTimeSymm_eq (I := I) (M := M) g₀ g_bg a ha_super] at hTsh
  set hLip := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLip_def
  set hmix := deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hmix_def
  set C₁ : ℝ≥0 := hmix.choose with hC₁def
  set C₂ : ℝ≥0 := hmix.choose_spec.choose with hC₂def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hsingle := hmix.choose_spec.choose_spec
  have hρeq : ρ = 1 / (16 * ((C₁ : ℝ) + 1)) := rfl
  have hρpos : 0 < ρ := by rw [hρeq]; positivity
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_left _ _))
  set ρt := recenteredBallRetraction
    (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) ρ with hρt_def
  have hρt_norm : ∀ F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T,
      ‖ρt F‖ ≤ ρ := by
    intro F
    have hmem := recenteredBallRetraction_mapsTo
      (X := timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) (Set.mem_univ F)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hdist := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρpos.le (ρt x) (ρt y) (hρt_norm x) (hρt_norm y)
  have hretr : ‖ρt x - ρt y‖ ≤ ‖x - y‖ := by
    have h := (recenteredBallRetraction_lipschitzWith_one hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)).dist_le_mul x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    exact h
  have hcoef_nn : (0:ℝ) ≤ (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have hcoef_le : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
    rw [hρeq]
    exact symmForce_contraction_coeff_le_half C₁ C₂ hT.le hT1 hT_lo
  calc ‖deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT x -
          deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT y‖
      = ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT (ρt x) -
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT (ρt y)‖ := rfl
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) *
          ‖ρt x - ρt y‖ := hdist
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) *
          ‖x - y‖ := mul_le_mul_of_nonneg_left hretr hcoef_nn
    _ ≤ (1 / 2) * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef_le (norm_nonneg _)

private theorem deTurckForceRetractedMapSymm_lipschitzWith
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    LipschitzWith (1 / 2 : ℝ≥0)
      (deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num]
  exact deTurckForceRetractedMapSymm_dist_le_half (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 hTsh x y

private theorem nemytskiiMixedForcingMapSymm_norm_le_ballRadius
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (G : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hG : ‖G‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super) hT G‖ ≤
      deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  rw [deTurckForceShortTimeSymm_eq (I := I) (M := M) g₀ g_bg a ha_super] at hTsh
  set hLip := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLip_def
  set hmix := deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hmix_def
  set C₁ : ℝ≥0 := hmix.choose with hC₁def
  set C₂ : ℝ≥0 := hmix.choose_spec.choose with hC₂def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hsingle := hmix.choose_spec.choose_spec
  have hρeq : ρ = 1 / (16 * ((C₁ : ℝ) + 1)) := rfl
  have hρpos : 0 < ρ := by rw [hρeq]; positivity
  set M₀ : ℝ := ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hT_stay : T ≤ (ρ / (2 * (M₀ + 1))) ^ 2 :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcoef_nn : (0:ℝ) ≤ (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have hcoef_le : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
    rw [hρeq]
    exact symmForce_contraction_coeff_le_half C₁ C₂ hT.le hT1 hT_lo
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (M₀ + 1)) := by
      rw [show ρ / (2 * (M₀ + 1)) = Real.sqrt ((ρ / (2 * (M₀ + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (M₀ + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (M₀ + 1))) * (M₀ + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (M₀ + 1) ≠ 0 := by positivity
          field_simp
  have hΨ0 : ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤ Real.sqrt T * M₀ := by
    rw [nemytskiiMixedForcingMap_apply,
      maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT]
    refine timeL2_norm_le_of_ae_bound _ (by positivity) ?_
    have hcoe := nemytskii_coeFn (I := I) (M := M) hLip
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    have hzero := Lp.coeFn_zero (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (p := 2) (μ := timeMeasure T)
    filter_upwards [hcoe, hzero] with t ht htz
    rw [ht, htz, Pi.zero_apply]
  have hball := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρpos.le G (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hG
    (by rw [norm_zero]; exact hρpos.le)
  rw [sub_zero] at hball
  calc ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT G‖
      = ‖(nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)) +
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ +
          ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := norm_add_le _ _
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖ +
          Real.sqrt T * M₀ := add_le_add hball hΨ0
    _ ≤ (1 / 2) * ρ + ρ / 2 := by
        refine add_le_add ?_ hsqrtTM
        calc ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖
            ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ρ :=
              mul_le_mul_of_nonneg_left hG hcoef_nn
          _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hcoef_le hρpos.le
    _ = ρ := by ring

private theorem galerkinForcing_norm_le_ballRadiusSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    ‖nemytskii (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))‖ ≤
      deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  haveI hcount : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) h_compact
  set hLipC := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, deTurckForceBallRadiusSymm]; positivity
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set Ψ' := deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT with hΨ'_def
  have hκlt : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
    deTurckForceRetractedMapSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
  have hPΦ : ContractingWith (1 / 2 : ℝ≥0)
      (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
    refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    rw [Function.comp_apply, Function.comp_apply,
      show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num, dist_eq_norm, dist_eq_norm]
    calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
            timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
        = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
      _ ≤ ‖Ψ' x - Ψ' y‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ (1 / 2) * ‖x - y‖ := by
          have hd := hΨ'_lip.dist_le_mul x y
          rw [dist_eq_norm, dist_eq_norm, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at hd
          exact hd
  set yN := ContractingWith.fixedPoint
    (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') hPΦ with hyN_def
  have hyN_fix : (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') yN = yN :=
    ContractingWith.fixedPoint_isFixedPt hPΦ
  have hΨ'stay : ∀ z, ‖Ψ' z‖ ≤ ρ := by
    intro z
    rw [hΨ'_def, deTurckForceRetractedMapSymm_apply]
    refine nemytskiiMixedForcingMapSymm_norm_le_ballRadius (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ _ ?_
    have hmem := recenteredBallRetraction_mapsTo
      (X := timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) (Set.mem_univ z)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hyN_norm : ‖yN‖ ≤ ρ := by
    have h1 := hyN_fix
    rw [Function.comp_apply] at h1
    calc ‖yN‖ = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' yN)‖ := by rw [h1]
      _ ≤ ‖Ψ' yN‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ ρ := hΨ'stay yN
  set vN := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) yN with hvN_def
  have hΨ'yN : Ψ' yN = nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLipC hT yN := by
    rw [hΨ'_def,
      deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super hT yN
        hyN_norm]
  have hyN_eq : yN = timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
      (nemytskii (I := I) (M := M) hLipC vN) := by
    have h1 := hyN_fix
    rw [Function.comp_apply, hΨ'yN, nemytskiiMixedForcingMap_apply] at h1
    exact h1.symm
  set W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t with hW_def
  have hvN_coeff : ∀ i, (fun t => (vN t).coeff i) =ᵐ[timeMeasure T] (fun t => W t i) := by
    intro i
    exact timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT yN i
  have hyN_mode : ∀ j, ⇑(timeModeCoeff (I := I) (M := M) yN j) =ᵐ[timeMeasure T]
      (fun s => if j ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (vN s)).coeff j else 0) := by
    intro j
    have hco := timeModeCoeff_coeFn (I := I) (M := M)
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (nemytskii (I := I) (M := M) hLipC vN)) j
    have hproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M) hLipC vN)) =ᵐ[timeMeasure T]
        (fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N
          ((nemytskii (I := I) (M := M) hLipC vN) s)) :=
      ContinuousLinearMap.coeFn_compLpL _ (nemytskii (I := I) (M := M) hLipC vN)
    have hX := nemytskii_coeFn (I := I) (M := M) hLipC vN
    rw [hyN_eq]
    filter_upwards [hco, hproj, hX] with s hs1 hs2 hs3
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff]
    by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hj, if_pos hj, hs3]
    · rw [if_neg hj, if_neg hj]
  have hvN_eq_combo : ∀ᵐ s ∂(timeMeasure T),
      vN s = finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2) := by
    have hall : ∀ᵐ s ∂(timeMeasure T), ∀ j,
        (vN s).coeff j = (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2)).coeff j := by
      refine ae_all_iff.2 (fun j => ?_)
      by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
      · filter_upwards [hvN_coeff j] with s hs
        rw [hs, finiteEigenComboHs_coeff, if_pos hj]
      · filter_upwards [hvN_coeff j, hyN_mode j, ae_restrict_mem (μ := volume) measurableSet_Icc]
          with s hs hmode humem
        have humem' : s ∈ Set.Icc (0 : ℝ) T := humem
        rw [hs, finiteEigenComboHs_coeff, if_neg hj]
        change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
          (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s = 0
        have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
              (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j) (fun _ => (0 : ℝ)) s := by
          refine perModeConv_timeL2_congr _ ?_ humem'
          filter_upwards [hyN_mode j] with u hu
          rw [hu, if_neg hj]
        rw [hcongr]; unfold perModeConv; simp
    filter_upwards [hall] with s hs
    apply tensorHs.ext
    funext j
    exact hs j
  have hWcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T) := by
    intro i _
    exact continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) yN i) hT.le
  have hWderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => W r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    set fForce : ℝ → ℝ := Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W p.1) ((a : ℝ) + 2))).coeff i) with hfForce_def
    have hg_cont : ContinuousOn
      (fun s => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      refine (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super
        (fun _ => W) N hWcont i).congr (fun s _ => ?_)
      rw [deTurckGalerkinForcingSymm_apply, if_pos hi]
    have hfForce_cont : Continuous fForce := Continuous.Icc_extend' hg_cont.restrict
    have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
        fForce x = (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (W x) ((a : ℝ) + 2))).coeff i := by
      intro x hx
      rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
    have hWrep : ∀ s ∈ Set.Icc (0 : ℝ) T,
        W s i = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s := by
      intro s hs
      change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) yN i) u) s =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s
      refine perModeConv_timeL2_congr (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ hs
      filter_upwards [hyN_mode i, hvN_eq_combo, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with u hu1 hu2 humem'
      have humem : u ∈ Set.Icc (0 : ℝ) T := humem'
      rw [hu1, if_pos hi, hu2, hfForce_mem humem]
    have hIcc_mem : Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici t] t := by
      have h1 : Set.Ici t ∩ Set.Iic T ∈ 𝓝[Set.Ici t] t :=
        inter_mem_nhdsWithin (Set.Ici t) (Iic_mem_nhds ht.2)
      rw [Set.Ici_inter_Iic] at h1
      exact Filter.mem_of_superset h1 (Set.Icc_subset_Icc_left ht.1)
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hWi_eqEv : (fun r => W r i) =ᶠ[𝓝[Set.Ici t] t]
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce) :=
      Filter.eventuallyEq_of_mem hIcc_mem (fun r hr => hWrep r hr)
    have hderiv_pmc : HasDerivWithinAt
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce)
        (fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t) (Set.Ici t) t :=
      (perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i) hfForce_cont
        t).hasDerivWithinAt
    have hderiv_W := hderiv_pmc.congr_of_eventuallyEq hWi_eqEv (hWrep t htIcc)
    have hval_eq : fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i := by
      rw [hfForce_mem htIcc, ← hWrep t htIcc]; ring
    rw [hval_eq] at hderiv_W
    exact hderiv_W
  have hUderivN : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    have hd := hUderiv N t ht i hi
    rwa [deTurckGalerkinForcingSymm_apply, if_pos hi] at hd
  have hinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = W 0 i := by
    intro i hi
    rw [hUinit N i hi]
    change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) 0
    rw [perModeConv_zero_left]
  have hVN_eq_vN : VN = vN := by
    refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
    refine Lp.ext ?_
    have hL := timeModeCoeff_coeFn (I := I) (M := M) VN i
    have hVco : ⇑VN =ᵐ[timeMeasure T]
        (fun t => finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
      TimeSobolev.coeFn_ofContinuousOn _
    have hR := timeModeCoeff_coeFn (I := I) (M := M) vN i
    refine hL.trans (Filter.EventuallyEq.trans ?_ (hR.trans (hvN_coeff i)).symm)
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · filter_upwards [hVco, ae_restrict_mem (μ := volume) measurableSet_Icc] with t htV htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_pos hi]
      exact galerkinODE_solution_uniqueSymm (I := I) (M := M) g₀ g_bg a ha_super hT
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) W (hUcont N) hUderivN hWcont hWderiv
        hinit i hi htmem'
    · filter_upwards [hVco, hyN_mode i, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htV hmode htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_neg hi]
      change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t
      have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fun _ => (0 : ℝ)) t := by
        refine perModeConv_timeL2_congr _ ?_ htmem'
        filter_upwards [hyN_mode i] with s hs
        rw [hs, if_neg hi]
      rw [hcongr]; unfold perModeConv; simp
  have hfinal : nemytskii (I := I) (M := M) hLipC VN = Ψ' yN := by
    rw [hVN_eq_vN, hΨ'yN, nemytskiiMixedForcingMap_apply]
  rw [hfinal]
  exact hΨ'stay yN

private theorem galerkinForcing_tendsto_force_timeL2_ofProjFixedPointSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    Tendsto (fun N => TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i))
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hcontField : ∀ N, ContinuousOn
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N t) ((a : ℝ) + 2))) (Set.Icc (0 : ℝ) T) :=
    fun N => hK.continuous.comp_continuousOn
      (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
  have hfield : Tendsto (fun N => TimeSobolev.ofContinuousOn (hcontField N)) atTop (𝓝 gforce) := by
    have hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super := hTT₀
    set Ψ' := deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT with hΨ'_def
    have hκcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    have hκlt : (1 / 2 : ℝ≥0) < 1 := by
      rw [← NNReal.coe_lt_coe, hκcoe, NNReal.coe_one]; norm_num
    have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
      deTurckForceRetractedMapSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh
    have hcontr : ContractingWith (1 / 2 : ℝ≥0) Ψ' := ⟨hκlt, hΨ'_lip⟩
    have hPtendsto : ∀ x, Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N x)
        atTop (𝓝 x) := fun x => timeL2EigenProj_tendsto (I := I) (M := M) g₀ (a : ℝ) T x
    have hPΦ : ∀ N, ContractingWith (1 / 2 : ℝ≥0)
        (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
      intro N
      refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
      rw [Function.comp_apply, Function.comp_apply, hκcoe, dist_eq_norm, dist_eq_norm]
      calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
              timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
          = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
        _ ≤ ‖Ψ' x - Ψ' y‖ := by
            refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
            exact mul_le_of_le_one_left (norm_nonneg _)
              (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
        _ ≤ (1 / 2) * ‖x - y‖ :=
            deTurckForceRetractedMapSymm_dist_le_half (I := I) (M := M) g₀ g_bg a ha_super hT hT1
              hTsh x y
    have hFP := DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction
      hcontr (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) hPtendsto hPΦ
    have hgforce_fix : Ψ' gforce = gforce := by
      rw [hΨ'_def, deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT gforce hgforce, nemytskiiMixedForcingMap_apply]
      refine Lp.ext ?_
      exact (nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a
          ha_super)
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)).trans hforce.symm
    have hFstar_eq : ContractingWith.fixedPoint Ψ' hcontr = gforce :=
      (ContractingWith.fixedPoint_unique hcontr hgforce_fix).symm
    rw [hFstar_eq] at hFP
    have hgforceN_eq : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        nemytskii (I := I) (M := M)
          (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
            a ha_super)
          (TimeSobolev.ofContinuousOn
            (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))) := by
      intro N
      refine Lp.ext ?_
      have h1 := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
      have h2 := nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a
          ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
      have h3 := TimeSobolev.coeFn_ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      rw [ht1, ht2, ht3]
    have hball : ∀ N, ‖TimeSobolev.ofContinuousOn (hcontField N)‖ ≤
        deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      rw [hgforceN_eq N]
      exact galerkinForcing_norm_le_ballRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh
        U
        hUinit hUcont hUderiv N
    have hxN_ball : ∀ N, ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))‖ ≤
        deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      refine le_trans ?_ (hball N)
      refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
    have hgforceN_Ψ' : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        Ψ' (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))) := by
      intro N
      rw [hΨ'_def, deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT _ (hxN_ball N), nemytskiiMixedForcingMap_apply, hgforceN_eq N]
      congr 1
      exact galerkinForcing_field_eq_maxRegDuhamel_projTruncationSymm (I := I) (M := M) g₀ g_bg a
        ha_super hT U hUinit hUcont hUderiv N
    have hxN_fix : ∀ N, ContractingWith.fixedPoint
          (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') (hPΦ N) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N)) := by
      intro N
      refine (ContractingWith.fixedPoint_unique (hPΦ N) ?_).symm
      change (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ')
          (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
            (TimeSobolev.ofContinuousOn (hcontField N))) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))
      rw [Function.comp_apply, ← hgforceN_Ψ' N]
    have hxN_tendsto : Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))) atTop (𝓝 gforce) :=
      hFP.congr (fun N => hxN_fix N)
    have hcomp := (hΨ'_lip.continuous.tendsto gforce).comp hxN_tendsto
    rw [hgforce_fix] at hcomp
    exact hcomp.congr (fun N => (hgforceN_Ψ' N).symm)
  have hmode : Tendsto
      (fun N => timeModeCoeff (I := I) (M := M) (TimeSobolev.ofContinuousOn (hcontField N)) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) :=
    (((tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).compLpL 2
      (timeMeasure T)).continuous.tendsto
      gforce).comp hfield
  refine hmode.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N :=
    eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
  refine Lp.ext ?_
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (TimeSobolev.ofContinuousOn (hcontField N)) i
  have hF := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
  have hG := TimeSobolev.coeFn_ofContinuousOn
    (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i)
  refine hL.trans (Filter.EventuallyEq.trans ?_ hG.symm)
  filter_upwards [hF] with t ht
  rw [ht, deTurckGalerkinForcingSymm_apply, if_pos hi]

theorem galerkinSol_tendsto_solField_perModeConvSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => U N t i) atTop
      (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hcontF : ∀ N, ContinuousOn
      (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i)
      (Set.Icc (0 : ℝ) T) :=
    fun N => continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a (by omega) U N
      (hUcont N) i
  set fseq : ℕ → timeL2 ℝ T := fun N => TimeSobolev.ofContinuousOn (hcontF N) with hfseq_def
  have hposit : Tendsto fseq atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) :=
    galerkinForcing_tendsto_force_timeL2_ofProjFixedPointSymm (I := I) (M := M) g₀ g_bg a
      (by omega) hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
  have hstab : Tendsto (fun N => perModeConv lam (fun s => (fseq N) s) t) atTop
      (𝓝 (perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) :=
    tendsto_perModeConv_of_tendsto_timeL2 lam hlam_nn hposit ht
  have hmem_ev : ∀ᶠ N in atTop, i ∈ eigenIdxFinset (I := I) (M := M) g₀ N := by
    obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
  refine hstab.congr' ?_
  filter_upwards [hmem_ev] with N hiN
  have hae : (fun s => (fseq N) s) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
        deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i) := by
    have hcoe : ⇑(fseq N) =ᵐ[timeMeasure T]
        fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := by
      rw [hfseq_def]
      exact TimeSobolev.coeFn_ofContinuousOn (hcontF N)
    have hcoe' : (fun s => (fseq N) s) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
        fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := hcoe
    filter_upwards [hcoe', ae_restrict_mem measurableSet_Icc] with s hs hsmem
    rw [hs, Set.IccExtend_of_mem hT.le _ hsmem]
  have hperm_eq :
      perModeConv lam (fun s => (fseq N) s) t =
        perModeConv lam (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i)) t :=
    perModeConv_timeL2_congr lam hae ht
  have hstagea :=
    galerkinPerMode_eq_perModeConvSymm (I := I) (M := M) g₀ g_bg a (by omega) hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hiN ht
  rw [← hlam_def] at hstagea
  rw [hperm_eq, ← hstagea]

theorem deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ := by
  classical
  obtain ⟨U, hUcont, hUderiv, hUinit_coeff⟩ :=
    deTurckGalerkin_solution_existsSymm (I := I) (M := M) g₀ g_bg a (by omega)
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) hT.le
  have hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0 := by
    intro N i hi
    rw [hUinit_coeff N i hi]; rfl
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScaleSymm (I := I) (M := M) g₀ g_bg a ha_super
      (T := T) U hUinit
  have hUmass : ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U)
      (Fseq := deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB
  intro σ
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - (a : ℝ))
  have hσk : σ ≤ (a : ℝ) + (k : ℝ) := by linarith
  obtain ⟨Bound, hBound⟩ := hUmass k
  refine ⟨Bound, fun t ht => ?_⟩
  set wσ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ with hwσ
  have hwσ_nn : ∀ i, 0 ≤ wσ i := fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have hweight_dom : ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) := by
    intro i
    exact Real.rpow_le_rpow_of_exponent_le
      (one_le_one_add_lambda (I := I) (M := M) i) hσk
  have hpartialbound : ∀ N,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤ Bound := by
    intro N
    have hle : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_right (hweight_dom i) (sq_nonneg _)
    have hgal : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
      hBound N t ht
    have hgal_eq : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := rfl
    rw [hgal_eq] at hgal
    exact le_trans hle hgal
  have hconv : ∀ i,
      Tendsto (fun N => U N t i) atTop
        (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)) :=
    fun i => galerkinSol_tendsto_solField_perModeConvSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i t ht
  have hfatou := fatou_weighted_sq_mass_le
    (eigenIdxFinset (I := I) (M := M) g₀) (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    wσ hwσ_nn (fun N i => U N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)
    (fun i => hconv i) Bound hpartialbound
  exact hfatou

end Spectral
end Analysis
end DifferentialGeometry

end
end

section
open DifferentialGeometry.Analysis.Sobolev.CSupTensor
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance measurableSpaceE_forcingCoordinates : MeasurableSpace E := borel E
private local instance borelSpaceE_forcingCoordinates : BorelSpace E := ⟨rfl⟩
private local instance measurableSpaceM_forcingCoordinates : MeasurableSpace M := borel M
private local instance borelSpaceM_forcingCoordinates : BorelSpace M := ⟨rfl⟩

theorem maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hk⟩ :=
    deTurckForcing_finiteOrderSmoothDriver (I := I) (M := M)
      g₀ g_bg a ha_super hT gforce hforce hspatial
  choose F hF_smooth hF_mass hF_ae using hk
  set f0 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ := F 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) d ⊆ closure (interior (Set.Icc (0 : ℝ) d)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd_pos)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (F k i) (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro k i
    have hae : (F k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (f0 i) :=
      (hF_ae k i).symm.trans (hF_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hF_smooth k i).continuous).continuousOn ((hF_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hF_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) d) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hd_pos (hf0_smoothOn i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) d →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) d) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨d, hd_pos, hd_le, ψ, hψ_smooth, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hF_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (ψ i) t = iteratedDeriv j (F j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
        ((hF_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  · intro i
    have hf0ψ : (f0 i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (ψ i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
      exact hψ_eqOn i ht
    exact (hF_ae 0 i).trans hf0ψ

section SymmSCoefficientBlockTransfer

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ccTensor02Symm domDomCongrSection tensorResolventHilbertEigenbasisSigma
    tensorResolventHilbertEigenbasisSigma_apply eigenvectorSmooth_toL2)

private noncomputable def eigenBlockFinset (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
  Finset.univ.map ⟨Sigma.mk i.1, sigma_mk_injective⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma mem_eigenBlockFinset (g₀ : SmoothRiemannianMetric I M)
    {i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2} :
    j ∈ eigenBlockFinset (I := I) (M := M) g₀ i ↔ j.1 = i.1 := by
  constructor
  · intro hj
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hj
    rfl
  · intro hj
    obtain ⟨μ, kk⟩ := j
    have hμ : μ = i.1 := hj
    subst hμ
    exact Finset.mem_map.mpr ⟨kk, Finset.mem_univ kk, rfl⟩

private noncomputable def swapEigenCoeff (g₀ : SmoothRiemannianMetric I M)
    (i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g₀ i))) j

private lemma eigenbasis_eq_toL2_eigenSmooth_loc (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g₀) i =
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (eigenSmooth (I := I) (M := M) g₀ i) := by
  rw [tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀) i]
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i).symm

private lemma tensorL2_eq_of_coeff_eq (g₀ : SmoothRiemannianMetric I M)
    {U V : TensorL2 0 2 g₀}
    (h : ∀ k, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) U k =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) V k) : U = V := by
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀)).repr.injective
  ext k
  exact h k

open scoped Classical in
private lemma tensorL2Coeff_sum_smul_basis (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (k : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (∑ j ∈ S, c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) j) k =
      (if k ∈ S then c k else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, inner_sum]
  have h_term : ∀ j ∈ S,
      ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) k,
        c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) j⟫_ℝ =
      (if k = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (hCompact (I := I) (M := M) g₀)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth k j]
    by_cases h : k = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hkS : k ∈ S
  · rw [Finset.sum_eq_single k]
    · simp [hkS]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm)]
    · intro h
      exact absurd hkS h
  · rw [if_neg hkS, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hkS (by rw [h]; exact hj))]

private lemma toL2_swap_eigenSmooth_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g₀ i)) =
      ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        swapEigenCoeff (I := I) (M := M) g₀ i j •
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g₀) j := by
  classical
  refine tensorL2_eq_of_coeff_eq (I := I) (M := M) g₀ (fun k => ?_)
  rw [tensorL2Coeff_sum_smul_basis (I := I) (M := M) g₀ _ _ k]
  by_cases hk : k ∈ eigenBlockFinset (I := I) (M := M) g₀ i
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk]
    refine tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne (I := I) (M := M) g₀ i k ?_
    exact fun h => hk ((mem_eigenBlockFinset (I := I) (M := M) g₀).mpr h.symm)

private lemma sum_sq_swapEigenCoeff_le_one (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
      (swapEigenCoeff (I := I) (M := M) g₀ i j) ^ 2 ≤ 1 := by
  classical
  set Y : TensorL2 0 2 g₀ := SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (eigenSmooth (I := I) (M := M) g₀ i)) with hY_def
  have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀)).orthonormal
  have hb := horth.sum_inner_products_le (𝕜 := ℝ)
    (s := eigenBlockFinset (I := I) (M := M) g₀ i) Y
  have hnorm : ‖Y‖ = 1 := by
    rw [hY_def]
    exact (orthonormal_toL2_swap_eigenSmooth (I := I) (M := M) g₀).1 i
  calc ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        (swapEigenCoeff (I := I) (M := M) g₀ i j) ^ 2
      = ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          ‖⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
              (hCompact (I := I) (M := M) g₀) j, Y⟫_ℝ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show swapEigenCoeff (I := I) (M := M) g₀ i j =
            tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) Y j from rfl,
          tensorL2Coeff_eq_inner, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖Y‖ ^ 2 := hb
    _ = 1 := by rw [hnorm, one_pow]

private lemma tensorL2Coeff_toL2_swap_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X)) i =
      ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        swapEigenCoeff (I := I) (M := M) g₀ i j *
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j := by
  classical
  rw [tensorL2Coeff_eq_inner, eigenbasis_eq_toL2_eigenSmooth_loc (I := I) (M := M) g₀ i,
    SmoothCcTensor.inner_toL2,
    ← inner_domDomCongrSection_swap (I := I) (M := M) g₀
      (eigenSmooth (I := I) (M := M) g₀ i) X,
    ← SmoothCcTensor.inner_toL2, toL2_swap_eigenSmooth_eq_blockSum (I := I) (M := M) g₀ i,
    sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, ← tensorL2Coeff_eq_inner]

private lemma tensorL2Coeff_toL2_symmS_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (ccTensor02Symm (I := I) (M := M) g₀ X)) i
          =
      (1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) i +
        ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          swapEigenCoeff (I := I) (M := M) g₀ i j *
            tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j) := by
  have htoL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (ccTensor02Symm (I := I) (M := M) g₀ X) =
      (1 / 2 : ℝ) • (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X +
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X)) := by
    simp only [ccTensor02Symm]
    rw [map_smul, map_add]
  rw [htoL2, tensorL2Coeff_smul, tensorL2Coeff_add,
    tensorL2Coeff_toL2_swap_eq_blockSum (I := I) (M := M) g₀ X i]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorSobolevWeight_eq_of_block (g₀ : SmoothRiemannianMetric I M)
    {i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2} (h : j.1 = i.1) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) j σ = tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  have hlam : TensorEigenIdx.lambda (I := I) (M := M) j =
      TensorEigenIdx.lambda (I := I) (M := M) i := by
    unfold TensorEigenIdx.lambda
    rw [h]
  rw [hlam]

noncomputable def symmCoeffPath (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (φ i t + ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
    swapEigenCoeff (I := I) (M := M) g₀ i j * φ j t)

lemma symmCoeffPath_contDiff (g₀ : SmoothRiemannianMetric I M)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} {n : WithTop ℕ∞}
    (hφ : ∀ i, ContDiff ℝ n (φ i)) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContDiff ℝ n (symmCoeffPath (I := I) (M := M) g₀ φ i) := by
  unfold symmCoeffPath
  exact contDiff_const.mul ((hφ i).add
    (ContDiff.sum fun j _ => contDiff_const.mul (hφ j)))

lemma symmCoeffPath_realizes (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (X : SmoothCcTensor g₀ 0 2) {t : ℝ}
    (hX : ∀ j, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j = φ j t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (ccTensor02Symm (I := I) (M := M) g₀ X)) i
          =
      symmCoeffPath (I := I) (M := M) g₀ φ i t := by
  rw [tensorL2Coeff_toL2_symmS_eq_blockSum (I := I) (M := M) g₀ X i, hX i]
  unfold symmCoeffPath
  congr 2
  exact Finset.sum_congr rfl fun j _ => by rw [hX j]

private lemma iteratedDeriv_finsetSum_const_mul {ι' : Type*} (s : Finset ι')
    (c : ι' → ℝ) (f : ι' → ℝ → ℝ) (k : ℕ)
    (hf : ∀ j, ContDiff ℝ (k : ℕ) (f j)) (t : ℝ) :
    iteratedDeriv k (fun u => ∑ j ∈ s, c j * f j u) t =
      ∑ j ∈ s, c j * iteratedDeriv k (f j) t := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty]; exact iteratedDeriv_fun_const_zero
  | cons b s hb ih =>
    have hfun : (fun u => ∑ j ∈ Finset.cons b s hb, c j * f j u) =
        fun u => c b * f b u + ∑ j ∈ s, c j * f j u := by
      funext u
      rw [Finset.sum_cons]
    rw [hfun, iteratedDeriv_fun_add ((contDiff_const.mul (hf b)).contDiffAt)
        ((ContDiff.sum fun j _ => contDiff_const.mul (hf j)).contDiffAt),
      Finset.sum_cons, ih]
    congr 1
    exact iteratedDeriv_const_mul_field (c b) (f b)

lemma iteratedDeriv_symmCoeffPath (g₀ : SmoothRiemannianMetric I M)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} (k : ℕ)
    (hφ : ∀ j, ContDiff ℝ (k : ℕ) (φ j))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ) :
    iteratedDeriv k (symmCoeffPath (I := I) (M := M) g₀ φ i) t =
      (1 / 2 : ℝ) * (iteratedDeriv k (φ i) t +
        ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          swapEigenCoeff (I := I) (M := M) g₀ i j * iteratedDeriv k (φ j) t) := by
  unfold symmCoeffPath
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add ((hφ i).contDiffAt)
    ((ContDiff.sum fun j _ => contDiff_const.mul (hφ j)).contDiffAt),
    iteratedDeriv_finsetSum_const_mul _ _ _ k hφ t]

lemma symmCoeffPath_spectralMass (g₀ : SmoothRiemannianMetric I M)
    {d : ℝ} (hd_pos : 0 < d)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} (k : ℕ)
    (hφ : ∀ j, ContDiff ℝ (k : ℕ) (φ j)) (τ : ℝ)
    (hmτ : ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i τ * (iteratedDeriv k (φ i) t) ^ 2 ≤ B i)
    (hmτρ : ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i
            (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) *
          (iteratedDeriv k (φ i) t) ^ 2 ≤ B i) :
    ∃ B' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B' ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i τ *
          (iteratedDeriv k (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B' i := by
  classical
  obtain ⟨B₁, hB₁s, hB₁⟩ := hmτ
  obtain ⟨B₂, hB₂s, hB₂⟩ := hmτρ
  set ρ : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρ_def
  have hρ_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρ := by
    rw [hρ_def]; linarith
  have hB₂nn : ∀ j, 0 ≤ B₂ j := fun j =>
    le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) j _) (sq_nonneg _))
      (hB₂ j 0 ⟨le_rfl, hd_pos.le⟩)
  set K : ℝ := ∑' j, B₂ j with hK_def
  refine ⟨fun i => (1 / 2 : ℝ) * B₁ i +
    (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i (-ρ) * K), ?_, ?_⟩
  · exact (hB₁s.mul_left _).add
      (((tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_right K).mul_left _)
  · intro i t ht
    rw [iteratedDeriv_symmCoeffPath (I := I) (M := M) g₀ k hφ i t]
    set x : ℝ := iteratedDeriv k (φ i) t with hx_def
    set y : ℝ := ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
      swapEigenCoeff (I := I) (M := M) g₀ i j * iteratedDeriv k (φ j) t with hy_def
    have hw_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i τ
    have hsq : ((1 / 2 : ℝ) * (x + y)) ^ 2 ≤ (1 / 2) * x ^ 2 + (1 / 2) * y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have h1 : tensorSobolevWeight (I := I) (M := M) i τ * x ^ 2 ≤ B₁ i := hB₁ i t ht
    have h2 : tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i (-ρ) * K := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (eigenBlockFinset (I := I) (M := M) g₀ i)
        (fun j => swapEigenCoeff (I := I) (M := M) g₀ i j)
        (fun j => iteratedDeriv k (φ j) t)
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          (iteratedDeriv k (φ j) t) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have hy2 : y ^ 2 ≤ ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          (iteratedDeriv k (φ j) t) ^ 2 :=
        le_trans hcs (mul_le_of_le_one_left hsum_nn
          (sum_sq_swapEigenCoeff_le_one (I := I) (M := M) g₀ i))
      have hstep : tensorSobolevWeight (I := I) (M := M) i τ *
          ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i, (iteratedDeriv k (φ j) t) ^ 2 =
          tensorSobolevWeight (I := I) (M := M) i (-ρ) *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
              tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
                (iteratedDeriv k (φ j) t) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjw : tensorSobolevWeight (I := I) (M := M) j (τ + ρ) =
            tensorSobolevWeight (I := I) (M := M) i (τ + ρ) :=
          tensorSobolevWeight_eq_of_block (I := I) (M := M) g₀
            ((mem_eigenBlockFinset (I := I) (M := M) g₀).mp hj) (τ + ρ)
        have hsplit : tensorSobolevWeight (I := I) (M := M) i τ =
            tensorSobolevWeight (I := I) (M := M) i (-ρ) *
              tensorSobolevWeight (I := I) (M := M) i (τ + ρ) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) (τ + ρ)]
          congr 1
          ring
        rw [hjw, hsplit]
        ring
      have hblock : ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
            (iteratedDeriv k (φ j) t) ^ 2 ≤ K := by
        refine le_trans (Finset.sum_le_sum fun j _ => hB₂ j t ht) ?_
        exact hB₂s.sum_le_tsum _ fun j _ => hB₂nn j
      calc tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i τ *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i, (iteratedDeriv k (φ j) t) ^ 2 :=
            mul_le_mul_of_nonneg_left hy2 hw_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (-ρ) *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
              tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
                (iteratedDeriv k (φ j) t) ^ 2 := hstep
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * K :=
            mul_le_mul_of_nonneg_left hblock
              (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
    calc tensorSobolevWeight (I := I) (M := M) i τ * ((1 / 2 : ℝ) * (x + y)) ^ 2
        ≤ tensorSobolevWeight (I := I) (M := M) i τ *
          ((1 / 2) * x ^ 2 + (1 / 2) * y ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nn
      _ = (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i τ * x ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * B₁ i +
          (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i (-ρ) * K) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))

theorem exists_smoothCcPath_realizing_coeff (g₀ : SmoothRiemannianMetric I M)
    {d₂ : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i) :
    ∃ F : ℝ → SmoothCcTensor g₀ 0 2, ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hsum_pt : ∀ t, t ∈ Set.Icc (0 : ℝ) d₂ →
      ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2) := by
    intro t ht σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => hBle i t ht) hBs
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  set ct : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => φ i t with hct_def
  have hreconstruct : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = φ i t := by
    intro t ht
    obtain ⟨B0, hB0s, hB0le⟩ := hmass0 0 le_rfl
    set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
      tensorHs_of_spectralMass_majorant (I := I) (M := M) (ct t) B0 hB0s
        (fun i => by
          have := hB0le i t ht
          simpa [hct_def] using this) with hv0_def
    set u : TensorL2 0 2 g₀ :=
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
    have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = φ i t := by
      intro i
      rw [hu_def, tensorHsToL2_tensorL2Coeff]
      simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff, hct_def]
    have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
      intro σ hσ
      refine (hsum_pt t ht σ hσ).congr (fun i => ?_)
      rw [hu_coeff i]
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
      allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
    refine ⟨S, fun i => ?_⟩
    have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
      rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
          = (S : TensorL2 0 2 g₀) from rfl, hS]
    rw [hSL2, hu_coeff i]
  choose! S₀ hS₀ using hreconstruct
  exact ⟨S₀, hS₀⟩

private theorem deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (X : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) X‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) X) =
      deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ X)) := by
  classical
  obtain ⟨hp_pos, hp_lt, hp_ball⟩ := Classical.choose_spec
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)
  have hδ_lt : (Classical.choose (deTurckSobolevNHa2_exists_of_super
      (I := I) (M := M) g₀ a ha_super)).2 < 1 :=
    lt_of_le_of_lt hp_lt (de_turck_remainder_contraction_threshold_lt_one_of_ne_zero (Module.finrank ℝ E))
  rw [deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super X hδ_lt
    (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ X (hp_ball X hball))
      hball]
  exact (deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super
    (ccTensor02Symm (I := I) (M := M) g₀ X) hδ_lt
    (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ X (hp_ball X hball))
    (le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) X)
      hball)).symm


private theorem deTurckForcing_jetSpectralMass_preservingSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (_hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (_hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ d₂)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ d₂ ∧
        ∀ i, (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨hφ_smooth, hφ_mass⟩ := hφ
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  obtain ⟨F, hF_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g₀ φ hmass0
  have hφ'_smooth : ∀ i, ContDiff ℝ ∞ (symmCoeffPath (I := I) (M := M) g₀ φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g₀ hφ_smooth
  have hφ'_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B i := by
    intro j τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g₀ hd₂_pos j
      (fun j' => (hφ_smooth j').of_le (mod_cast le_top)) τ
      (hφ_mass j τ hτ)
      (hφ_mass j (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  have hwF : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t htall htmem
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, smoothCcToTensorHs_coeff, hF_coeff t htmem j]
  have hw'_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (F t))‖ ≤
        deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super := by
    filter_upwards [hw_ball, hwF] with t hwball_t hwF_t
    refine le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (F t)) ?_
    rw [← hwF_t]
    exact hwball_t
  have hw'_ae : ∀ i, (fun t => (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (F t))).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        symmCoeffPath (I := I) (M := M) g₀ φ i := by
    intro i
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
    rw [smoothCcToTensorHs_coeff]
    exact symmCoeffPath_realizes (I := I) (M := M) g₀ φ (F t)
      (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M) g₀ g_bg a ha_super
      hd₂_pos
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)))
      hw'_ball (symmCoeffPath (I := I) (M := M) g₀ φ) ⟨hφ'_smooth, hφ'_mass⟩ hw'_ae
  refine ⟨ψ, hψ_ctrl, fun i => ?_⟩
  filter_upwards [hψ_ae i, hw_ball, hwF] with t hψt hwball_t hwF_t
  have hballF : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1 := by
    rw [← hwF_t]
    exact hwball_t
  rw [hwF_t, deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS (I := I) (M := M)
    g₀ g_bg a ha_super (F t) hballF]
  exact hψt


private theorem deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {d₂ : ℝ} (hd₂_pos : 0 < d₂)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (k : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i) := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  obtain ⟨F, hF_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g₀ φ hmass0
  have hφ'_smooth : ∀ i, ContDiff ℝ (k : ℕ) (symmCoeffPath (I := I) (M := M) g₀ φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g₀ hφ_smooth
  have hφ'_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B i := by
    intro j hjk τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g₀ hd₂_pos j
      (fun j' => (hφ_smooth j').of_le (mod_cast hjk)) τ
      (hφ_mass j hjk τ hτ)
      (hφ_mass j hjk (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  have hwF : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t htall htmem
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, smoothCcToTensorHs_coeff, hF_coeff t htmem j]
  have hw'_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (F t))‖ ≤
        deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super := by
    filter_upwards [hw_ball, hwF] with t hwball_t hwF_t
    refine le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (F t)) ?_
    rw [← hwF_t]
    exact hwball_t
  have hw'_ae : ∀ i, (fun t => (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (F t))).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        symmCoeffPath (I := I) (M := M) g₀ φ i := by
    intro i
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
    rw [smoothCcToTensorHs_coeff]
    exact symmCoeffPath_realizes (I := I) (M := M) g₀ φ (F t)
      (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
    deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super hd₂_pos
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)))
      hw'_ball k (symmCoeffPath (I := I) (M := M) g₀ φ) hφ'_smooth hφ'_mass hw'_ae
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  filter_upwards [hψ_ae i, hw_ball, hwF] with t hψt hwball_t hwF_t
  have hballF : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1 := by
    rw [← hwF_t]
    exact hwball_t
  rw [hwF_t, deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS (I := I) (M := M)
    g₀ g_bg a ha_super (F t) hballF]
  exact hψt


private theorem deTurckForcing_finiteOrderSmoothDriverSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
        (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
        (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
              tensorSobolevWeight (I := I) (M := M) i τ *
                  (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
        (∀ i, (fun t => (gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hs_cont, hs_mass, hball, hcoeff_id⟩ :=
    deTurckForcing_solCoeff_continuous_smallTimeBase (I := I) (M := M)
      g₀ a ha_super hT gforce hspatial
  choose c hc_cont hc_ae using hs_cont
  have hae_d : ∀ i, c i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le) (hc_ae i)
  have hcont_pmc : ∀ i, ContinuousOn
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    (continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le).mono (Set.Icc_subset_Icc le_rfl hd_le)
  have heqOn_d : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (ne_of_lt hd_pos) (hae_d i) (hc_cont i).continuousOn (hcont_pmc i)
  refine ⟨d, hd_pos, hd_le, ?_⟩
  have hsub : Set.Icc (0 : ℝ) d ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hd_le
  have hforce_coeff : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  have hgforce_tmc : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  intro k
  induction k with
  | zero =>
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hd_pos
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball 0
        c
        (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
        (fun j hj τ hτ => by
          obtain rfl := Nat.le_zero.mp hj
          obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
          refine ⟨B, hBs, fun i t ht => ?_⟩
          rw [iteratedDeriv_zero, heqOn_d i ht]
          exact hBle i t ht)
        (fun i => (hcoeff_id i).trans (hae_d i).symm)
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g₀ hd_pos.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (fk i) :=
        (hgforce_tmc i).symm.trans (hfk_ae i)
      have hbridge : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
        exact perModeConv_timeL2_congr (T := d) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hfk_tmc ht
      exact (hcoeff_id i).trans hbridge
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hd_pos
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball (k + 1)
        (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
        hφ_cont hφ_mass hw_coeff
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩


theorem maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hk⟩ :=
    deTurckForcing_finiteOrderSmoothDriverSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT gforce hforce hspatial
  choose F hF_smooth hF_mass hF_ae using hk
  set f0 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ := F 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) d ⊆ closure (interior (Set.Icc (0 : ℝ) d)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd_pos)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (F k i) (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro k i
    have hae : (F k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (f0 i) :=
      (hF_ae k i).symm.trans (hF_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hF_smooth k i).continuous).continuousOn ((hF_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hF_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) d) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hd_pos (hf0_smoothOn i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) d →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) d) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨d, hd_pos, hd_le, ψ, hψ_smooth, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hF_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (ψ i) t = iteratedDeriv j (F j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
        ((hF_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  · intro i
    have hf0ψ : (f0 i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (ψ i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
      exact hψ_eqOn i ht
    exact (hF_ae 0 i).trans hf0ψ

end SymmSCoefficientBlockTransfer


theorem maxRegSolField_parabolicInterior_jetSpectralMassSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a (by omega)) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm (I := I) (M := M)
      g₀ g_bg a (by omega) hT gforce hforce
      (deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm (I := I) (M := M)
        g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_top (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) (hf_smooth i)
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le_d₀, hball_W⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₀_pos f
      (fun i => (hf_smooth i).continuous) (B := B0) hB0_sum
      (fun i s hs => by
        have h := hB0_le i s hs
        rwa [iteratedDeriv_zero] at h)
      (deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a (by omega))
  have hd₂_le : d₂ ≤ T := le_trans hd₂_le_d₀ hd₀_le
  have hd₂_le_d₀' : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) d₀ :=
    Set.Icc_subset_Icc le_rfl hd₂_le_d₀
  refine ⟨d₂, hd₂_pos, hd₂_le, φ, ⟨hφ_smooth, ?_⟩, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₀) hd₀_pos.le f hf_smooth hf_mass j τ hτ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t (hd₂_le_d₀' ht)
  · have hsolcoeff_ae : ∀ i,
        (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
      intro i
      have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hd₂_le
      have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) hT hc gforce i)
      have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
        have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
              (fun s => (gforce s).coeff i) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
            (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
        exact htmc.trans
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
            hd₂_le_d₀' (hf_ae i))
      have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
        exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hforce_ae ht
      exact hstep1.trans hstep2
    have hcoeff_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t :=
      (MeasureTheory.ae_all_iff).2 hsolcoeff_ae
    filter_upwards [hcoeff_eq, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht_coeff ht_mem
    refine hball_W t ht_mem
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t) ?_
    intro i
    exact ht_coeff i
  · intro i
    have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hd₂_le
    have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
          (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) hT hc gforce i)
    have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
      have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun s => (gforce s).coeff i) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
      exact htmc.trans
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
          hd₂_le_d₀' (hf_ae i))
    have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
      rw [hφ_def]
      exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
        hforce_ae ht
    exact hstep1.trans hstep2


private theorem deTurckForcing_smoothForcingDriverSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    maxRegSolField_parabolicInterior_jetSpectralMassSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckForcing_jetSpectralMass_preservingSymm (I := I) (M := M)
      g₀ g_bg a (by omega) hT hd₂_pos hd₂_le
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨d₂, hd₂_pos, hd₂_le, ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₂_le
  have hforce_coeff : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  exact hforce_coeff.trans (hψ_ae i)


private theorem deTurckForcing_fixedPoint_coeff_smooth_and_massSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (c i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] c i) := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothForcingDriverSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₀ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₀_le
  have hbridge : (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)]
        (fun t => (gforce t).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
  exact hbridge.trans (hf_ae i)


theorem deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] g i) :=
  deTurckForcing_fixedPoint_coeff_smooth_and_massSymm (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce


theorem deTurckForcing_smoothCoordinate_aeTimeJetSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, fun i => ?_⟩
  have htmc : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd₂_le) ?_
    exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  exact htmc.trans (hg_ae i)

end Spectral
end Analysis
end DifferentialGeometry

end
end

section
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance measurableSpaceE_jointSmoothness : MeasurableSpace E := borel E
private local instance borelSpaceE_jointSmoothness : BorelSpace E := ⟨rfl⟩
private local instance measurableSpaceM_jointSmoothness : MeasurableSpace M := borel M
private local instance borelSpaceM_jointSmoothness : BorelSpace M := ⟨rfl⟩


theorem deTurckForcing_smoothTimeCoordinateFieldSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothCoordinate_aeTimeJetSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 (a : ℝ) (Nat.cast_nonneg a)
  have hslab_sum : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (a : ℝ) * (f i t) ^ 2) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a : ℝ)) (sq_nonneg _)
    · have := hB_le i t ht
      rwa [iteratedDeriv_zero] at this
  set F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂ then
      ⟨fun i => f i t, hslab_sum t ht⟩ else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t := by
    intro t ht i
    simp only [hF_def, dif_pos ht]
  refine ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, ?_, hF_coeff⟩
  have hjoint : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ i, (gforce t).coeff i = f i t :=
    (MeasureTheory.ae_all_iff).2 hf_ae
  have hrestrict : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      t ∈ Set.Icc (0 : ℝ) d₂ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  filter_upwards [hjoint, hrestrict] with t ht_eq ht_mem
  refine tensorHs.ext ?_
  funext i
  rw [ht_eq i, hF_coeff t ht_mem i]


theorem deTurckForcing_smoothTimeCoordinateFamilySymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coeff⟩ :=
    deTurckForcing_smoothTimeCoordinateFieldSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
      hTT₀ gforce hforce hgforce
  have hF_coord_cont : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂) := by
    intro i
    refine ContinuousOn.congr (f := fun t => f i t) ?_ ?_
    · exact (hf_smooth i).continuous.continuousOn
    · intro t ht
      exact hF_coeff t ht i
  exact ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩

end Spectral
end Analysis
end DifferentialGeometry
end
end

section
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.Analysis.Spectral

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorL2_ext_of_tensorL2Coeff_jsmooth
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator
      (Analysis.Parabolic.TensorSpectral.tensorResolventL2 (I := I) (M := M) g r s))
    {S T : TensorL2 r s g}
    (h : ∀ i, tensorL2Coeff (I := I) (M := M) h_compact S i =
      tensorL2Coeff (I := I) (M := M) h_compact T i) :
    S = T := by
  classical
  set b := Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact with hb
  apply b.repr.injective
  ext i
  have hS : (b.repr S) i = tensorL2Coeff (I := I) (M := M) h_compact S i := rfl
  have hT : (b.repr T) i = tensorL2Coeff (I := I) (M := M) h_compact T i := rfl
  rw [hS, hT, h i]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem ccTensorBilinSymm_zero_apply_jsmooth (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) x v w = 0 := by
  have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
    (zero_smul ℝ _).symm
  rw [h0, ccTensorBilinSymm_smul]
  ring

private theorem realizedSolField_continuousOn_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {T₁ : ℝ} (_hT₁_pos : 0 < T₁)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) := by
  classical
  set σ : ℝ := (a : ℝ) + 2 with hσ_def
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hp_def
  set σ' : ℝ := σ + p with hσ'_def
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmodemass 0 σ' (by
    rw [hσ'_def, hσ_def, hp_def]; positivity)
  have hmass : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      tensorSobolevWeight (I := I) (M := M) i σ' * (φ i t) ^ 2 ≤ Cmaj i := by
    intro i t ht
    have := hCmaj_le i t ht
    rwa [iteratedDeriv_zero] at this
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hcoeff t ht i
  have hwthr : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ := by
    rw [hσ'_def, hp_def]; ring_nf; linarith
  exact tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g₀ hwthr
    (s := Set.Icc (0 : ℝ) T₁)
    (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ σ (F t)) φ hcoeff'
    (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum hmass

private theorem metricPerturbationPathily_flowDeriv_of_repr
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
      SmoothCcTensor g₀ 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    {T : ℝ} (_hT : 0 < T) (_hT1 : T ≤ 1)
    {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (_hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hForceRepr : ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Nsec (F t) hδ_lt (hδ t))) i) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
        (F_RHS
          (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
        (Set.Ici 0) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  set φ' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i s => f i s - TensorEigenIdx.lambda (I := I) (M := M) i * φ i s with hφ'_def
  have hφ_deriv : ∀ i (s : ℝ), HasDerivAt (φ i) (φ' i s) s := by
    intro i s
    exact perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i)
      (hf_smooth i).continuous s
  have hφ_mass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    exact perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
  have hcoeff : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) i = φ i s := by
    intro s hs i
    rw [h_pin s hs, tensorHsToL2_tensorL2Coeff]
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hid := hf_id s hs_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  have hu_mem : ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s) := by
    intro s hs σ hσ
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (fun τ hτ => ?_) σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj⟩ := hφ_mass 0 τ hτ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hCmaj_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i τ) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hCmaj i s hs_icc
      rw [iteratedDeriv_zero] at h
      rw [hcoeff s hs i]
      exact h
  have hforcing := hForceRepr
  obtain ⟨m, hm_lossy⟩ : ∃ m : ℕ, 2 * Module.finrank ℝ E + 4 ≤ m :=
    ⟨2 * Module.finrank ℝ E + 4, le_rfl⟩
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g₀ 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) :=
    tensorEigen_summable_negpow (I := I) (M := M) g₀ (sW : ℝ) hsW_gt
  intro t ht x v w
  obtain ⟨C, hC_pos, hC_bd⟩ :=
    abs_eigenBilinScalar_le (I := I) (M := M) g₀ m hm_lossy x v w
  set K : ℝ := Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hψ_bd : ∀ i, |eigenBilinScalar (I := I) g₀ x v w i| ≤
      (C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) := by
    intro i
    have := hC_bd i
    rw [hK_def]
    calc |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) *
            (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := this
      _ = C * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) := by ring
  have hprod_summable : ∀ (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ)) *
          (c i) ^ 2) →
      Summable (fun i => c i * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro c hc_sum
    have hdom : Summable (fun i =>
        (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ)) *
            (c i) ^ 2)) +
          (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) :=
      ((hc_sum.mul_left (C * K)).mul_left (1 / 2)).add
        ((hweyl.mul_left (C * K)).mul_left (1 / 2))
    refine Summable.of_norm_bounded hdom (fun i => ?_)
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (m : ℝ) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ)
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |c i| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |c i| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((m : ℝ) + (sW : ℝ)))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((m : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          have hAB : (C * K) * (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((m : ℝ) + (sW : ℝ)))) *
              Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              (C * K) * ((|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
                ((m : ℝ) + (sW : ℝ)))) *
                Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by ring
          rw [hAB]
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|c i| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((m : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
              ((m : ℝ) + (sW : ℝ)) * (c i) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring
  have hsum_series : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      Summable (fun i => φ i s * eigenBilinScalar (I := I) g₀ x v w i) := by
    intro s hs
    refine hprod_summable (fun i => φ i s) ?_
    obtain ⟨B, hB_sum, hB_le⟩ := hφ_mass 0 ((m : ℝ) + (sW : ℝ)) (by positivity)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _)
    · have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
      have h := hB_le i s hs_icc
      rwa [iteratedDeriv_zero] at h
  obtain ⟨Bφ', hBφ'_sum, hBφ'_le⟩ := hφ_mass 1 ((m : ℝ) + (sW : ℝ)) (by positivity)
  set u_bd : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
      (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))
    with hu_bd_def
  have hu_bd_sum : Summable u_bd :=
    ((hBφ'_sum.mul_left (C * K)).mul_left (1 / 2)).add
      ((hweyl.mul_left (C * K)).mul_left (1 / 2))
  have hφ'_term_bd : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ‖φ' i s * eigenBilinScalar (I := I) g₀ x v w i‖ ≤ u_bd i := by
    intro i s hs
    have hs_icc : s ∈ Set.Icc (0 : ℝ) d₂F := ⟨hs.1, le_trans hs.2 hT₁_le_d2F⟩
    have hCK_nn : 0 ≤ C * K := mul_nonneg hC_pos.le hK_nn
    have hwasW_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hwneg_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hsqrt_split : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) =
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ))) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      rw [← Real.sqrt_mul hwasW_nn]
      congr 1
      unfold tensorSobolevWeight
      rw [← Real.rpow_add (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i))]
      congr 1; ring
    have hbd1 : tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + (sW : ℝ)) *
        (φ' i s) ^ 2 ≤ Bφ' i := by
      have h := hBφ'_le i s hs_icc
      rwa [iteratedDeriv_one, show deriv (φ i) s = φ' i s from (hφ_deriv i s).deriv] at h
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ' i s| * |eigenBilinScalar (I := I) g₀ x v w i|
        ≤ |φ' i s| * ((C * K) * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (hψ_bd i) (abs_nonneg _)
      _ = (C * K) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((m : ℝ) + (sW : ℝ)))) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) := by
          rw [hsqrt_split]; ring
      _ ≤ (C * K) * ((1 / 2) * ((|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
            ((m : ℝ) + (sW : ℝ)))) ^ 2 +
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)))) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCK_nn
          nlinarith [sq_nonneg (|φ' i s| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i
              ((m : ℝ) + (sW : ℝ))) -
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))]
      _ = (1 / 2 : ℝ) * ((C * K) * (tensorSobolevWeight (I := I) (M := M) i
            ((m : ℝ) + (sW : ℝ)) * (φ' i s) ^ 2)) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [mul_pow, Real.sq_sqrt hwasW_nn, Real.sq_sqrt hwneg_nn, sq_abs]; ring
      _ ≤ (1 / 2 : ℝ) * ((C * K) * Bφ' i) +
            (1 / 2 : ℝ) * ((C * K) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (le_refl _)
          exact mul_le_mul_of_nonneg_left hbd1 hCK_nn
  have hG_deriv : HasDerivWithinAt
      (fun s : ℝ => ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩
    refine hasDerivWithinAt_tsum
      (f := fun i s => φ i s * eigenBilinScalar (I := I) g₀ x v w i)
      (f' := fun i s => φ' i s * eigenBilinScalar (I := I) g₀ x v w i)
      (u := u_bd) (s := Set.Icc (0 : ℝ) T₁)
      (fun i z _hz => ?_) (fun i z hz => hφ'_term_bd i z hz) hu_bd_sum
      (convex_Icc 0 T₁) ht_icc (hsum_series t ht_icc) ht_icc
    exact ((hφ_deriv i z).hasDerivWithinAt).mul_const _
  have hG_eq : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
      ccTensorBilinSymm (I := I) g₀ (F s) x v w =
        ∑' i, φ i s * eigenBilinScalar (I := I) g₀ x v w i := by
    intro s hs
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F s)) (hu_mem s hs) (F s)
      (SmoothCcTensor.toL2_apply (F s)) x v w ?_
    · rw [heig]
      exact tsum_congr (fun i => by rw [hcoeff s hs i])
    · refine (hsum_series s hs).congr (fun i => ?_)
      rw [hcoeff s hs i]
  have hG_deriv' : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Icc (0 : ℝ) T₁) t := by
    refine hG_deriv.congr (fun s hs => hG_eq s hs) ?_
    exact hG_eq t ⟨ht.1, le_of_lt ht.2⟩
  have hIci : HasDerivWithinAt
      (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
      (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) (Set.Ici (0 : ℝ)) t := by
    have hmem : Set.Icc (0 : ℝ) T₁ ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
      have hsub : Set.Ici (0 : ℝ) ∩ Set.Iio T₁ ⊆ Set.Icc (0 : ℝ) T₁ :=
        fun s hs => ⟨hs.1, le_of_lt hs.2⟩
      exact Filter.mem_of_superset
        (inter_mem_nhdsWithin _ (Iio_mem_nhds ht.2)) hsub
    exact (hG_deriv'.mono_of_mem_nhdsWithin hmem)
  have hval : (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
      F_RHS
        (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w := by
    set gDT := tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t) with hgDT_def
    set R : SmoothCcTensor g₀ 0 2 :=
      Nsec (F t) hδ_lt (hδ t) + rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t)
      with hR_def
    have hR_split : R = Nsec (F t) hδ_lt (hδ t) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t) := rfl
    have hcoord : ∀ i, φ' i t =
        tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i := by
      intro i
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, le_of_lt ht.2⟩
      have hf_coord := hforcing t ht i
      have hraw : tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (F t))) i =
          -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i :=
        tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ hc (F t) i
      rw [hcoeff t ht_icc i] at hraw
      rw [hR_split, ContinuousLinearMap.map_add, tensorL2Coeff_add, ← hf_coord, hraw, hφ'_def]
      ring
    have hR_mem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vH : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vH =
            SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R := by
      intro σ hσ
      refine allHs_of_weighted_summable_pub (I := I) (M := M) g₀
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) (fun τ _hτ => ?_) σ hσ
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ τ R hc
    have hR_sum : Summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
        eigenBilinScalar (I := I) g₀ x v w i) := by
      refine (hprod_summable (fun i => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i) ?_)
      exact smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
        ((m : ℝ) + (sW : ℝ)) R hc
    have heig := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g₀
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) hR_mem R
      (SmoothCcTensor.toL2_apply R) x v w hR_sum
    rw [show (∑' i, φ' i t * eigenBilinScalar (I := I) g₀ x v w i) =
        ∑' i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) R) i *
            eigenBilinScalar (I := I) g₀ x v w i from
      tsum_congr (fun i => by rw [hcoord i])]
    rw [← heig, hR_def]
    exact hRepr (F t) hδ_lt (hδ t) x v w
  rw [← hval]
  exact hIci

private theorem metricPerturbationPathily_jointChartGramSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) :=
  jointChartGramSmooth_of_spectralSmooth_timeSmooth (I := I) (M := M)
    g hT T_rep hδ_lt hδ φ hφ_smooth hcoeff hmodemass

private theorem forcingSmoothTimeCoordsSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
      (F : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)),
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (⇑gforce =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] F) ∧
      (∀ i, ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i, (F t).coeff i = f i t) :=
  deTurckForcing_smoothTimeCoordinateFamilySymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1
    hTT₀ gforce hforce hgforce

private theorem forcingSmoothCoordsRealizeSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (_htrace : timeH1.trace0 _ T u = 0) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, f, F, hf_smooth, hf_mass, hF_rep, hF_coord_cont, hF_coeff⟩ :=
    forcingSmoothTimeCoordsSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce
      hgforce
  have hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
    intro i
    have hrep_coeff : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (F t).coeff i) := hF_rep.fun_comp (fun S => S.coeff i)
    refine hrep_coeff.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
    exact hF_coeff s hs i
  refine ⟨d₂, hd₂_pos, hd₂_le, f, hf_smooth, hf_mass, ?_, hforce_coord⟩
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  intro t ht i
  rw [hduh, tensorHsToL2_tensorL2Coeff (Nat.cast_nonneg a)]
  have hid := carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
    (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hT hd₂_pos hd₂_le h_compact gforce
    (F := F) hF_coord_cont hF_rep i ht
  rw [hid]
  refine perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
    (f₁ := Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F (p : ℝ)).coeff i))
    (f₂ := f i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with s hs
  rw [Set.IccExtend_of_mem hd₂_pos.le _ hs, hF_coeff s hs i]

private theorem realizedSol_solField_smallnessHorizon_Ha2Symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (htrace : timeH1.trace0 _ T u = 0)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ := by
  classical
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, _⟩ :=
    forcingSmoothCoordsRealizeSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce hgforce htrace
  obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le, hbound⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₂F_pos f
      (fun i => (hf_smooth i).continuous)
      (B := B) hB_sum
      (fun i s hs => by
        have h := hB_le i s hs
        rwa [iteratedDeriv_zero] at h)
      hR₀
  refine ⟨d₂, hd₂_pos, le_trans hd₂_le hd₂F_le, ?_⟩
  intro t ht S hS
  have ht_d2F : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hd₂_le⟩
  set W : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S with hW_def
  have hWcoeff : ∀ i, W.coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t := by
    intro i
    rw [hW_def, smoothCcToTensorHs_coeff, hS, ← hf_id t ht_d2F i]
  have := hbound t ht W hWcoeff
  rwa [hW_def] at this

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm) in
private theorem realizedForcingCoord_eq_smoothNSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T)
    (_hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a ha_super)
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a ha_super)).choose)
    {T₁ : ℝ} (hT₁_pos : 0 < T₁) (hT₁_le : T₁ ≤ T)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (_hd₂F_le : d₂F ≤ T) (hT₁_le_d2F : T₁ ≤ d₂F)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hforce_coord : ∀ i, (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)] f i)
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (Nat.cast_nonneg a) (timeH1.toFun u t))
    (hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
        (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a
          ha_super)).1) :
    ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
              (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t)
                (hδ t)))) i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ i, tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [h_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
  have hfield_cont : ContinuousOn
      (fun t : ℝ => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))
      (Set.Icc (0 : ℝ) T₁) :=
    realizedSolField_continuousOn_smoothCcToTensorHs (I := I) (M := M) g₀ a hT₁_pos F φ hφ_smooth
      hcoeff hmodemass
  have hu_eq : u = recentredCarrier (I := I) (M := M) hT
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce := by
    refine timeH1.ext ?_ ?_
    · have hinit : u.init = 0 := by
        rw [← timeH1.trace0_apply (X := tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) (T := T) u]
        exact htrace
      rw [hinit]
      simp only [recentredCarrier, timeH1.init_mk]
    · rw [hduh]
      simp only [recentredCarrier, timeH1.deriv_mk]
  have hfield_ae : (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)) := by
    have hper : ∀ i, ∀ᵐ t ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T₁)),
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)).coeff i := by
      intro i
      have hsub : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hT₁_le
      have hsol := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        hsub
        (maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
          (h_compact := hc) (a := (a : ℝ)) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i)
      filter_upwards [hsol, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        measurableSet_Icc]
        with t htsol htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := hsub htmem
      rw [htsol, tensorHs.zero_coeff, zero_add]
      have hcarr : (timeH1.toFun u t).coeff i =
          ∫ s in (0 : ℝ)..t, ((maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce).deriv s).coeff i := by
        rw [hu_eq]
        exact recentredCarrier_toFun_coeff (I := I) (M := M) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce i htmem'
      rw [← hcarr, smoothCcToTensorHs_coeff, h_pin t htmem, tensorHsToL2_tensorL2Coeff]
    rw [← MeasureTheory.ae_all_iff] at hper
    filter_upwards [hper] with t ht
    exact tensorHs.ext (funext fun i => ht i)
  intro t₀ ht₀ i
  set RHS : ℝ → ℝ := fun t => tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t)))) i
    with hRHS_def
  have hRHS_smoothN : ∀ t, RHS t =
      (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)) hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t)
          (hδ t))).coeff i := by
    intro t; rw [hRHS_def, deTurckSmoothN_coeff]
  have heqN : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i = RHS t := by
    intro t ht
    rw [hRHS_smoothN t,
      deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super (F t)
        hδ_lt (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ (F t) (hδ t))
          (hball t ht)]
  obtain ⟨KN, hKN⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hRHS_cont : ContinuousOn RHS (Set.Ico (0 : ℝ) T₁) := by
    have hcomp : ContinuousOn
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i)
        (Set.Icc (0 : ℝ) T₁) := by
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)))
          (Set.Icc (0 : ℝ) T₁) :=
        hKN.continuous.comp_continuousOn hfield_cont
      exact (coeffCLM (I := I) (M := M) (g := g₀) (r := 0) (s := 2) (σ := (a : ℝ)) i).continuous
        |>.comp_continuousOn hN_cont
    refine (hcomp.mono Set.Ico_subset_Icc_self).congr (fun t ht => ?_)
    exact (heqN t ht).symm
  have hLHS_cont : ContinuousOn (f i) (Set.Ico (0 : ℝ) T₁) :=
    (hf_smooth i).continuous.continuousOn
  have hae : (f i) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
    (Set.Ico (0 : ℝ) T₁)] RHS := by
    have h1 : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂F)]
        (fun t => (gforce t).coeff i) := (hforce_coord i).symm
    have h2 : (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      hforce.fun_comp (fun S => S.coeff i)
    have hsub₁ : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hT₁_le
    have hsub₁F : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) d₂F :=
      Set.Icc_subset_Icc le_rfl hT₁_le_d2F
    have h1' : f i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (gforce t).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁F h1
    have h2' : (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub₁ h2
    have h12 : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
      h1'.trans h2'
    have h3 : (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      hfield_ae.fun_comp (fun S =>
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a S).coeff i)
    have hchain : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Icc (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      h12.trans h3
    have hchain' : f i =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ico (0 : ℝ) T₁)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t))).coeff i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
        Set.Ico_subset_Icc_self hchain
    refine hchain'.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ico]
      with t ht
    exact heqN t ht
  have heqOn : Set.EqOn (f i) RHS (Set.Ico (0 : ℝ) T₁) :=
    MeasureTheory.Measure.eqOn_Ico_of_ae_eq (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      hae hLHS_cont hRHS_cont
  exact heqOn ht₀

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm) in
theorem deTurckRicci_forcingBootstrap_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) :
    ∀ {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
        (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
          (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
            (g_bg := g_bg) a (by omega))
          (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
            (g_bg := g_bg) a (by omega))).choose)
        (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
        (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
        (hforce : gforce =ᵐ[timeMeasure T]
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
        (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
        (htrace : timeH1.trace0 _ T u = 0),
      ∃ (d₂F : ℝ), 0 < d₂F ∧ d₂F ≤ T ∧
        ∃ (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ),
          (∀ i, ContDiff ℝ ∞ (f i)) ∧
          (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
            ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
              ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
                tensorSobolevWeight (I := I) (M := M) i τ *
                    (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
            tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                  (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
              perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) ∧
          ∃ (R₀ : ℝ), 0 < R₀ ∧
            (∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
              ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
                SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
                  tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (Nat.cast_nonneg a) (timeH1.toFun u t) →
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀) ∧
            (∀ {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
                (_hT₁_le_d2F : T₁ ≤ d₂F)
                (Ffam : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
                (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
                  (ccTensorBilinSymm (I := I) g₀ (Ffam t)) δ)
                (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
                  SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Ffam t) =
                    tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                      (Nat.cast_nonneg a) (timeH1.toFun u t))
                (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Ffam t)‖ ≤ R₀),
              ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
                f i t = tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                      (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
                        (ccTensor02Symm (I := I) (M := M) g₀ (Ffam t)) hδ_lt
                        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀
                          (Ffam t) (hδ t)))) i) := by
  classical
  intro T hT hT1 hTT₀ u gforce hduh hforce hgforce htrace
  obtain ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, hforce_coord⟩ :=
    forcingSmoothCoordsRealizeSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀ u gforce
      hduh hforce hgforce htrace
  refine ⟨d₂F, hd₂F_pos, hd₂F_le, f, hf_smooth, hf_mass, hf_id, ?_⟩
  set R₀ : ℝ := (Classical.choose
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1 with hR₀_def
  have hR₀_pos : 0 < R₀ :=
    (Classical.choose_spec
      (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a (by omega))).1
  refine ⟨R₀, hR₀_pos, ?_, ?_⟩
  · exact realizedSol_solField_smallnessHorizon_Ha2Symm (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ u gforce hduh hforce hgforce htrace hR₀_pos
  · intro T₁ hT₁_pos hT₁_le hT₁_le_d2F Ffam δ hδ_lt hδ h_pin hball
    exact realizedForcingCoord_eq_smoothNSymm (I := I) (M := M) g₀ g_bg a (by omega)
      hT hTT₀ hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u gforce hduh hforce htrace
      Ffam hδ_lt hδ f hf_id hf_smooth hf_mass hforce_coord h_pin hball

theorem maxreg_solution_jointly_smooth_representative_of_nemytskii
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_eq : a = 4 * Module.finrank ℝ E + 10)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
      SmoothCcTensor g₀ 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0)
    {d₂F : ℝ} (hd₂F_pos : 0 < d₂F) (hd₂F_le : d₂F ≤ T)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) d₂F, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    {R₀ : ℝ}
    (hHorizon : ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀)
    (hForceRepr_fam : ∀ {T₁ : ℝ} (_hT₁_pos : 0 < T₁) (_hT₁_le : T₁ ≤ T)
        (_hT₁_le_d2F : T₁ ≤ d₂F)
        (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
        (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t))
        (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀),
      ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
        f i t = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (Nsec (F t) hδ_lt (hδ t))) i) :
    ∃ (T₁ : ℝ), 0 < T₁ ∧ T₁ ≤ T ∧
      ∃ (F : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T₁,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T₁
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  have hu0 : timeH1.toFun u 0 = 0 := by rw [timeH1.toFun_zero, hinit]
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hφ_cont : ∀ i, Continuous (φ i) := fun i => (hφ_smooth i).continuous
  have hf_endpoint_sum : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (f i s) ^ 2) := by
    intro c hc t ht
    obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 c hc
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hB_sum.mul_left d₂F)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i c
      have hcont_sq : Continuous (fun s => (f i s) ^ 2) := ((hf_smooth i).continuous).pow 2
      have htint : (∫ s in (0 : ℝ)..t, (f i s) ^ 2) ≤ ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hd₂F_pos.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set hcont_sq.integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      have hbig : tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 ≤ d₂F * B i := by
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2)
            MeasureTheory.volume 0 d₂F :=
          (hcont_sq.const_mul _).intervalIntegrable 0 d₂F
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) MeasureTheory.volume 0 d₂F :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..d₂F,
              tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2
            ≤ ∫ _s in (0 : ℝ)..d₂F, B i := by
          refine intervalIntegral.integral_mono_on hd₂F_pos.le hi_lhs hi_const ?_
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        exact hmono
      calc tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..t, (f i s) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..d₂F, (f i s) ^ 2 :=
            mul_le_mul_of_nonneg_left htint hwt_nn
        _ ≤ d₂F * B i := hbig
  have hF₀_exists : ∀ t ∈ Set.Icc (0 : ℝ) d₂F,
      ∃ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    obtain ⟨uDuh, huDuh_coeff, huDuh_mem⟩ :=
      duhamel_into_all_tensorHs (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (t := t) ht.1 h_compact f (fun i => (hf_smooth i).continuous)
        (fun c hc => hf_endpoint_sum c hc t ht)
    have hval : uDuh = tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
      refine tensorL2_ext_of_tensorL2Coeff_jsmooth (I := I) (M := M) h_compact (fun i => ?_)
      rw [huDuh_coeff i]
      exact (hf_id t ht i).symm
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              h_compact hσ v = uDuh := huDuh_mem
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) uDuh hmem
    refine ⟨S, ?_⟩
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = (S : TensorL2 0 2 g₀) from rfl,
      hS, hval]
  choose F₀ hF₀ using hF₀_exists
  set Fdef : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) d₂F then F₀ t ht else 0 with hFdef_def
  have hFdef_pin : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) d₂F),
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Fdef t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    simp only [hFdef_def, dif_pos ht]
    exact hF₀ t ht
  have ha_lossy : 2 * Module.finrank ℝ E + 4 ≤ a := by omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order (I := I) (M := M) g₀ a
      ha_lossy
  have hcontU : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T) :=
    timeH1.continuousOn_toFun u
  have hwithin : ContinuousWithinAt (timeH1.toFun u) (Set.Icc (0 : ℝ) T) 0 :=
    hcontU.continuousWithinAt ⟨le_refl 0, hT.le⟩
  rw [Metric.continuousWithinAt_iff] at hwithin
  obtain ⟨d, hd_pos, hd⟩ := hwithin (1 / (2 * C)) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le, hd₂⟩ := hHorizon
  set T₁ : ℝ := min (min (min T (d / 2)) d₂) d₂F with hT₁_def
  have hT₁_pos : 0 < T₁ := lt_min (lt_min (lt_min hT (by positivity)) hd₂_pos) hd₂F_pos
  have hT₁_le : T₁ ≤ T :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hT₁_le_d2 : T₁ ≤ d₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hT₁_le_d2F : T₁ ≤ d₂F := min_le_right _ _
  have hT₁_le_d : T₁ ≤ d / 2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Ioc (0 : ℝ) T₁ then Fdef t else 0 with hF_def
  have hF_zero : F 0 = 0 := by
    simp only [hF_def]
    rw [if_neg]
    intro hmem; exact absurd hmem.1 (lt_irrefl 0)
  have hF_small : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) (1 / 2) := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) T₁
    · have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le⟩
      have ht_icc_d2F : t ∈ Set.Icc (0 : ℝ) d₂F :=
        ⟨ht.1.le, le_trans ht.2 hT₁_le_d2F⟩
      have hpin := hFdef_pin t ht_icc_d2F
      have heq : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t) =
          timeH1.toFun u t := by
        refine tensorHs.ext (funext (fun i => ?_))
        rw [smoothCcToTensorHs_coeff, hpin, tensorHsToL2_tensorL2Coeff]
      have hdist : dist t (0 : ℝ) < d := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact lt_of_le_of_lt (le_trans ht.2 hT₁_le_d) (by linarith)
      have hnorm_lt : dist (timeH1.toFun u t) (timeH1.toFun u 0) < 1 / (2 * C) :=
        hd ht_icc hdist
      have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤
          1 / (2 * C) := by
        rw [hu0, dist_eq_norm, sub_zero] at hnorm_lt
        rw [heq]
        exact hnorm_lt.le
      intro x v w
      rw [hFt]
      refine le_trans (hC (Fdef t) x v w) ?_
      have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤ 1 / 2 := by
        calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖
            ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hnorm_le hC_pos.le
          _ = 1 / 2 := by field_simp
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
        mul_nonneg hsv_nn hsw_nn
      calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
          = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
              (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
        _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
            mul_le_mul_of_nonneg_right hCN_le hmul_nn
        _ = (1 / 2 : ℝ) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
    · have hFt : F t = 0 := by simp only [hF_def, if_neg ht]
      intro x v w
      rw [hFt, ccTensorBilinSymm_zero_apply_jsmooth]
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      rw [abs_zero]
      positivity
  have hF_pin : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hF_zero, hu0]
      simp only [map_zero]
    · have ht_ioc : t ∈ Set.Ioc (0 : ℝ) T₁ := ⟨h0, ht.2⟩
      have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht_ioc]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
      rw [hFt]
      exact hFdef_pin t ht_icc
  have hF_cont : ContinuousOn
      (fun t : ℝ => (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)))
      (Set.Icc (0 : ℝ) T₁) := by
    have hcontU₁ : ContinuousOn (timeH1.toFun u) (Set.Icc (0 : ℝ) T₁) :=
      hcontU.mono (Set.Icc_subset_Icc le_rfl hT₁_le)
    have hcomp : ContinuousOn
        (fun t : ℝ => tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t)) (Set.Icc (0 : ℝ) T₁) :=
      (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a)).continuous.comp_continuousOn hcontU₁
    refine hcomp.congr (fun t ht => ?_)
    exact hF_pin t ht
  have hδ_lt : (1 / 2 : ℝ) < 1 := by norm_num
  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T₁,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    intro t ht
    have ht_d2 : t ∈ Set.Icc (0 : ℝ) d₂ :=
      ⟨ht.1, le_trans ht.2.le hT₁_le_d2⟩
    have ht_icc₁ : t ∈ Set.Icc (0 : ℝ) T₁ := ⟨ht.1, ht.2.le⟩
    exact hd₂ t ht_d2 (F t) (hF_pin t ht_icc₁)
  have hForceRepr : ∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Nsec (F t) hδ_lt (hF_small t))) i :=
    hForceRepr_fam hT₁_pos hT₁_le hT₁_le_d2F F hδ_lt hF_small hF_pin hball
  have hF_flow := metricPerturbationPathily_flowDeriv_of_repr (I := I) (M := M) g₀ a
    F_RHS Nsec hRepr hT hT1 hT₁_pos hT₁_le hd₂F_pos hd₂F_le hT₁_le_d2F u F hδ_lt hF_small
    hF_pin f hf_smooth hf_mass hf_id hForceRepr
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T₁,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hF_pin t ht, tensorHsToL2_tensorL2Coeff]
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    have hid := hf_id t ht_icc i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T₁,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₂F) hd₂F_pos.le f hf_smooth hf_mass k σ hσ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    have ht_icc : t ∈ Set.Icc (0 : ℝ) d₂F := ⟨ht.1, le_trans ht.2 hT₁_le_d2F⟩
    exact hCmaj_le i t ht_icc
  have hF_joint : JointChartGramSmooth (I := I) T₁
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hF_small t)) :=
    metricPerturbationPathily_jointChartGramSmooth (I := I) (M := M) g₀ hT₁_pos F hδ_lt hF_small
      φ hφ_smooth hcoeff hmodemass
  exact ⟨T₁, hT₁_pos, hT₁_le, F, 1 / 2, hδ_lt, hF_small, hF_zero, hF_pin, hF_flow,
    hF_joint⟩

theorem maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
      SmoothCcTensor g₀ 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0)
    (f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (f i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (f i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t)
    (C : ℝ) (hC_pos : 0 < C)
    (hC : ∀ (S : SmoothCcTensor g₀ 0 2),
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ S)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) S‖))
    (hstate : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ 1 / (2 * C))
    {R₀ : ℝ}
    (hball_full : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀)
    (hForce : ∀ (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
        (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (Nat.cast_nonneg a) (timeH1.toFun u t))
        (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀),
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
        f i t = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (Nsec (F t) hδ_lt (hδ t))) i) :
    ∃ (F : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hinit : u.init = 0 := by have := htrace; rwa [timeH1.trace0_apply] at this
  have hu0 : timeH1.toFun u 0 = 0 := by rw [timeH1.toFun_zero, hinit]
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_of_contDiff ⊤ _ (f i) (hf_smooth i)
  have hf_endpoint_sum : ∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
        ∫ s in (0 : ℝ)..t, (f i s) ^ 2) := by
    intro c hc t ht
    obtain ⟨B, hB_sum, hB_le⟩ := hf_mass 0 c hc
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hB_sum.mul_left T)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · have hwt_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i c :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i c
      have hcont_sq : Continuous (fun s => (f i s) ^ 2) := ((hf_smooth i).continuous).pow 2
      have htint : (∫ s in (0 : ℝ)..t, (f i s) ^ 2) ≤ ∫ s in (0 : ℝ)..T, (f i s) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le hT.le,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set hcont_sq.integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      have hbig : tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..T, (f i s) ^ 2 ≤ T * B i := by
        have hi_lhs : IntervalIntegrable
            (fun s => tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2)
            MeasureTheory.volume 0 T :=
          (hcont_sq.const_mul _).intervalIntegrable 0 T
        have hi_const : IntervalIntegrable (fun _ : ℝ => B i) MeasureTheory.volume 0 T :=
          intervalIntegrable_const
        have hmono : ∫ s in (0 : ℝ)..T,
              tensorSobolevWeight (I := I) (M := M) i c * (f i s) ^ 2
            ≤ ∫ _s in (0 : ℝ)..T, B i := by
          refine intervalIntegral.integral_mono_on hT.le hi_lhs hi_const ?_
          intro s hs
          have := hB_le i s hs
          rwa [iteratedDeriv_zero] at this
        rw [intervalIntegral.integral_const_mul] at hmono
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
        exact hmono
      calc tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..t, (f i s) ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i c * ∫ s in (0 : ℝ)..T, (f i s) ^ 2 :=
            mul_le_mul_of_nonneg_left htint hwt_nn
        _ ≤ T * B i := hbig
  have hF₀_exists : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ S : SmoothCcTensor g₀ 0 2,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    obtain ⟨uDuh, huDuh_coeff, huDuh_mem⟩ :=
      duhamel_into_all_tensorHs (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (t := t) ht.1 h_compact f (fun i => (hf_smooth i).continuous)
        (fun c hc => hf_endpoint_sum c hc t ht)
    have hval : uDuh = tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
      refine tensorL2_ext_of_tensorL2Coeff_jsmooth (I := I) (M := M) h_compact (fun i => ?_)
      rw [huDuh_coeff i]
      exact (hf_id t ht i).symm
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ v : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              h_compact hσ v = uDuh := huDuh_mem
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) uDuh hmem
    refine ⟨S, ?_⟩
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = (S : TensorL2 0 2 g₀) from rfl,
      hS, hval]
  choose F₀ hF₀ using hF₀_exists
  set Fdef : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if ht : t ∈ Set.Icc (0 : ℝ) T then F₀ t ht else 0 with hFdef_def
  have hFdef_pin : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T),
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Fdef t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    simp only [hFdef_def, dif_pos ht]
    exact hF₀ t ht
  set F : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => if t ∈ Set.Ioc (0 : ℝ) T then Fdef t else 0 with hF_def
  have hF_zero : F 0 = 0 := by
    simp only [hF_def]
    rw [if_neg]
    intro hmem; exact absurd hmem.1 (lt_irrefl 0)
  have hF_small : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) (1 / 2) := by
    intro t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) T
    · have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht]
      have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
      have hpin := hFdef_pin t ht_icc
      have heq : smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t) =
          timeH1.toFun u t := by
        refine tensorHs.ext (funext (fun i => ?_))
        rw [smoothCcToTensorHs_coeff, hpin, tensorHsToL2_tensorL2Coeff]
      have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤
          1 / (2 * C) := by
        rw [heq]
        exact hstate t ht_icc
      intro x v w
      rw [hFt]
      refine le_trans (hC (Fdef t) x v w) ?_
      have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖ ≤ 1 / 2 := by
        calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖
            ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hnorm_le hC_pos.le
          _ = 1 / 2 := by field_simp
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
        mul_nonneg hsv_nn hsw_nn
      calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
          = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Fdef t)‖) *
              (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
        _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
            mul_le_mul_of_nonneg_right hCN_le hmul_nn
        _ = (1 / 2 : ℝ) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
    · have hFt : F t = 0 := by simp only [hF_def, if_neg ht]
      intro x v w
      rw [hFt, ccTensorBilinSymm_zero_apply_jsmooth]
      have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
      have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
      rw [abs_zero]
      positivity
  have hF_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          h_compact (Nat.cast_nonneg a) (timeH1.toFun u t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hF_zero, hu0]
      simp only [map_zero]
    · have ht_ioc : t ∈ Set.Ioc (0 : ℝ) T := ⟨h0, ht.2⟩
      have hFt : F t = Fdef t := by simp only [hF_def, if_pos ht_ioc]
      rw [hFt]
      exact hFdef_pin t ht
  have hδ_lt : (1 / 2 : ℝ) < 1 := by norm_num
  have hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤ R₀ := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    exact hball_full t ht_icc (F t) (hF_pin t ht_icc)
  have hForceRepr : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      f i t = tensorL2Coeff (I := I) (M := M) h_compact
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
            (Nsec (F t) hδ_lt (hF_small t))) i :=
    hForce F hδ_lt hF_small hF_pin hball
  have hF_flow := metricPerturbationPathily_flowDeriv_of_repr (I := I) (M := M) g₀ a
    F_RHS Nsec hRepr hT hT1 hT (le_refl T) hT (le_refl T) (le_refl T) u F hδ_lt hF_small
    hF_pin f hf_smooth hf_mass hf_id hForceRepr
  have hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hF_pin t ht, tensorHsToL2_tensorL2Coeff]
    have hid := hf_id t ht i
    rw [tensorHsToL2_tensorL2Coeff] at hid
    rw [hid]
  have hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i := by
    intro k σ hσ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := T) hT.le f hf_smooth hf_mass k σ hσ
    exact ⟨Cmaj, hCmaj_sum, fun i t ht => hCmaj_le i t ht⟩
  have hF_joint : JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hF_small t)) :=
    metricPerturbationPathily_jointChartGramSmooth (I := I) (M := M) g₀ hT F hδ_lt hF_small
      φ hφ_smooth hcoeff hmodemass
  exact ⟨F, 1 / 2, hδ_lt, hF_small, hF_zero, hF_pin, hF_flow, hF_joint⟩

theorem hs2_opBound_at_two (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ S)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 : ℕ) : ℝ)) S‖) := by
  obtain ⟨C, hC_pos, hOp⟩ := hs2_op_bound (I := I) (M := M) hDim g₀
  refine ⟨C, hC_pos, fun S => ?_⟩
  have htwo : ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S :=
    tensorHs.ext (funext (fun _ ↦ rfl))
  simpa only [htwo, Nat.cast_ofNat] using hOp S

end DifferentialGeometry.Analysis.Spectral
end
