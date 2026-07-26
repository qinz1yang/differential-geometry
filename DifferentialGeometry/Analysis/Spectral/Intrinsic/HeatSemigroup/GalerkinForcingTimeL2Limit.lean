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

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

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
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
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
    {μ : Measure α} [NormedAddCommGroup β] [IsFiniteMeasure μ]
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
  have hhelper := tendsto_of_coeff
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
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
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
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
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
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT hT1 (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (VN s)) :=
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
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (_hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
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
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
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

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
