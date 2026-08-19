import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.AllOrderRegularity

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic (field_mem_lower lowerState zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (JetSpectralMassControl contDiffOn_Icc_scalar_globalExtend deTurckSmoothN
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass deTurckSmoothRemainder
    exists_smoothCcPath_realizing_coeff gFibreOpBound_symmS
    perModeConv_allOrder_timeDeriv_spectralMass_le
    perModeConv_finiteOrder_timeJet_spectralMass_gain smoothCcToTensorHs
    smoothCcToTensorHs_coeff smoothCcToTensorHs_smul symmCoeffPath
    symmCoeffPath_contDiff symmCoeffPath_realizes symmCoeffPath_spectralMass
    tensorResolventL2_isCompactOperator)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem force_step_one
    (g g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g_bg hδ hreal))
    {T : ℝ} (hT : 0 < T)
    (field : timeL2 (tensorHs (I := I) (M := M) g 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      field t ∈ lowerState (I := I) (M := M) g 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le) field t))
    (k : ℕ) (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hfield : ∀ i, (fun t => (field t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fLo t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] ψ i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  obtain ⟨F₀, hF₀_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g φ hmass0
  set F : ℝ → SmoothCcTensor g 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) T then F₀ t else 0 with hF_def
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    simp only [hF_def, ht, if_pos]
    exact hF₀_coeff t ht i
  have hF_hs2 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t))
      (Set.Icc (0 : ℝ) T) := by
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0
      ((((1 : ℕ) : ℝ) + 1) +
        (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (((1 : ℕ) : ℝ) + 1))
      (σ' := (((1 : ℕ) : ℝ) + 1) +
        (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) ?_
      (s := Set.Icc (0 : ℝ) T)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t)) φ
      hF_hs2 (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have hring : (((1 : ℕ) : ℝ) + 1) +
        (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) -
          (((1 : ℕ) : ℝ) + 1) =
        ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by ring
    rw [hring]
    linarith
  have hball_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t)‖ ≤ R := by
    have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ i, (field t).coeff i = φ i t := (MeasureTheory.ae_all_iff).2 hfield
    filter_upwards [hstate, hall, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hst htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t) =
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
          (field t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [hF_hs2 t htmem j, tensorHsInclusion_coeff_apply, htall j]
    rw [heq]
    simpa only [lowerState, lowerBall] using hst
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t)‖ ≤ R := by
    have hcont_norm : ContinuousOn
        (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖)
        (Set.Icc (0 : ℝ) T) := continuous_norm.comp_continuousOn hfield_cont
    have hg_cont : ContinuousOn
        (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖ ⊓ R)
        (Set.Icc (0 : ℝ) T) := hcont_norm.inf continuousOn_const
    have hfg : (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T)]
        (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖ ⊓ R) := by
      filter_upwards [hball_ae] with t ht
      exact (min_eq_left ht).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hT) hfg
      hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (F t)‖ ⊓ R := heq ht
    rw [hmin]
    exact inf_le_right
  have hball_all : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R := by
    intro t
    have heq : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (F t)) =
          smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) (F t) := by
      refine tensorHs.ext (funext fun i => ?_)
      rw [tensorHsInclusion_coeff_apply, smoothCcToTensorHs_coeff,
        smoothCcToTensorHs_coeff]
    rw [heq]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · exact hball_pt t ht
    · have hF0 : F t = (0 : SmoothCcTensor g 0 2) := by
        simp only [hF_def, ht, if_neg, not_false_iff]
      rw [hF0]
      have hz : smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1)
          (0 : SmoothCcTensor g 0 2) = 0 := by
        have h0 : (0 : SmoothCcTensor g 0 2) =
            (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
        rw [h0, smoothCcToTensorHs_smul, zero_smul]
      rw [hz, norm_zero]
      exact hR.le
  have hδF : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (F t)) δ := by
    intro t
    exact hreal (F t) (by
      rw [← show tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (F t)) =
            smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) (F t) from by
          refine tensorHs.ext (funext fun i => ?_)
          rw [tensorHsInclusion_coeff_apply, smoothCcToTensorHs_coeff,
            smoothCcToTensorHs_coeff]]
      exact hball_all t)
  have hδS : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (symmS (I := I) (M := M) g (F t))) δ :=
    fun t => gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδF t)
  have hφ'_smooth : ∀ i, ContDiff ℝ (k : ℕ)
      (symmCoeffPath (I := I) (M := M) g φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g hφ_smooth
  have hφ'_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g φ i) t) ^ 2 ≤ B i := by
    intro j hjk τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g hT j
      (fun i => (hφ_smooth i).of_le (mod_cast hjk)) τ
      (hφ_mass j hjk τ hτ)
      (hφ_mass j hjk (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (symmS (I := I) (M := M) g (F t))) i =
        symmCoeffPath (I := I) (M := M) g φ i t := fun t ht i =>
    symmCoeffPath_realizes (I := I) (M := M) g φ (F t) (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g g_bg 1 hT k (fun t => symmS (I := I) (M := M) g (F t)) hδ hδS
      (symmCoeffPath (I := I) (M := M) g φ) hφ'_smooth hcoeff' hφ'_mass
  have hpinF : ∀ᵐ t ∂timeMeasure T,
      smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (F t) = field t := by
    have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ i, (field t).coeff i = φ i t := (MeasureTheory.ae_all_iff).2 hfield
    filter_upwards [hall, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t htall htmem
    refine tensorHs.ext (funext fun i => ?_)
    rw [smoothCcToTensorHs_coeff, hF_coeff t htmem i, ← htall i]
  have hsmooth := deTurck_remainder_forcing_eq_smooth_remainder_ae (I := I) (M := M) g g_bg hR hδ hreal hcore
    field fLo hstate hforce F hpinF hball_all
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  filter_upwards [hsmooth, MeasureTheory.ae_restrict_mem
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htmem
  rw [ht]
  exact hψ_coeff t htmem i

private theorem force_driver_one
    (g g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g_bg hδ hreal))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo t ∈ lowerState (I := I) (M := M) g 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ) :
    ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fLo t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] f i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  set field : timeL2 (tensorHs (I := I) (M := M) g 0 2
      (((1 : ℕ) : ℝ) + 2)) T :=
    maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo
      with hfield_def
  set ρw : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρw_def
  have hρw_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρw := by
    rw [hρw_def]
    linarith
  have hpmc_contOn : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u))
          (Set.Icc (0 : ℝ) T) := fun i =>
    continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) fLo i) hT.le
  set c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := fun i =>
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) p.1) with hc_def
  have hc_cont : ∀ i, Continuous (c i) := fun i =>
    Continuous.Icc_extend' ((hpmc_contOn i).restrict)
  have hc_eqOn : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u))
          (Set.Icc (0 : ℝ) T) := by
    intro i t ht
    exact Set.IccExtend_of_mem hT.le _ ht
  have hs_mass : ∀ τ : ℝ, 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ B i := by
    intro τ hτ
    obtain ⟨Cτ, hCτ⟩ := hspatial (τ + ρw)
    refine ⟨fun i => Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw),
      (tensorEigen_summable_negpow (I := I) (M := M) g ρw hρw_gt).mul_left Cτ, ?_⟩
    intro i t ht
    obtain ⟨hsum_t, hbd_t⟩ := hCτ t ht
    have hterm : tensorSobolevWeight (I := I) (M := M) i (τ + ρw) *
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cτ :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j (τ + ρw)) (sq_nonneg _))) hbd_t
    have hsplit : tensorSobolevWeight (I := I) (M := M) i τ =
        tensorSobolevWeight (I := I) (M := M) i (-ρw) *
          tensorSobolevWeight (I := I) (M := M) i (τ + ρw) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρw) (τ + ρw)]
      congr 1
      ring
    calc tensorSobolevWeight (I := I) (M := M) i τ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρw) *
            (tensorSobolevWeight (I := I) (M := M) i (τ + ρw) *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) := by
            rw [hsplit]
            ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρw) * Cτ :=
        mul_le_mul_of_nonneg_left hterm
          (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρw))
      _ = Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw) := by ring
  have hcoeff_id : ∀ i, (fun t => (field t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) := fun i => by
    simpa only [field] using
      (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hT1 hc fLo i)
  have hfLo_tmc : ∀ i, (fun t => (fLo t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        fun t => (timeModeCoeff (I := I) (M := M) fLo i) t := fun i =>
    (timeModeCoeff_coeFn (I := I) (M := M) fLo i).symm
  intro k
  induction k with
  | zero =>
    exact force_step_one (I := I) (M := M) g g_bg hR hδ hreal hcore hT field fLo
      (by simpa only [field] using hstate)
      (by simpa only [field] using hforce) 0 c
      (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
      (fun j hj τ hτ => by
        obtain rfl := Nat.le_zero.mp hj
        obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
        refine ⟨B, hBs, fun i t ht => ?_⟩
        rw [iteratedDeriv_zero, hc_eqOn i ht]
        exact hBle i t ht)
      (fun i => by
        refine (hcoeff_id i).trans ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
        exact (hc_eqOn i ht).symm)
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g hT.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (field t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i) := by
      intro i
      have hfk_tmc : (fun t => (timeModeCoeff (I := I) (M := M) fLo i) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] fk i :=
        (hfLo_tmc i).symm.trans (hfk_ae i)
      have hpm : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun t => (timeModeCoeff (I := I) (M := M) fLo i) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
        exact perModeConv_timeL2_congr (T := T)
          (TensorEigenIdx.lambda (I := I) (M := M) i) hfk_tmc ht
      exact (hcoeff_id i).trans hpm
    exact force_step_one (I := I) (M := M) g g_bg hR hδ hreal hcore hT field fLo
      (by simpa only [field] using hstate)
      (by simpa only [field] using hforce) (k + 1)
      (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
      hφ_cont hφ_mass hw_coeff

private theorem force_jet_of_mass
    (g g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g_bg hδ hreal))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo t ∈ lowerState (I := I) (M := M) g 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ) :
    ∃ fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g fc T ∧
      ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i := by
  classical
  have hdrv := force_driver_one (I := I) (M := M) g g_bg hR hδ hreal
    hcore hT hT1 fLo hstate hforce hspatial
  choose Fk hFk_smooth hFk_mass hFk_ae using hdrv
  set f0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := Fk 0
    with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) T ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have hEqOn : ∀ (k : ℕ) i, Set.EqOn (Fk k i) (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro k i
    have hae : Fk k i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] f0 i :=
      (hFk_ae k i).symm.trans (hFk_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hFk_smooth k i).continuous).continuousOn
      ((hFk_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hFk_smooth n i).contDiffOn).congr (fun t ht => (hEqOn n i ht).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) T) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hT (hf0_smoothOn i)
  choose fc hfc_smooth hfc_eqOn using hext
  have hjetEq : ∀ (j : ℕ) i t, t ∈ Set.Icc (0 : ℝ) T →
      iteratedDeriv j (fc i) t =
        iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) T) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hfc_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
      ((hfc_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  have hfc_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i := by
    intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hFk_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (fc i) t = iteratedDeriv j (Fk j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT)
        ((hFk_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  have hfc_pin : ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i := by
    intro i
    refine (hFk_ae 0 i).trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
    exact hfc_eqOn i ht
  exact ⟨fc, ⟨hfc_smooth, hfc_mass⟩, hfc_pin⟩

theorem exists_forcing_spectral_jet_mass_control_for_adapted_solution
    (g : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g fc T ∧
      ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i := by
  let hs := hlo.toIsLowRegularitySolutionAt
  have hR : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hs.hCtop hs.hB1 hs.hρ hs.hP
  have hstate : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo t ∈ lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius Ctop B1 ρ P) := by
    exact field_mem_lower (I := I) (M := M) g 1 hT hT1
      (by nlinarith [hR.le]) fLo hs.hball
  have hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g hR hs.hδ
        (lowRegularityMetricRealization (I := I) (M := M) g
          (Ctop := Ctop) (B1 := B1) (ρ := ρ) hs.hP.le hs.hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t) := by
    simpa only [boundedDeTurckRemainderOnLowerState] using hs.hforce
  exact force_jet_of_mass (I := I) (M := M) g g hR hs.hδ
    (lowRegularityMetricRealization (I := I) (M := M) g
      (Ctop := Ctop) (B1 := B1) (ρ := ρ) hs.hP.le hs.hreal)
    hs.hcore hT hT1 fLo hstate hforce
    (fun σ =>
      per_mode_limit_weighted_energy_bound_all_orders (I := I) (M := M)
        g hT hT1 fLo hlo σ)

omit [BoundarylessManifold I M] in
private theorem force_promote_two
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hfc : JetSpectralMassControl (I := I) (M := M) g fc T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hpin : ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i) :
    ∃ fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T,
      (∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) ∧
      ∀ᵐ t ∂timeMeasure T,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
  obtain ⟨B₂, hB₂_sum, hB₂_le'⟩ := hfc.2 0 (2 : ℝ) (by norm_num)
  have hB₂_le : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i t) ^ 2 ≤ B₂ i := by
    intro i t ht
    simpa only [iteratedDeriv_zero] using hB₂_le' i t ht
  set pr : ℝ → ℝ :=
    fun t => ((Set.projIcc (0 : ℝ) T hT.le t : Set.Icc (0 : ℝ) T) : ℝ)
      with hpr_def
  have hpr_mem : ∀ t, pr t ∈ Set.Icc (0 : ℝ) T :=
    fun t => (Set.projIcc (0 : ℝ) T hT.le t).2
  have hpr_id : ∀ t ∈ Set.Icc (0 : ℝ) T, pr t = t := by
    intro t ht
    rw [hpr_def]
    simp only [Set.projIcc_of_mem hT.le ht]
  have hpr_cont : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  set W : ℝ → tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) := fun t =>
    tensorHs_of_spectralMass_majorant (I := I) (M := M)
      (fun i => fc i (pr t)) B₂ hB₂_sum
      (fun i => hB₂_le i (pr t) (hpr_mem t)) with hW_def
  set σ' : ℝ := (2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)
    with hσ'_def
  obtain ⟨Bh, hBh_sum, hBh_le'⟩ := hfc.2 0 σ' (by
    rw [hσ'_def]
    positivity)
  have hBh_le : ∀ i t,
      tensorSobolevWeight (I := I) (M := M) i σ' * (fc i (pr t)) ^ 2 ≤ Bh i := by
    intro i t
    simpa only [iteratedDeriv_zero] using hBh_le' i (pr t) (hpr_mem t)
  have hW_cont : Continuous W := by
    rw [← continuousOn_univ]
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (2 : ℝ)) (σ' := σ') ?_ (s := Set.univ) W
      (fun i t => fc i (pr t)) ?_ ?_ hBh_sum ?_
    · rw [hσ'_def]
      linarith
    · intro t _ i
      simp only [W, tensorHs_of_spectralMass_majorant_coeff]
    · intro i
      exact ((hfc.1 i).continuous.comp hpr_cont).continuousOn
    · intro i t _
      exact hBh_le i t
  let fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T :=
    DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ofContinuousOn
      hW_cont.continuousOn
  have hrep : (fun t => fHi t) =ᵐ[timeMeasure T] W :=
    DifferentialGeometry.Analysis.Parabolic.TimeSobolev.coeFn_ofContinuousOn
      hW_cont.continuousOn
  have hpin_all : ∀ᵐ t ∂timeMeasure T, ∀ i, (fLo t).coeff i = fc i t :=
    (MeasureTheory.ae_all_iff).2 hpin
  have hpin_hi : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i := by
    intro i
    filter_upwards [hrep, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htmem
    rw [ht]
    simp only [W, tensorHs_of_spectralMass_majorant_coeff, hpr_id t htmem]
  refine ⟨fHi, hpin_hi, ?_⟩
  filter_upwards [hrep, hpin_all, MeasureTheory.ae_restrict_mem
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htl htmem
  refine tensorHs.ext (funext fun i => ?_)
  rw [tensorHsInclusion_coeff_apply, ht]
  simp only [W, tensorHs_of_spectralMass_majorant_coeff, hpr_id t htmem, htl i]

omit [BoundarylessManifold I M] in
private theorem carrier_one_coeff
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_cont : ∀ i, Continuous (fc i))
    (hf_mass0 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      Summable B ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) * (fc i t) ^ 2 ≤ B i)
    (hpin : ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        ((maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).toFun t).coeff i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass0
  set pr : ℝ → ℝ := fun t =>
    ((Set.projIcc (0 : ℝ) T hT.le t : Set.Icc (0 : ℝ) T) : ℝ) with hpr_def
  have hpr_mem : ∀ t, pr t ∈ Set.Icc (0 : ℝ) T :=
    fun t => (Set.projIcc (0 : ℝ) T hT.le t).2
  have hpr_id : ∀ t ∈ Set.Icc (0 : ℝ) T, pr t = t := by
    intro t ht
    rw [hpr_def]
    simp only [Set.projIcc_of_mem hT.le ht]
  have hpr_cont : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  set Frep : ℝ → tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) := fun t =>
    tensorHs_of_spectralMass_majorant (I := I) (M := M)
      (fun i => fc i (pr t)) B0 hB0_sum
      (fun i => hB0_le i (pr t) (hpr_mem t)) with hFrep_def
  have hFrep_coeff : ∀ t i, (Frep t).coeff i = fc i (pr t) := fun _ _ => rfl
  have hFcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (fun t => (Frep t).coeff i) (Set.Icc (0 : ℝ) T) := fun i =>
    ((hf_cont i).comp hpr_cont).continuousOn
  have hall : ∀ᵐ t ∂timeMeasure T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2, (fLo t).coeff i = fc i t :=
    (MeasureTheory.ae_all_iff).2 hpin
  have hF_rep : (⇑fLo) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] Frep := by
    filter_upwards [hall, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htmem
    refine tensorHs.ext (funext fun i => ?_)
    rw [ht i, hFrep_coeff t i, hpr_id t htmem]
  intro t ht i
  rw [carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
    (h_compact := hc) (a := ((1 : ℕ) : ℝ)) hT hT1 hT le_rfl fLo hFcoord hF_rep i ht]
  refine perModeConv_timeL2_congr (T := T)
    (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
  rw [Set.IccExtend_of_mem hT.le _ hs, hFrep_coeff s i, hpr_id s hs]

omit [BoundarylessManifold I M] in
private theorem duhamel_mode_pin
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hfc : JetSpectralMassControl (I := I) (M := M) g fc T)
    (hpinLo : ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i)
    (hpinHi : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).toFun t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
          ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).repr t) := by
  classical
  obtain ⟨B1, hB1s, hB1⟩ := hfc.2 0 ((1 : ℕ) : ℝ) (by norm_num)
  obtain ⟨B2, hB2s, hB2⟩ := hfc.2 0 (2 : ℝ) (by norm_num)
  have hmass1 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      Summable B ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i ((1 : ℕ) : ℝ) * (fc i t) ^ 2 ≤ B i :=
    ⟨B1, hB1s, fun i t ht => by simpa only [iteratedDeriv_zero] using hB1 i t ht⟩
  have hmass2 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      Summable B ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i t) ^ 2 ≤ B i :=
    ⟨B2, hB2s, fun i t ht => by simpa only [iteratedDeriv_zero] using hB2 i t ht⟩
  have hhi := carrier_coeff_pmConv (I := I) (M := M) g hT hT1 fHi fc
    (fun i => (hfc.1 i).continuous) hmass2 hpinHi
  have hlo := carrier_one_coeff (I := I) (M := M) g hT hT1 fLo fc
    (fun i => (hfc.1 i).continuous) hmass1 hpinLo
  intro t ht
  refine tensorHs.ext (funext fun i => ?_)
  rw [tensorHsCongr_coeff]
  rw [(duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).repr_coeff hT ht i]
  change _ = ((maxRegDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).toFun t).coeff i
  have hh := hhi t ht i
  rw [tensorHsToL2_tensorL2Coeff] at hh
  exact hh.trans (hlo t ht i).symm

omit [BoundarylessManifold I M] in
private theorem direct_state_bound
    (g : SmoothRiemannianMetric I M) {R T : ℝ} (hR : 0 < R)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (uHi : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (hmode : ∀ t ∈ Set.Icc (0 : ℝ) T,
      timeH1.toFun uHi t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
          ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).repr t))
    (hmem : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo t ∈
        lowerState (I := I) (M := M) g 1 R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun uHi t‖ ≤ R := by
  have hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).hiL2 t)‖ ≤
          R := by
    filter_upwards [hmem] with t ht
    simpa only [duhamelCross, lowerState, lowerBall] using ht
  have hrepr := crossRepr_ball (I := I) (M := M)
    (duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo)
    hT hR.le hball
  intro t ht
  rw [hmode t ht, norm_tensorHsCongr]
  exact hrepr t ht

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem direct_force_coeff
    (g g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g_bg hδ hreal))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hfield_mem : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t))
    (uHi : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hfc : JetSpectralMassControl (I := I) (M := M) g fc T)
    (hpinLo : ∀ i, (fun t => (fLo t).coeff i) =ᵐ[timeMeasure T] fc i)
    (hmode : ∀ t ∈ Set.Icc (0 : ℝ) T,
      timeH1.toFun uHi t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
          ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo).repr t))
    (hstate : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun uHi t‖ ≤ R)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun uHi t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t) :
    ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g (F t)) δ'),
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun uHi t)) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
        fc i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (deTurckSmoothRemainder (I := I) g g_bg
              (symmS (I := I) (M := M) g (F t)) hδ'_lt
              (gFibreOpBound_symmS (I := I) (M := M) g (F t)
                (hδ' t)))) i := by
  classical
  intro F δ' hδ'_lt hδ' hpin
  let field : timeL2 (tensorHs (I := I) (M := M) g 0 2
      (((1 : ℕ) : ℝ) + 2)) T :=
    maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo
  have hF2 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) (F t) =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num)
          (timeH1.toFun uHi t) := by
    intro t ht
    refine tensorHs.ext (funext fun i => ?_)
    rw [smoothCcToTensorHs_coeff, tensorHsCongr_coeff, hpin t ht,
      tensorHsToL2_tensorL2Coeff]
  set Fcut : ℝ → SmoothCcTensor g 0 2 :=
    fun t => if t ∈ Set.Icc (0 : ℝ) T then F t else 0 with hFcut_def
  have hball2 : ∀ t : ℝ,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (Fcut t)‖ ≤ R := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · rw [show Fcut t = F t by simp only [hFcut_def, ht, if_pos], hF2 t ht]
      rw [norm_tensorHsCongr]
      exact hstate t ht
    · rw [show Fcut t = (0 : SmoothCcTensor g 0 2) by
        simp only [hFcut_def, ht, if_false], smoothCcToTensorHs_zero, norm_zero]
      exact hR.le
  have hball_all : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (Fcut t))‖ ≤ R := by
    intro t
    rw [show tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (Fcut t)) =
          smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) (Fcut t) by
      refine tensorHs.ext (funext fun i => ?_)
      rw [tensorHsInclusion_coeff_apply, smoothCcToTensorHs_coeff,
        smoothCcToTensorHs_coeff]]
    exact hball2 t
  have hδcut : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (Fcut t)) δ := fun t => hreal (Fcut t) (by
    exact hball2 t)
  have hfield_pin : ∀ᵐ t ∂timeMeasure T,
      smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (Fcut t) = field t := by
    have hrepr := duhRepr_field_ae (I := I) (M := M)
      g 0 2 ((1 : ℕ) : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo
    filter_upwards [hrepr, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hrepr_t ht
    refine tensorHs.ext (funext fun i => ?_)
    have hi := congrArg (fun x => x.coeff i) (hF2 t ht)
    change (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) (F t)).coeff i =
      (tensorHsCongr (I := I) (M := M) g 0 2
        (show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num)
        (timeH1.toFun uHi t)).coeff i at hi
    rw [tensorHsCongr_coeff] at hi
    have hm := congrArg (fun x => x.coeff i) (hmode t ht)
    change (timeH1.toFun uHi t).coeff i =
      (tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
        ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo).repr t)).coeff i at hm
    rw [tensorHsCongr_coeff] at hm
    have hr := congrArg (fun x => x.coeff i) hrepr_t
    calc
      (smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (Fcut t)).coeff i =
          (smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) (F t)).coeff i := by
              rw [show Fcut t = F t by simp only [hFcut_def, ht, if_pos],
                smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
      _ = (timeH1.toFun uHi t).coeff i := hi
      _ = ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo).repr t).coeff i := hm
      _ = (field t).coeff i := by
          simpa only [tensorHsInclusion_coeff_apply, field] using hr
  have hsmooth := deTurck_remainder_forcing_eq_smooth_remainder_ae (I := I) (M := M) g g_bg hR hδ hreal
    hcore field fLo (by simpa only [field] using hfield_mem)
      (by simpa only [field] using hforce) Fcut hfield_pin hball_all
  set φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := fun i =>
    perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i => by
    rw [hφ_def]
    exact perModeConv_contDiff_of_contDiff ⊤ _ (fc i) (hfc.1 i)
  have hφ_mass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv j (φ i) t) ^ 2 ≤ B i := by
    intro j σ hσ
    simpa only [φ] using
      (perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g) (r := 0) (s := 2) (T := T) hT.le fc hfc.1 hfc.2 j σ hσ)
  have hF_coeff : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t)) i = φ i t := by
    intro t ht i
    rw [hpin t ht, hf_id t ht i]
  have hφ'_smooth : ∀ i, ContDiff ℝ (1 : ℕ)
      (symmCoeffPath (I := I) (M := M) g φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g
      (fun i => (hφ_smooth i).of_le (by simp))
  have hφ'_mass : ∀ (j : ℕ), j ≤ 1 → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g φ i) t) ^ 2 ≤ B i := by
    intro j hj σ hσ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g hT j
      (fun i => (hφ_smooth i).of_le
        (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))) σ
      (hφ_mass j σ hσ)
      (hφ_mass j (σ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (symmS (I := I) (M := M) g (F t))) i =
        symmCoeffPath (I := I) (M := M) g φ i t := fun t ht i =>
    symmCoeffPath_realizes (I := I) (M := M) g φ (F t)
      (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_smooth, -, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g g_bg 1 hT 1 (fun t => symmS (I := I) (M := M) g (F t)) hδ'_lt
      (fun t => gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδ' t))
      (symmCoeffPath (I := I) (M := M) g φ) hφ'_smooth hcoeff' hφ'_mass
  have hae : ∀ i, fc i =ᵐ[timeMeasure T] ψ i := by
    intro i
    filter_upwards [hpinLo i, hsmooth, MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hpin_t hsmooth_t ht
    have hcut : Fcut t = F t := by simp only [hFcut_def, ht, if_pos]
    have hwd : deTurckSmoothN (I := I) (M := M) g g_bg 1
          (symmS (I := I) (M := M) g (Fcut t)) hδ
          (gFibreOpBound_symmS (I := I) (M := M) g (Fcut t) (hδcut t)) =
        deTurckSmoothN (I := I) (M := M) g g_bg 1
          (symmS (I := I) (M := M) g (F t)) hδ'_lt
          (gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδ' t)) := by
      apply smoothN_wd (I := I) (M := M)
      rw [hcut]
    calc fc i t = (fLo t).coeff i := (hpin_t).symm
      _ = (deTurckSmoothN (I := I) (M := M) g g_bg 1
          (symmS (I := I) (M := M) g (Fcut t)) hδ
          (gFibreOpBound_symmS (I := I) (M := M) g (Fcut t) (hδcut t))).coeff i := by
            rw [hsmooth_t]
      _ = (deTurckSmoothN (I := I) (M := M) g g_bg 1
          (symmS (I := I) (M := M) g (F t)) hδ'_lt
          (gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδ' t))).coeff i := by
            rw [hwd]
      _ = ψ i t := hψ_coeff t ht i
  have heqOn : ∀ i, Set.EqOn (fc i) (ψ i) (Set.Ico (0 : ℝ) T) := by
    intro i
    refine MeasureTheory.Measure.eqOn_Ico_of_ae_eq
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
      ((hfc.1 i).continuous.continuousOn) ((hψ_smooth i).continuous.continuousOn)
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self (hae i)
  intro t ht i
  refine (heqOn i ht).trans ?_
  rw [← hψ_coeff t (Set.Ico_subset_Icc_self ht) i]
  rfl

private theorem direct_radius
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (uHi : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hfc : JetSpectralMassControl (I := I) (M := M) g fc T)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun uHi t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun uHi t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀ := by
  classical
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
    perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (T := T) hT.le fc hfc.1 hfc.2 0
      ((2 : ℝ) + 2) (by norm_num)
  have hCmaj_nn : ∀ i, 0 ≤ Cmaj i := fun i =>
    le_trans (mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i ((2 : ℝ) + 2))
      (sq_nonneg _)) (hCmaj_le i 0 ⟨le_rfl, hT.le⟩)
  refine ⟨Real.sqrt (∑' i, Cmaj i) + 1,
    by linarith only [Real.sqrt_nonneg (∑' i, Cmaj i)], ?_⟩
  intro t ht S hS
  have hcoeff : ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
    intro i
    rw [smoothCcToTensorHs_coeff, hS]
    exact hf_id t ht i
  have hptwise : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i ((2 : ℝ) + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i) ^ 2 ≤
        Cmaj i := by
    intro i
    rw [hcoeff i]
    have h := hCmaj_le i t ht
    rwa [iteratedDeriv_zero] at h
  have hsq_le : ‖smoothCcToTensorHs (I := I) (M := M) g
        ((2 : ℝ) + 2) S‖ ^ 2 ≤ ∑' i, Cmaj i := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    exact Summable.tsum_le_tsum hptwise
      ((smoothCcToTensorHs (I := I) (M := M) g
        ((2 : ℝ) + 2) S).weighted_summable) hCmaj_sum
  have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g
      ((2 : ℝ) + 2) S‖ ≤ Real.sqrt (∑' i, Cmaj i) := by
    rw [show ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ =
      Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g
        ((2 : ℝ) + 2) S‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq_le
  linarith only [hnorm_le]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
theorem direct_jet_of_mass
    (g g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g_bg hδ hreal))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hfield_mem : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo t ∈
        lowerState (I := I) (M := M) g 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Cσ) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) (2 : ℝ) T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
      (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ) (R₀ : ℝ),
      timeH1.trace0 _ T u = 0 ∧
      u = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi ∧
      (∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) ∧
      (∀ i, ContDiff ℝ ∞ (fc i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (fc i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t) ∧
      0 < R₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀) ∧
      (∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g (F t)) δ'),
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) →
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
          fc i t = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g g_bg
                  (symmS (I := I) (M := M) g (F t)) hδ'_lt
                  (gFibreOpBound_symmS (I := I) (M := M) g (F t)
                    (hδ' t)))) i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ R) := by
  classical
  obtain ⟨fc, hfc, hpinLo⟩ :=
    force_jet_of_mass (I := I) (M := M) g g_bg hR hδ hreal hcore
      hT hT1 fLo hfield_mem hforce hspatial
  obtain ⟨fHi, hpinHi, _hincl⟩ :=
    force_promote_two (I := I) (M := M) g hT fc hfc fLo hpinLo
  let u : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T :=
    maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi
  have hcross := duhamel_mode_pin (I := I) (M := M)
    g hT hT1 fLo fHi fc hfc hpinLo hpinHi
  have hcross' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      timeH1.toFun u t =
        tensorHsCongr (I := I) (M := M) g 0 2
          (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
          ((duhamelCross (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo).repr t) := by
    simpa only [u] using hcross
  have hstate := direct_state_bound (I := I) (M := M)
    g hR hT hT1 fLo u hcross' hfield_mem
  obtain ⟨B2, hB2s, hB2⟩ := hfc.2 0 (2 : ℝ) (by norm_num)
  have hmass2 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      Summable B ∧ ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i t) ^ 2 ≤ B i :=
    ⟨B2, hB2s, fun i t ht => by simpa only [iteratedDeriv_zero] using hB2 i t ht⟩
  have hf_id := carrier_coeff_pmConv (I := I) (M := M)
    g hT hT1 fHi fc (fun i => (hfc.1 i).continuous) hmass2 hpinHi
  have hf_id' : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
    simpa only [u] using hf_id
  obtain ⟨R₀, hR₀, hrealize⟩ := direct_radius (I := I) (M := M)
    g hT u fc hfc hf_id'
  have hforceOut := direct_force_coeff (I := I) (M := M)
    g g_bg hR hδ hreal hcore hT hT1 fLo hfield_mem hforce
      u fc hfc hpinLo hcross' hstate hf_id'
  have htrace : timeH1.trace0 _ T u = 0 := by
    dsimp only [u]
    rw [maxRegDuhamelMap_trace0 (I := I) (M := M) (a := (2 : ℝ))
      (T := T) hT hT1]
    exact map_zero _
  exact ⟨u, fHi, fc, R₀, htrace, rfl, hpinHi, hfc.1, hfc.2, hf_id', hR₀,
    hrealize, hforceOut, hstate⟩

theorem exists_second_order_solution_with_all_order_spectral_jet_control
    (g : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) (2 : ℝ) T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
      (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ) (R₀ : ℝ),
      timeH1.trace0 _ T u = 0 ∧
      u = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi ∧
      (∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) ∧
      (∀ i, ContDiff ℝ ∞ (fc i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (fc i) t) ^ 2 ≤ B i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t) ∧
      0 < R₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀) ∧
      (∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ'_lt : δ' < 1)
          (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g (F t)) δ'),
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) →
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
          fc i t = tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
                (deTurckRemainderSection (I := I) (M := M) g (F t) hδ'_lt (hδ' t))) i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ Rcap) := by
  let hs := hlo.toIsLowRegularitySolutionAt
  let R := lowRegularityStateRadius Ctop B1 ρ P
  have hR : 0 < R := lowRegularityStateRadius_pos hs.hCtop hs.hB1 hs.hρ hs.hP
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hs.hP.le hs.hreal
  have hfield_mem : ∀ᵐ t ∂timeMeasure T,
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2)) fLo t ∈
        lowerState (I := I) (M := M) g 1 R := by
    exact field_mem_lower (I := I) (M := M) g 1 hT hT1
      (by nlinarith [hR.le]) fLo hs.hball
  have hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g g hR hs.hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1 hR.le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t) := by
    simpa only [R, hreal, boundedDeTurckRemainderOnLowerState] using hs.hforce
  obtain ⟨u, fHi, fc, R₀, htrace, hu, hpin, hsmooth, hmass, hmode,
      hR₀, hrealize, hforceRaw, hstate⟩ :=
    direct_jet_of_mass (I := I) (M := M) g g hR hs.hδ hreal hs.hcore
      hT hT1 fLo hfield_mem hforce
      (fun σ =>
        per_mode_limit_weighted_energy_bound_all_orders (I := I) (M := M)
          g hT hT1 fLo hlo σ)
  have hforce' : ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ}
      (hδ'_lt : δ' < 1)
      (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g (F t)) δ'),
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
        fc i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (deTurckRemainderSection (I := I) (M := M) g (F t) hδ'_lt (hδ' t))) i := by
    simpa only [deTurckRemainderSection] using hforceRaw
  have hstateCap : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖timeH1.toFun u t‖ ≤ Rcap := by
    intro t ht
    exact (hstate t ht).trans (by simpa only [R] using hs.hcap)
  exact ⟨u, fHi, fc, R₀, htrace, hu, hpin, hsmooth, hmass, hmode, hR₀,
    hrealize, hforce', hstateCap⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
