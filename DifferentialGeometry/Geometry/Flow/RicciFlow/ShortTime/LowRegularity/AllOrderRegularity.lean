import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.HigherOrderEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegSolutionRegularity

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
open DifferentialGeometry.Analysis.Spectral
  (JetSpectralMassControl ccTensorToHs ccTensorToHs_coeff ccToHsLin deTurckSmoothN
    deTurckSmoothN_coeff
    deTurckSmoothRemainder exists_smoothCcPath_realizing_coeff gFibreOpBound_symmS
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass
    hs2_opBound_at_two maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
    perModeConv_allOrder_timeDeriv_spectralMass_le
    perModeConv_finiteOrder_timeJet_spectralMass_gain smoothCcToTensorHs
    smoothCcToTensorHs_coeff smoothCcToTensorHs_smul symmCoeffPath
    symmCoeffPath_contDiff symmCoeffPath_realizes symmCoeffPath_spectralMass
    tensorHsInclusion_smoothCcToTensorHs
    tensorResolventL2_isCompactOperator contDiffOn_Icc_scalar_globalExtend)
open DifferentialGeometry.Analysis.Elliptic (rawTensorConnLapSmooth)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsCongr_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ) {a b : ℝ}
    (h : a = b) (v : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsCongr (I := I) (M := M) g r s h v).coeff i = v.coeff i := by
  cases h
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
noncomputable def deTurckRemainderSection (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ) :
    SmoothCcTensor g 0 2 :=
  deTurckSmoothRemainder (I := I) g g (symmS (I := I) (M := M) g S) hδ_lt
    (gFibreOpBound_symmS (I := I) (M := M) g S hδ)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem coord_eq_smoothN
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
          (firstOrderCoreActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    {T : ℝ} (hT : 0 < T)
    (u : MaxRegSolutionSpace (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (hUball : ∀ᵐ t ∂timeMeasure T, ‖timeH1.toFun u t‖ ≤ R)
    (hi : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) T)
    (hlink : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (hi t) = timeH1.toFun u t)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hforceId : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (hi t)))
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (fc i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i)
    (hcpin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t)
    (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ_lt : δ' < 1)
    (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (F t)) δ')
    (h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
      SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
      fc i t = tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (deTurckRemainderSection (I := I) (M := M) g (F t) hδ_lt (hδ' t))) i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
  have hsm2 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) =
        timeH1.toFun u t := by
    intro t ht
    refine tensorHs.ext (funext fun j => ?_)
    rw [smoothCcToTensorHs_coeff, h_pin t ht, tensorHsToL2_tensorL2Coeff]
  have hφ_smooth : ∀ i, ContDiff ℝ ∞
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i)) :=
    fun i => perModeConv_contDiff_of_contDiff ⊤ _ (fc i) (hf_smooth i)
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
    perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (T := T) hT.le fc hf_smooth hf_mass 0
      ((3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity)
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))
      (Set.Icc (0 : ℝ) T) := by
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (3 : ℝ))
      (σ' := (3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) ?_ _
      (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i))
      ?_ (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum ?_
    · have hring : (3 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) - 3 =
          ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by ring
      rw [hring]
      linarith
    · intro t ht i
      rw [smoothCcToTensorHs_coeff, h_pin t ht]
      exact hf_id t ht i
    · intro i t ht
      have h := hCmaj_le i t ht
      rwa [iteratedDeriv_zero] at h
  have hΨ_cont : ContinuousOn
      (fun t => lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t)))
      (Set.Icc (0 : ℝ) T) :=
    (lowerScaleNonlinearityWithFirstOrderOperator_continuous (I := I) (M := M) g hρ hδ0 hδ_le hreal' FLo
      hA2cont hFLo).comp_continuousOn hfield_cont
  have hae : ∀ i, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      fc i t =
        (lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
          (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i := by
    intro i
    filter_upwards [hcpin i, hforceId, hlink,
      MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := T))]
      with t hcp hfo hlk htmem
    have hv : tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (hi t) =
        smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, h_pin t htmem,
        tensorHsToL2_tensorL2Coeff, ← hlk, tensorHsInclusion_coeff_apply]
    have hsplit := hiN_incl (I := I) (M := M) g hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t))
    rw [tensorHsInclusion_smoothCcToTensorHs] at hsplit
    rw [← hcp, hfo, hv, ← hsplit, tensorHsInclusion_coeff_apply]
  have heqOn : ∀ i, Set.EqOn (fc i)
      (fun t => (lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i)
      (Set.Ico (0 : ℝ) T) := by
    intro i
    refine MeasureTheory.Measure.eqOn_Ico_of_ae_eq
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
      ((hf_smooth i).continuous.continuousOn) ?_
    · exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self (hae i)
    · exact (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (σ := (1 : ℝ)) i).continuous.comp_continuousOn
        (hΨ_cont.mono Set.Ico_subset_Icc_self)
  have hnorm_cont : ContinuousOn (fun t => ‖timeH1.toFun u t‖)
      (Set.Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn (timeH1.continuousOn_toFun u)
  have hmin_cont : ContinuousOn (fun s => min ‖timeH1.toFun u s‖ R)
      (Set.Icc (0 : ℝ) T) := ContinuousOn.inf hnorm_cont continuousOn_const
  have hballIco : ∀ t ∈ Set.Ico (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ R := by
    intro t ht
    have hmin : (fun s => min ‖timeH1.toFun u s‖ R)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ico (0 : ℝ) T)] fun s => ‖timeH1.toFun u s‖ := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (μ := MeasureTheory.volume) Set.Ico_subset_Icc_self hUball] with s hs
      exact min_eq_left hs
    have h := MeasureTheory.Measure.eqOn_Ico_of_ae_eq
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hmin
      (hmin_cont.mono Set.Ico_subset_Icc_self)
      (hnorm_cont.mono Set.Ico_subset_Icc_self) ht
    exact min_eq_left_iff.mp h
  intro t ht i
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R := by
    rw [tensorHsInclusion_smoothCcToTensorHs,
      norm_smoothCc_congr (I := I) (M := M) g
        (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) (F t), hsm2 t htIcc]
    exact hballIco t ht
  have hcongr3 : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) (F t)) =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  have hAff : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδlt hreal
          ⟨smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) (F t), hS⟩) =
      lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t)) := by
    rw [← hcongr3]
    exact deTurckRemainderOnLowerState_affine (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FLo hFLo hFLoCore
      ⟨smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) (F t), hS⟩
  refine (heqOn i ht).trans ?_
  change (lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
      (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) (F t))).coeff i = _
  rw [← hAff, tensorHsCongr_coeff,
    deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g g hR hδlt hreal hcoreN (F t) hS,
    smoothN_wd (I := I) (M := M) g g 1
      (symmS (I := I) (M := M) g (F t)) (symmS (I := I) (M := M) g (F t))
      hδlt (hreal _ (symm_h2_of_state (I := I) (M := M) g (F t) hS))
      hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g (F t) (hδ' t)) rfl,
    deTurckSmoothN_coeff]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem liftN_smoothN_coeff
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
          (firstOrderCoreActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    (S : SmoothCcTensor g 0 2)
    (hS2 : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R)
    (δ' : ℝ) (hδ_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) δ')
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
      (deTurckSmoothN (I := I) (M := M) g g 2
        (symmS (I := I) (M := M) g S) hδ_lt
        (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i := by
  have h1 : (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
      (lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S)).coeff i := by
    have hsplit := hiN_incl (I := I) (M := M) g hρ hδ0 hδ_le hreal' FHi FLo
      hA2sq hFComm (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)
    rw [tensorHsInclusion_smoothCcToTensorHs] at hsplit
    rw [← hsplit, tensorHsInclusion_coeff_apply]
  have hS : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      (smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) S)‖ ≤ R := by
    rw [tensorHsInclusion_smoothCcToTensorHs,
      norm_smoothCc_congr (I := I) (M := M) g
        (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num) S]
    exact hS2
  have hcongr3 : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
        (smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) S) =
      smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  have hAff : tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδlt hreal
          ⟨smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) S, hS⟩) =
      lowerScaleNonlinearityWithFirstOrderOperator (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FLo
        (smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) S) := by
    rw [← hcongr3]
    exact deTurckRemainderOnLowerState_affine (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FLo hFLo hFLoCore
      ⟨smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 2) S, hS⟩
  rw [h1, ← hAff, tensorHsCongr_coeff,
    deTurckRemainderOnLowerState_on_smooth (I := I) (M := M) g g hR hδlt hreal hcoreN S hS,
    smoothN_wd (I := I) (M := M) g g 1
      (symmS (I := I) (M := M) g S) (symmS (I := I) (M := M) g S)
      hδlt (hreal _ (symm_h2_of_state (I := I) (M := M) g S hS))
      hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g S hδ') rfl]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem lowRegularity_forceJetStep
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    {T : ℝ} (hT : 0 < T)
    (w : ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (w t)‖ ≤ R)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t)))
    (k : ℕ) (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fHi t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] ψ i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
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
      (smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)).coeff i = φ i t := by
    intro t ht i
    rw [smoothCcToTensorHs_coeff]
    exact hF_coeff t ht i
  have hfield_cont : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t))
      (Set.Icc (0 : ℝ) T) := by
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ := hmass0
      ((2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity)
    refine tensorHs_continuousOn_of_coeff_of_higher_mass (I := I) (M := M) g
      (σ := (2 : ℝ))
      (σ' := (2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) ?_
      (s := Set.Icc (0 : ℝ) T)
      (fun t => smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)) φ
      hF_hs2 (fun i => (hφ_smooth i).continuous.continuousOn) hCmaj_sum
      (fun i t ht => hCmaj_le i t ht)
    have hring : (2 : ℝ) + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) - 2 =
        ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 := by ring
    rw [hring]
    linarith
  have hball_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ≤ R := by
    have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ i, (w t).coeff i = φ i t := (MeasureTheory.ae_all_iff).2 hw
    filter_upwards [hw_ball, hall, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hbt htall htmem
    have heq : smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) =
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num) (w t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [hF_hs2 t htmem j, tensorHsInclusion_coeff_apply, htall j]
    rw [heq]
    exact hbt
  have hball_pt : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ≤ R := by
    have hcont_norm : ContinuousOn
        (fun t => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖)
        (Set.Icc (0 : ℝ) T) := continuous_norm.comp_continuousOn hfield_cont
    have hg_cont : ContinuousOn
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖ ⊓ R)
        (Set.Icc (0 : ℝ) T) := hcont_norm.inf continuousOn_const
    have hfg : (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Icc (0 : ℝ) T)]
        (fun s => ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F s)‖ ⊓ R) := by
      filter_upwards [hball_ae] with s hs
      exact (min_eq_left hs).symm
    have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hT) hfg
      hcont_norm hg_cont
    intro t ht
    have hmin : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t)‖ ⊓ R := heq ht
    rw [hmin]
    exact inf_le_right
  have hδF : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (F t)) δ := by
    intro t
    refine hreal' (F t) ?_
    have hcc : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (F t) =
        smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) (F t) := by
      refine tensorHs.ext (funext fun j => ?_)
      rw [ccTensorToHs_coeff, smoothCcToTensorHs_coeff]
    rw [hcc]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · exact le_trans (hball_pt t ht) hRρ
    · have hF0 : F t = (0 : SmoothCcTensor g 0 2) := by
        simp only [hF_def, ht, if_neg, not_false_iff]
      have hz : smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
        have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
          (zero_smul ℝ _).symm
        rw [h0, smoothCcToTensorHs_smul, zero_smul]
      rw [hF0, hz, norm_zero]
      exact hρ.le
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
      (fun j' => (hφ_smooth j').of_le (mod_cast hjk)) τ
      (hφ_mass j hjk τ hτ)
      (hφ_mass j hjk (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hcoeff' : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
            (symmS (I := I) (M := M) g (F t))) i =
        symmCoeffPath (I := I) (M := M) g φ i t := fun t ht i =>
    symmCoeffPath_realizes (I := I) (M := M) g φ (F t) (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_coeff⟩ :=
    deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass (I := I) (M := M)
      g g 2 hT k (fun t => symmS (I := I) (M := M) g (F t)) hδlt hδS
      (symmCoeffPath (I := I) (M := M) g φ) hφ'_smooth hcoeff' hφ'_mass
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  have hall : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  filter_upwards [hfix, hall, MeasureTheory.ae_restrict_mem
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t hfx htall htmem
  have hv : tensorHsCongr (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t) =
      smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t) := by
    refine tensorHs.ext (funext fun j => ?_)
    rw [tensorHsCongr_coeff, smoothCcToTensorHs_coeff, htall j]
    exact (hF_coeff t htmem j).symm
  calc (fHi t).coeff i
      = (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (tensorHsCongr (I := I) (M := M) g 0 2
            (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num) (w t))).coeff i := by rw [hfx]
    _ = (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
          (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) (F t))).coeff i := by rw [hv]
    _ = (deTurckSmoothN (I := I) (M := M) g g 2
          (symmS (I := I) (M := M) g (F t)) hδlt (hδS t)).coeff i :=
        hbridge (F t) (hball_pt t htmem) δ hδlt (hδF t) i
    _ = ψ i t := hψ_coeff t htmem i

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
private theorem lowRegularity_forceDriver
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    {T : ℝ} (hT : 0 < T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R)
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cσ) :
    ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (fHi t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] f i) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  set w : ℝ → tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2) :=
    fun t => maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t with hw_def
  set ρw : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρw_def
  have hρw_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρw := by rw [hρw_def]; linarith
  have hpmc_contOn : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) (Set.Icc (0 : ℝ) T) :=
    fun i => continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) fHi i) hT.le
  set c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := fun i =>
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) p.1) with hc_def
  have hc_cont : ∀ i, Continuous (c i) := fun i =>
    Continuous.Icc_extend' ((hpmc_contOn i).restrict)
  have hc_eqOn : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) (Set.Icc (0 : ℝ) T) := by
    intro i t ht
    exact Set.IccExtend_of_mem hT.le _ ht
  have hs_mass : ∀ τ : ℝ, 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ B i := by
    intro τ hτ
    obtain ⟨Cτ, hCτ⟩ := hspatial (τ + ρw)
    refine ⟨fun i => Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw),
      (tensorEigen_summable_negpow (I := I) (M := M) g ρw hρw_gt).mul_left Cτ, ?_⟩
    intro i t ht
    obtain ⟨hsum_t, hbd_t⟩ := hCτ t ht
    have hterm : tensorSobolevWeight (I := I) (M := M) i (τ + ρw)
        * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cτ :=
      le_trans (hsum_t.le_tsum i (fun j _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) j (τ + ρw)) (sq_nonneg _))) hbd_t
    have hsplit : tensorSobolevWeight (I := I) (M := M) i τ
        = tensorSobolevWeight (I := I) (M := M) i (-ρw)
          * tensorSobolevWeight (I := I) (M := M) i (τ + ρw) := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρw) (τ + ρw)]
      congr 1
      ring
    calc tensorSobolevWeight (I := I) (M := M) i τ
          * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-ρw)
            * (tensorSobolevWeight (I := I) (M := M) i (τ + ρw)
              * (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) := by
          rw [hsplit]; ring
      _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρw) * Cτ :=
          mul_le_mul_of_nonneg_left hterm
            (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρw))
      _ = Cτ * tensorSobolevWeight (I := I) (M := M) i (-ρw) := by ring
  have hcoeff_id : ∀ i, (fun t => (w t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u)) := fun i =>
    timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) hT hc fHi i
  have hfHi_tmc : ∀ i, (fun t => (fHi t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
        (fun s => (timeModeCoeff (I := I) (M := M) fHi i) s) := fun i =>
    (timeModeCoeff_coeFn (I := I) (M := M) fHi i).symm
  intro k
  induction k with
  | zero =>
    exact lowRegularity_forceJetStep (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
      FHi hbridge hT w hballU fHi hfix 0 c
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
    have hw_coeff : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) fHi i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] (fk i) :=
        (hfHi_tmc i).symm.trans (hfk_ae i)
      have hpm : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
        exact perModeConv_timeL2_congr (T := T)
          (TensorEigenIdx.lambda (I := I) (M := M) i) hfk_tmc ht
      exact (hcoeff_id i).trans hpm
    exact lowRegularity_forceJetStep (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
      FHi hbridge hT w hballU fHi hfix (k + 1)
      (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
      hφ_cont hφ_mass hw_coeff

omit [BoundarylessManifold I M] in
theorem carrier_coeff_pmConv
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_cont : ∀ i, Continuous (fc i))
    (hf_mass0 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i t) ^ 2 ≤ B i)
    (hpin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
            ((maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT
              (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).toFun t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass0
  set pr : ℝ → ℝ :=
    fun t => ((Set.projIcc (0 : ℝ) T hT.le t : Set.Icc (0 : ℝ) T) : ℝ) with hpr_def
  have hpr_mem : ∀ t, pr t ∈ Set.Icc (0 : ℝ) T :=
    fun t => (Set.projIcc (0 : ℝ) T hT.le t).2
  have hpr_id : ∀ t ∈ Set.Icc (0 : ℝ) T, pr t = t := by
    intro t ht
    rw [hpr_def]
    simp only [Set.projIcc_of_mem hT.le ht]
  have hpr_cont : Continuous pr :=
    continuous_subtype_val.comp continuous_projIcc
  set Frep : ℝ → tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) :=
    fun t => tensorHs_of_spectralMass_majorant (I := I) (M := M)
      (fun i => fc i (pr t)) B0 hB0_sum
      (fun i => hB0_le i (pr t) (hpr_mem t)) with hFrep_def
  have hFrep_coeff : ∀ (t : ℝ) (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      (Frep t).coeff i = fc i (pr t) := fun _ _ => rfl
  have hFcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      ContinuousOn (fun t => (Frep t).coeff i) (Set.Icc (0 : ℝ) T) := fun i =>
    ((hf_cont i).comp hpr_cont).continuousOn
  have hall : ∀ᵐ t ∂(timeMeasure T),
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2, (fHi t).coeff i = fc i t :=
    (MeasureTheory.ae_all_iff).2 hpin
  have hF_rep : (⇑fHi) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] Frep := by
    filter_upwards [hall, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht htmem
    refine tensorHs.ext (funext fun i => ?_)
    rw [ht i, hFrep_coeff t i, hpr_id t htmem]
  intro t ht i
  rw [tensorHsToL2_tensorL2Coeff,
    carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
      (h_compact := hc) (a := (2 : ℝ)) hT hT le_rfl fHi hFcoord hF_rep i ht]
  refine perModeConv_timeL2_congr (T := T)
    (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ ht
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
    (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
  rw [Set.IccExtend_of_mem hT.le _ hs, hFrep_coeff s i, hpr_id s hs]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
theorem exists_spatial_weighted_energy_bound_all_orders
    (g : SmoothRiemannianMetric I M)
    {δ : ℝ}
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    {Ctop B0 B1 D ρlo P Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρlo) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap)
    (σ : ℝ) :
    ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fHi i) u) t) ^ 2 ≤ Cσ := by
  have hfeq : timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) fHi = fLo := by
    refine MeasureTheory.Lp.ext ?_
    have hcoe := (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)).coeFn_compLpL
        (p := 2) (μ := timeMeasure T) fHi
    filter_upwards [hcoe, hincl] with t h1 h2
    exact h1.trans h2
  have hmode : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      timeModeCoeff (I := I) (M := M) fLo i =
        timeModeCoeff (I := I) (M := M) fHi i := by
    intro i
    rw [← hfeq]
    exact timeModeCoeff_timeL2Inclusion (I := I) (M := M)
      (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) fHi i
  obtain ⟨Cσ, hCσ⟩ :=
    per_mode_limit_weighted_energy_bound_all_orders (I := I) (M := M) g hT hT1 fLo hlo σ
  exact ⟨Cσ, fun t ht => by simpa only [hmode] using hCσ t ht⟩

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in
theorem exists_forcing_spectral_jet_mass_control (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) (hδlt : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hNcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g g hR hδlt hreal))
    (hcoreN : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g g hδlt hreal))
    (hA2cont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'))
    (hA2core : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal'
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (combinedLowerScaleActionCoefficients (I := I) (M := M) g
          hρ.le hδ0 hδ_le hreal' S).secondOrderActionThirdToFirstOrder (I := I) (M := M))
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    (FLo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)))
    (hFLo : Continuous FLo)
    (hFLoCore : ∀ S : SmoothCcTensor g 0 2,
      FLo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
        (radialLowerScaleActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M) +
          (firstOrderCoreActionCoefficients (I := I) (M := M)
            g hρ.le hδ0 hδ_le hreal' S).firstOrderActionSecondToFirstOrder (I := I) (M := M))
    (hA2sq : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp
          (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v) =
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num)))
    (hFComm : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)).comp (FHi x) =
        (FLo x).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R)
    {Ctop B0 B1 D ρlo P Rcap Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρlo) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
              ((maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT
                (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).toFun t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀) ∧
      ∃ fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ,
        JetSpectralMassControl (I := I) (M := M) g fc T ∧
        ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  have hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i :=
    fun S hS2 δ' hδ_lt hδ' i =>
      liftN_smoothN_coeff (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
        hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
        hA2sq hFComm S hS2 δ' hδ_lt hδ' i
  have hdrv := lowRegularity_forceDriver (I := I) (M := M) g hρ hRρ hδ0 hδ_le hreal'
    FHi hbridge hT fHi hfix hballU
    (fun σ => exists_spatial_weighted_energy_bound_all_orders (I := I) (M := M) g
      hT hT1 fHi fLo hincl hlo σ)
  choose Fk hFk_smooth hFk_mass hFk_ae using hdrv
  set f0 : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ := Fk 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) T ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (Fk k i) (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro k i
    have hae : (Fk k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)] (f0 i) :=
      (hFk_ae k i).symm.trans (hFk_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hFk_smooth k i).continuous).continuousOn
      ((hFk_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) T) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hFk_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) T) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hT (hf0_smoothOn i)
  choose fc hfc_smooth hfc_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) T →
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
  have hfc_pin : ∀ i, (fun t => (fHi t).coeff i) =ᵐ[timeMeasure T] fc i := by
    intro i
    refine (hFk_ae 0 i).trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with t ht
    exact hfc_eqOn i ht
  obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
    perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (T := T) hT.le fc hfc_smooth hfc_mass 0
      ((2 : ℝ) + 2) (by norm_num)
  have hCmaj_nn : ∀ i, 0 ≤ Cmaj i := fun i =>
    le_trans (mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) i ((2 : ℝ) + 2)) (sq_nonneg _))
      (hCmaj_le i 0 ⟨le_rfl, hT.le⟩)
  have hcarr := carrier_coeff_pmConv (I := I) (M := M) g hT fHi fc
    (fun i => (hfc_smooth i).continuous)
    (by
      obtain ⟨B, hBs, hBle⟩ := hfc_mass 0 (2 : ℝ) (by norm_num)
      refine ⟨B, hBs, fun i t ht => ?_⟩
      have h := hBle i t ht
      rwa [iteratedDeriv_zero] at h)
    hfc_pin
  refine ⟨Real.sqrt (∑' i, Cmaj i) + 1, ?_, ?_,
    fc, ⟨hfc_smooth, hfc_mass⟩, hfc_pin⟩
  · linarith only [Real.sqrt_nonneg (∑' i, Cmaj i)]
  · intro t ht S hS
    have hcoeff : ∀ i,
        (smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
      intro i
      rw [smoothCcToTensorHs_coeff, hS]
      exact hcarr t ht i
    have hptwise : ∀ i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℝ) + 2) *
        ((smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).coeff i) ^ 2 ≤
          Cmaj i := by
      intro i
      rw [hcoeff i]
      have h := hCmaj_le i t ht
      rwa [iteratedDeriv_zero] at h
    have hsq_le : ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ^ 2 ≤
        ∑' i, Cmaj i := by
      rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
      exact Summable.tsum_le_tsum hptwise
        ((smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S).weighted_summable)
        hCmaj_sum
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤
        Real.sqrt (∑' i, Cmaj i) := by
      rw [show ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ =
        Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq_le
    linarith only [hnorm_le]

theorem exists_second_order_solution_with_all_order_spectral_jet_control_of_compatible_solution (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) {Rcap : ℝ}
    (hre : HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Rcap)
    {Ctop B0 B1 D ρlo P Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hfLo : ∀ᵐ t ∂timeMeasure T, f t =
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t))
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρlo) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := 0) (s := 2) (2 : ℝ) T)
      (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
      (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ) (R₀ : ℝ),
      timeH1.trace0 _ T u = 0 ∧
      u = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT
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
      (∀ (F : ℝ → SmoothCcTensor g 0 2) {δ' : ℝ} (hδ_lt : δ' < 1)
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
                (deTurckRemainderSection (I := I) (M := M) g (F t) hδ_lt (hδ' t))) i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤ Rcap) := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
  obtain ⟨FHi, C2Hi, hA2Hi, hC2Hi, hA1Hi, uHi, fHi, ucs, FLo, R, hR, hreal,
    -, hhiL2, -, htr, hder, -, hfInc, -, -, -, -, -, hforceId,
    hRρ, hNcont, hcoreN, hA2cont, hA2core, -, -, hFLo, hFLoCore, hA2sq,
    hFComm, hballU, hRcapLe⟩ := hre
  have hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t := by
    filter_upwards [hfInc, hfLo] with t h1 h2
    refine (tensorHsCongr (I := I) (M := M) g 0 2
      (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)).injective ?_
    rw [tensorHsCongr_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num)
        (show (2 : ℝ) = (2 : ℝ) from rfl)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (show (1 : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t),
      tensorHsCongr_refl]
    exact h1.trans h2
  have hstateU : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun ucs.lo t‖ ≤ Rcap :=
    ucs.lo.norm_le_of_ae_le hT
      (by filter_upwards [hballU] with t ht using ht.trans hRcapLe)
  have hδlt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hfid0 := hforceId
  have hinit : ucs.lo.init = (0 : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) := by
    have h := htr
    rwa [timeH1.trace0_apply] at h
  have hduh : ucs.lo = maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT
      (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi := by
    refine timeH1.ext ?_ ?_
    · rw [hinit, maxRegDuhamelMap_init]
      exact (map_zero _).symm
    · have e1 : ucs.lo.deriv =
          timeScaleLaplacian (I := I) (M := M) (2 : ℝ) ucs.hiL2 + fHi := by
        rw [← timeH1.timeDeriv_apply]
        exact hder
      have e2 : (maxRegDuhamelMap (I := I) (M := M) (2 : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi).deriv =
          timeScaleLaplacian (I := I) (M := M) (2 : ℝ)
              (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
                (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi) + fHi := by
        rw [← timeH1.timeDeriv_apply]
        exact maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := hc)
          hT _ fHi
      rw [e1, e2, hhiL2]
  rw [hhiL2] at hforceId
  have hballD : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R := by
    filter_upwards [ucs.link, hballU] with t hlk hbt
    have hstep : tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t) =
        timeH1.toFun ucs.lo t := by
      rw [← hhiL2]
      exact hlk
    rw [hstep]
    exact hbt
  obtain ⟨R₀, hR₀_pos, hball, fc, ⟨hf_smooth, hf_mass⟩, hpin⟩ :=
    exists_forcing_spectral_jet_mass_control (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
      hA2sq hFComm hT hT1 fHi hforceId hballD fLo hincl hlo
  have hf_mass0 : ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) * (fc i s) ^ 2 ≤ B i := by
    obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 (2 : ℝ) (by norm_num)
    refine ⟨B0, hB0_sum, fun i s hs => ?_⟩
    have h := hB0_le i s hs
    rwa [iteratedDeriv_zero] at h
  have hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorL2Coeff (I := I) (M := M) hc
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2) hc
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun ucs.lo t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t := by
    intro t ht i
    rw [hduh]
    exact carrier_coeff_pmConv (I := I) (M := M) g hT fHi fc
      (fun j => (hf_smooth j).continuous) hf_mass0 hpin t ht i
  refine ⟨ucs.lo, fHi, fc, R₀, htr, hduh, hpin, hf_smooth, hf_mass, hf_id,
    hR₀_pos, ?_, ?_, hstateU⟩
  · intro t ht S hS
    exact hball t ht S (by rw [hS, hduh])
  · intro F δ' hδ_lt hδ' h_pin
    exact coord_eq_smoothN (I := I) (M := M) hDim g hR hρ hRρ hδ0 hδ_le hδlt
      hreal hreal' hNcont hcoreN hA2cont hA2core FHi FLo hFLo hFLoCore
      hA2sq hFComm hT ucs.lo hballU ucs.hiL2 ucs.link fHi hfid0 fc hf_smooth
      hf_mass hpin hf_id F hδ_lt hδ' h_pin


theorem exists_jointly_smooth_metric_solution_of_spectral_data (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (Nsec : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ),
      SmoothCcTensor g 0 2)
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (Nsec S hδ_lt hδ + rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (g := g) (r := 0) (s := 2) (2 : ℝ) T)
    (htrace : timeH1.trace0 _ T u = 0)
    (fc : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hf_smooth : ∀ i, ContDiff ℝ ∞ (fc i))
    (hf_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (fc i) t) ^ 2 ≤ B i)
    (hf_id : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) i =
        perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fc i) t)
    (hstate : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤
      1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose))
    {R₀ : ℝ}
    (hball_full : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ S : SmoothCcTensor g 0 2,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t) →
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) S‖ ≤ R₀)
    (hForce : ∀ (F : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ)
        (_h_pin : ∀ t ∈ Set.Icc (0 : ℝ) T,
          SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
            tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t))
        (_hball : ∀ t ∈ Set.Ico (0 : ℝ) T,
          ‖smoothCcToTensorHs (I := I) (M := M) g ((2 : ℝ) + 2) (F t)‖ ≤ R₀),
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i,
        fc i t = tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
              (Nsec (F t) hδ_lt (hδ t))) i) :
    ∃ (F : ℝ → SmoothCcTensor g 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ t)) := by
  obtain ⟨hC_pos, hC⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  exact maxreg_solution_jointly_smooth_representative_of_tame_nemytskii
    (I := I) (M := M) g 2 F_RHS Nsec hRepr hT hT1 u htrace fc hf_smooth hf_mass
    hf_id _ hC_pos hC hstate hball_full hForce


theorem exists_jointly_smooth_metric_solution_of_compatible_second_order_solution (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (deTurckRemainderSection (I := I) (M := M) g S hδ_lt hδ +
            rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) {Rcap : ℝ}
    (hre : HasCompatibleSecondOrderSolution (I := I) (M := M) g hρ hδ0 hδ_le hreal' hT hT1 f Rcap)
    {Ctop B0 B1 D ρlo P Ctop₂ Kr2 Kr1 Kcap : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hfLo : ∀ᵐ t ∂timeMeasure T, f t =
      tensorHsCongr (I := I) (M := M) g 0 2
        (show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num) (fLo t))
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρlo) (P := P)
      g hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap)
    (hRcapC : Rcap ≤
      1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose)) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) (2 : ℝ) T)
        (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
        (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g (F t)) δ'),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
          (F_RHS
            (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  obtain ⟨u, fHi, fc, R₀, htr, hduh, hpin, hf_smooth, hf_mass, hf_id,
    _, hball_full, hForce, hstateU⟩ :=
    exists_second_order_solution_with_all_order_spectral_jet_control_of_compatible_solution (I := I) (M := M) hDim g hρ hδ0 hδ_le hreal' hT hT1 f hre
      fLo hfLo hlo
  have hstate : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖timeH1.toFun u t‖ ≤
      1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose) :=
    fun t ht => (hstateU t ht).trans hRcapC
  exact ⟨u, exists_jointly_smooth_metric_solution_of_spectral_data (I := I) (M := M) hDim g F_RHS
    (deTurckRemainderSection (I := I) (M := M) g) hRepr hT hT1 u htr
    fc hf_smooth hf_mass hf_id hstate hball_full
    (fun F _ hδ_lt hδ' h_pin _ => hForce F hδ_lt hδ' h_pin)⟩

theorem exists_jointly_smooth_metric_solution_with_contraction_threshold (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (deTurckRemainderSection (I := I) (M := M) g S hδ_lt hδ +
            rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w) :
    ∃ B2 : ℝ, 0 ≤ B2 ∧
      ∀ {c : ℝ}, B2 ≤ c → c < 1 →
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (_hT : 0 < T) (_ : T ≤ T₀) (_hT1 : T ≤ 1),
            ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
                (g := g) (r := 0) (s := 2) (2 : ℝ) T)
                (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
                (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g (F t)) δ'),
              F 0 = 0 ∧
              (∀ t ∈ Set.Icc (0 : ℝ) T,
                SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
                  tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                    (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
              (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
                HasDerivWithinAt
                  (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
                  (F_RHS
                    (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t))
                      x v w)
                  (Set.Ici 0) t) ∧
              JointChartGramSmooth (I := I) T
                (fun t : ℝ =>
                  tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  obtain ⟨hC_pos, -⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, δ, Rcap, ρ, hδ, hδ_le, _hRcap,
      hRcapC, hρ, hreal', B2, hB2, hsolve⟩ :=
    exists_adapted_lowRegularity_solution_parameters (I := I) (M := M) hDim g
      (Rmax := 1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose))
      (div_pos one_pos (by linarith only [hC_pos]))
  refine ⟨B2, hB2, ?_⟩
  intro c hB2c hc1
  obtain ⟨T₀, hT₀, hpack⟩ := hsolve hB2c hc1
  refine ⟨T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨f, fLo, Ctop, B0, B1, D, ρlo, P, hre, hfLo, hlo⟩ :=
    hpack hT hTT₀ hT1
  exact exists_jointly_smooth_metric_solution_of_compatible_second_order_solution (I := I) (M := M) hDim g F_RHS hRepr hρ hδ.le hδ_le
    hreal' hT hT1 f hre fLo hfLo hlo hRcapC

theorem exists_jointly_smooth_metric_solution_for_short_time (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (F_RHS : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hRepr : ∀ (S : SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g
          (deTurckRemainderSection (I := I) (M := M) g S hδ_lt hδ +
            rawTensorConnLapSmooth (I := I) g 0 2 S) x v w =
        F_RHS (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) x v w) :
    ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ {T : ℝ} (_hT : 0 < T) (_ : T ≤ T₀) (_hT1 : T ≤ 1),
        ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
            (g := g) (r := 0) (s := 2) (2 : ℝ) T)
            (F : ℝ → SmoothCcTensor g 0 2) (δ' : ℝ) (hδ_lt : δ' < 1)
            (hδ' : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g (F t)) δ'),
          F 0 = 0 ∧
          (∀ t ∈ Set.Icc (0 : ℝ) T,
            SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (F t) =
              tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (timeH1.toFun u t)) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
            HasDerivWithinAt
              (fun s : ℝ => ccTensorBilinSymm (I := I) g (F s) x v w)
              (F_RHS
                (tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t))
                  x v w)
              (Set.Ici 0) t) ∧
          JointChartGramSmooth (I := I) T
            (fun t : ℝ =>
              tensorSectionRealizeMetric (I := I) g (F t) hδ_lt (hδ' t)) := by
  obtain ⟨hC_pos, -⟩ := (hs2_opBound_at_two (I := I) (M := M) hDim g).choose_spec
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, δ, Rcap, ρ, hδ, hδ_le, _hRcap,
      hRcapC, hρ, hreal', B2, _hB2, hB2lt, hsolve⟩ :=
    exists_adapted_lowRegularity_solution_parameters_with_contraction_threshold (I := I) (M := M) hDim g
      (Rmax := 1 / (2 * (hs2_opBound_at_two (I := I) (M := M) hDim g).choose))
      (div_pos one_pos (by linarith only [hC_pos]))
  let c : ℝ := (B2 + 1) / 2
  have hB2c : B2 ≤ c := by
    dsimp only [c]
    linarith
  have hc1 : c < 1 := by
    dsimp only [c]
    linarith only [hB2lt]
  obtain ⟨T₀, hT₀, hpack⟩ := hsolve hB2c hc1
  refine ⟨T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  obtain ⟨f, fLo, Ctop, B0, B1, D, ρout, P, hre, hfLo, hlo⟩ :=
    hpack hT hTT₀ hT1
  exact exists_jointly_smooth_metric_solution_of_compatible_second_order_solution (I := I) (M := M) hDim g F_RHS hRepr hρ hδ.le hδ_le
    hreal' hT hT1 f hre fLo hfLo hlo hRcapC

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
