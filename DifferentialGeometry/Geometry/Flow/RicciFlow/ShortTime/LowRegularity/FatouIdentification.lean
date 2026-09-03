import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.AdaptedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.GalerkinForcingSequence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.DuhamelEstimates
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeL2EigenProjection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic
  (lowerState norm_maxRegDuhamelSolField_zero_le zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset finiteEigenComboHs finiteEigenComboHs_coeff
    finiteEigenCombo_spectral_normSq galerkinEnergy galerkinEnergy_continuousOn
    galerkinEnergy_nonneg mem_eigenIdxFinset
    smoothCcToTensorHs spatialEigenProj spatialEigenProj_apply tensorResolventL2_isCompactOperator
    timeL2EigenProj)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def galerkinSolutionMode (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (t : ℝ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
    (fun u => (timeModeCoeff (I := I) (M := M) (fseq N) i) u) t

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] theorem lowRegularityProjMode_zero (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    galerkinSolutionMode (I := I) (M := M) g₀ fseq N 0 i = 0 :=
  perModeConv_zero_left _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem galerkinSolutionMode_continuous (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 ≤ T)
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
      (Set.Icc (0 : ℝ) T) :=
  continuousOn_perModeConv_timeL2 _ _ hT

omit [BoundarylessManifold I M] in
theorem galerkinSolutionMode_finiteEigenCombo (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hT : 0 < T) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun (u t)) :
    ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t =
        finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  have hfix : timeL2EigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) T N fld
      = fld := projField_fixed (I := I) (M := M) g₀ 1 hT N (fseq N) u hnem
  have hproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) T N fld)
      =ᵐ[timeMeasure T] fun t =>
        spatialEigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) N (fld t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hpt : (fun t => fld t) =ᵐ[timeMeasure T] fun t =>
      spatialEigenProj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) N (fld t) := by
    rw [hfix] at hproj
    exact hproj
  have hmodes : ∀ᵐ t ∂(timeMeasure T),
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        (fld t).coeff i = galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i := by
    refine Filter.eventually_all_finset _ |>.2 (fun i _ => ?_)
    exact timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M)
      (h_compact := h_compact) hT (fseq N) i
  filter_upwards [hpt, hmodes] with t h1 h2
  rw [h1, spatialEigenProj_apply]
  refine TensorHs.ext (funext fun j => ?_)
  rw [finiteEigenComboHs_coeff, finiteEigenComboHs_coeff]
  by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · rw [if_pos hj, if_pos hj, h2 j hj]
  · rw [if_neg hj, if_neg hj]

omit [BoundarylessManifold I M] in
theorem galerkinProjectedForce_mode_eq (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 < T) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N)) t))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ⇑(timeModeCoeff (I := I) (M := M) (fseq N) i) =ᵐ[timeMeasure T]
      fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) i := by
  classical
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  set lift := aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR) fld
    with hlift
  have hcombo := galerkinSolutionMode_finiteEigenCombo (I := I) (M := M) g₀ hT N (Nfun := Nfun)
    fseq lift hnem
  have hcoe := aeSetLift_coe_ae (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR)
    fld hball
  filter_upwards [timeModeCoeff_coeFn (I := I) (M := M) (fseq N) i, hnem, hball,
    hcombo, hcoe] with t h1 h2 h3 h4 h5
  have hstate : ‖galLowView (I := I) (M := M) g₀ 1
      (finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
    rw [← h4]; exact h3
  have hsub : lift t =
      (⟨finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) (((1 : ℕ) : ℝ) + 2),
        hstate⟩ : lowerState (I := I) (M := M) g₀ 1 R) :=
    Subtype.ext (h5.trans h4)
  rw [h1, h2, hsub]
  simp only [projNfun, spatialProj_coeff]
  rw [galTameForce_eq (I := I) (M := M) g₀ 1 hR Nfun
    (eigenIdxFinset (I := I) (M := M) g₀ N) hstate i]

theorem galerkinProjectedForce_mode_continuous (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    {T : ℝ} (N : ℕ) (c : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hc : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => c t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (c t) i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowRegularityOuterRadius Ctop ρ P :=
    (lowRegularityOuterRadius_pos hCtop hρ hP).le
  have hκ0 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hκ : ∀ j ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      1 + TensorEigenIdx.lambda (I := I) (M := M) j ≤ (N : ℝ) + 1 := by
    intro j hj
    rw [mem_eigenIdxFinset] at hj
    linarith
  obtain ⟨K, hK⟩ :=
    tame_lip_balls
      (X := TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
      (D := lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P))
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
      (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) id isometry_id rfl
      (galLowView (I := I) (M := M) g₀ 1) Ctop B0 B1
      (lowRegularityOuterRadius Ctop ρ P) hCtop hB0 hB1 hQnn htame
      (Real.sqrt ((N : ℝ) + 1) * lowRegularityStateRadius Ctop B1 ρ P)
  exact galTameForce_contOn (I := I) (M := M) g₀ 1 hRpos.le
    (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal)
    (eigenIdxFinset (I := I) (M := M) g₀ N) hκ0 hκ hK c hc i

omit [BoundarylessManifold I M] in
theorem galerkinSolutionMode_hasDerivWithinAt (g₀ : SmoothRiemannianMetric I M) {R T : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hFcont : ContinuousOn (fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) i) (Set.Icc (0 : ℝ) T))
    (hFmode : ⇑(timeModeCoeff (I := I) (M := M) (fseq N) i) =ᵐ[timeMeasure T]
      fun t => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) i)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => galerkinSolutionMode (I := I) (M := M) g₀ fseq N s i)
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
          galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i +
        galTameForce (I := I) (M := M) g₀ 1 hR Nfun
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t) i)
      (Set.Ici t) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
  set G : ℝ → ℝ := fun s => galTameForce (I := I) (M := M) g₀ 1 hR Nfun
    (eigenIdxFinset (I := I) (M := M) g₀ N)
    (galerkinSolutionMode (I := I) (M := M) g₀ fseq N s) i with hG
  set F : ℝ → ℝ := Set.IccExtend hT.le (fun p : Set.Icc (0 : ℝ) T => G p.1) with hF
  have hFc : Continuous F := Continuous.Icc_extend' hFcont.domRestrict
  have hFeq : ∀ s ∈ Set.Icc (0 : ℝ) T, F s = G s := fun s hs =>
    Set.IccExtend_of_mem hT.le _ hs
  have hae : (fun s => (timeModeCoeff (I := I) (M := M) (fseq N) i) s)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] F := by
    filter_upwards [hFmode, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with s hs hsmem
    rw [hs, hFeq s hsmem]
  have hconv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      galerkinSolutionMode (I := I) (M := M) g₀ fseq N s i = perModeConv lam F s :=
    fun s hs => perModeConv_timeL2_congr lam hae hs
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hderiv := perModeConv_hasDerivAt lam hFc t
  rw [hFeq t htIcc, ← hconv t htIcc] at hderiv
  have hval : G t - lam * galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i =
      -lam * galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i + G t := by ring
  rw [hval] at hderiv
  have hmem : Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici t] t := by
    have h1 : Set.Iio T ∈ 𝓝[Set.Ici t] t :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
    refine Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) ?_
    rintro s ⟨hs1, hs2⟩
    exact ⟨le_trans ht.1 hs2, hs1.le⟩
  refine (hderiv.hasDerivWithinAt (s := Set.Ici t)).congr_of_eventuallyEq ?_
    (hconv t htIcc)
  filter_upwards [hmem] with s hs using hconv s hs

theorem exists_uniform_galerkin_energy_three_bound_of_integral_bound
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Bd Ctop₂ Kr2 Kr1 Kcap ε : ℝ}
    (hT : 0 < T)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd)
    (hrung : HasGalerkinEnergyThreeBound (I := I) (M := M) g₀ Ctop₂ Kr2 Kr1 Kcap)
    (hε : 0 < ε)
    (habs : Ctop₂ * (Kcap * (δ / (1 - δ) ^ 2)) +
      Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
      Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1) :
    ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  classical
  set U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g₀ fseq with hU
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => galerkinSolutionMode_continuous (I := I) (M := M) g₀ hT.le fseq N i
  have hUinit : ∀ N i, U N 0 i = 0 :=
    fun N i => lowRegularityProjMode_zero (I := I) (M := M) g₀ fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine galerkinSolutionMode_hasDerivWithinAt (I := I) (M := M) g₀ hT
      (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le N fseq i ?_ ?_ ht
    · exact galerkinProjectedForce_mode_continuous (I := I) (M := M) g₀ g₀ hδ hCtop hB0 hB1 hρ hP hreal
        htame N (U N) (fun j _ => hUcont N j (by assumption)) i
    · exact galerkinProjectedForce_mode_eq (I := I) (M := M) g₀
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le hT N fseq (hball N) (hnem N) i
  set EE : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 p.1) with hEE
  have hEEc : ∀ N, Continuous (EE N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 (hUcont N)).domRestrict
  have hEEnn : ∀ N, ∀ s : ℝ, 0 ≤ EE N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEEeq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  set Pr : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE N s with hPr
  have hPrHas : ∀ N, ∀ t : ℝ, HasDerivAt (Pr N) (EE N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEEc N).intervalIntegrable 0 t)
      (hEEc N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEEc N).continuousAt
  have hPr0 : ∀ N, Pr N 0 = 0 := fun N => intervalIntegral.integral_same
  have hPrnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Pr N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEEnn N s)
  have hPrcont : ∀ N, ContinuousOn (Pr N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hPrHas N t).continuousAt)).continuousOn
  have hPrderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (Pr N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 t) (Set.Ici t) t := by
    intro N t ht
    have h := hPrHas N t
    rw [hEEeq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ Bd := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE N s = ∫ s, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) 3 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEEeq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplit : Pr N t + ∫ s in t..T, EE N s = ∫ s in (0 : ℝ)..T, EE N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEEc N).intervalIntegrable 0 t) ((hEEc N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEEnn N s)
    have hfin := hL2H3 N
    rw [← hTint] at hfin
    linarith
  exact hrung.2.2.2.2 hδ hδ0 hδ3 hCtop hB1 hρ hP hreal hcore hUcont hUderiv
    hUinit hPr0 hPrnn hPrcont hPrderiv hPrbd hε habs

theorem exists_uniform_galerkin_energy_three_bound_for_projected_forcing_sequence (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ Ctop B0 B1 ρ P T Bd : ℝ}
    (hT : 0 < T)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g₀ 1
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) t ∈
        lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤ Bd) :
    ∃ Ctop₂ Kr2 Kr1 Cδ : ℝ, 0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
      ∀ {ε : ℝ}, 0 < ε →
        Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N)
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  obtain ⟨Ctop₂, Kr2, Kr1, Kcap, hrung⟩ :=
    exists_galerkin_energy_three_bound_parameters (I := I) (M := M) hDim g₀
  let Cδ : ℝ := Kcap * (δ / (1 - δ) ^ 2)
  refine ⟨Ctop₂, Kr2, Kr1, Cδ, hrung.1, hrung.2.1, hrung.2.2.1,
    mul_nonneg hrung.2.2.2.1 (div_nonneg hδ0 (sq_nonneg _)), ?_⟩
  intro ε hε habs
  exact exists_uniform_galerkin_energy_three_bound_of_integral_bound (I := I) (M := M) g₀ hT hδ hδ0 hδ3 hCtop hB0
    hB1 hρ hP hreal hcore htame fseq hball hnem hL2H3 hrung hε
    (by simpa only [Cδ] using habs)

omit [BoundarylessManifold I M] in
theorem galerkin_energy_three_integral_bound (g₀ : SmoothRiemannianMetric I M) {R T b : ℝ}
    (hT : 0 < T) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun (u t))
    (hnorm : ‖fseq N‖ ≤ b) :
    ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ∂(timeMeasure T) ≤
      ((1 + T) * b) ^ 2 := by
  classical
  set fld := maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) (fseq N) with hfld
  have hexp : ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) := by norm_num
  have hae : (fun t => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g₀ N)
      (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t)
      =ᵐ[timeMeasure T] fun t => ‖fld t‖ ^ 2 := by
    filter_upwards [galerkinSolutionMode_finiteEigenCombo (I := I) (M := M) g₀ hT N
      (Nfun := Nfun) fseq u hnem] with t ht
    rw [ht, finiteEigenCombo_spectral_normSq, hexp]
    simp only [galerkinEnergy, tensorSobolevWeight]
  rw [MeasureTheory.integral_congr_ae hae]
  have hint : ∫ t, ‖fld t‖ ^ 2 ∂(timeMeasure T) = ‖fld‖ ^ 2 :=
    (norm_sq_eq_integral fld).symm
  rw [hint]
  have hle : ‖fld‖ ≤ (1 + T) * b :=
    le_trans (norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g₀)
      hT (fseq N))
      (mul_le_mul_of_nonneg_left hnorm (by linarith))
  nlinarith [norm_nonneg fld, hle]

theorem exists_fatou_galerkin_approximation_energy_three_bound
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g₀ N)
          (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  have hsol := hlo.toIsLowRegularitySolutionAt
  obtain ⟨fseq, _hconv, hmode, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence_with_mode_convergence (I := I) (M := M) g₀ hT hT1 fLo hsol
  obtain ⟨ε, hε, habs⟩ := hlo.absorb
  refine ⟨fseq, hmode, ?_⟩
  refine exists_uniform_galerkin_energy_three_bound_of_integral_bound (I := I) (M := M) g₀ hT hsol.hδ hsol.hδ0
    hsol.hδ3 hsol.hCtop hsol.hB0 hsol.hB1 hsol.hρ hsol.hP hsol.hreal
    hsol.hcore hsol.htame fseq (fun N => (hpack N).2.1)
    (fun N => (hpack N).2.2.1) (Bd := ((1 + T) *
      (lowRegularityStateRadius Ctop B1 ρ P / 4)) ^ 2) (fun N => ?_)
    hlo.toHasGalerkinEnergyThreeBound hε habs
  exact galerkin_energy_three_integral_bound (I := I) (M := M) g₀ hT N fseq _ ((hpack N).2.2.1)
    ((hpack N).2.2.2.2.2)

theorem exists_fatou_galerkin_approximation_energy_three_bound_from_dimension (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo) :
    ∃ (Ctop B1 ρ P : ℝ)
      (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∃ Ctop₂ Kr2 Kr1 Cδ : ℝ, 0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
        ∀ {ε : ℝ}, 0 < ε →
          Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
              Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
          ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N)
              (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) 3 t ≤ Φ := by
  obtain ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, _hconv, hmode, hpack⟩ :=
    galerkin_projected_forcing_sequence_mode_tendsto (I := I) (M := M) g₀ hT hT1 fLo hlo
  refine ⟨Ctop, B1, ρ, P, fseq, hmode, ?_⟩
  refine exists_uniform_galerkin_energy_three_bound_for_projected_forcing_sequence (I := I) (M := M) hDim g₀ hT hδ hδ0 hδ3 hCtop hB0 hB1
    hρ hP hreal hcore htame fseq (fun N => (hpack N).2.1)
    (fun N => (hpack N).2.2.1) (Bd := ((1 + T) *
      (lowRegularityStateRadius Ctop B1 ρ P / 4)) ^ 2) (fun N => ?_)
  exact galerkin_energy_three_integral_bound (I := I) (M := M) g₀ hT N fseq _ ((hpack N).2.2.1)
    ((hpack N).2.2.2.2.2)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
