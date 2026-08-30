import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.GalerkinSobolevThreePairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FatouIdentification

set_option autoImplicit false

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
open DifferentialGeometry.Analysis.Parabolic (lowerState zero_mem_lowerState)
open DifferentialGeometry.Analysis.Spectral
  (continuousOn_galerkinForcing_field eigenIdxFinset finiteEigenComboHs galerkinEnergy
    galerkinEnergy_continuousOn galerkinEnergy_nonneg smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem galerkinSolutionMode_state_bound
    (g : SmoothRiemannianMetric I M) {R T : ℝ}
    (hT : 0 < T) (N : ℕ)
    {Nfun : lowerState (I := I) (M := M) g 1 R →
      TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)}
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (u : ℝ → lowerState (I := I) (M := M) g 1 R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N) t ∈ lowerState (I := I) (M := M) g 1 R)
    (hnem : ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g 1 N Nfun (u t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N)
          (galerkinSolutionMode (I := I) (M := M) g fseq N t)
          (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
  let U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g fseq
  have hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun i _ => galerkinSolutionMode_continuous (I := I) (M := M) g hT.le fseq N i
  have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g 1 U N hUcont
  have hview : ContinuousOn
      (fun t => galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N) (U N t)
          (((1 : ℕ) : ℝ) + 2))) (Set.Icc (0 : ℝ) T) :=
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (((1 : ℕ) : ℝ) + 1) ≤ ((1 : ℕ) : ℝ) + 2 by
        norm_num)).continuous.comp_continuousOn hfield
  have hcont : ContinuousOn
      (fun t => ‖galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N) (U N t)
          (((1 : ℕ) : ℝ) + 2))‖) (Set.Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn hview
  have hcombo := galerkinSolutionMode_finiteEigenCombo (I := I) (M := M) g hT N fseq u hnem
  have hae : ∀ᵐ t ∂(timeMeasure T),
      ‖galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N) (U N t)
          (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
    filter_upwards [hball, hcombo] with t ht htc
    rw [← htc]
    exact ht
  have hmincont : ContinuousOn
      (fun t => ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g
            (eigenIdxFinset (I := I) (M := M) g N) (U N t)
            (((1 : ℕ) : ℝ) + 2))‖ ⊓ R)
      (Set.Icc (0 : ℝ) T) := hcont.inf continuousOn_const
  have haeeq :
      (fun t => ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g
            (eigenIdxFinset (I := I) (M := M) g N) (U N t)
            (((1 : ℕ) : ℝ) + 2))‖) =ᵐ[
        (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T)]
      (fun t => ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g
            (eigenIdxFinset (I := I) (M := M) g N) (U N t)
            (((1 : ℕ) : ℝ) + 2))‖ ⊓ R) := by
    filter_upwards [hae] with t ht
    exact (min_eq_left ht).symm
  have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) (ne_of_lt hT) haeeq hcont hmincont
  intro t ht
  have hmin := heq ht
  change ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g N) (U N t)
        (((1 : ℕ) : ℝ) + 2))‖ =
      ‖galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N) (U N t)
          (((1 : ℕ) : ℝ) + 2))‖ ⊓ R at hmin
  have hle : ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g N) (U N t)
        (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
    rw [hmin]
    exact inf_le_right
  simpa only [U] using hle

theorem exists_uniform_galerkin_energy_three_dissipation_four_bound_background_of_pairing_bounds
    (g gBase : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Bd G : ℝ}
    (hT : 0 < T)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ
      (lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 * ‖galLowView (I := I) (M := M) g 1
            ((u.1 : TensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 * (‖(u.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(v.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g 1
              ((u.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hG : 0 ≤ G)
    (hpair : ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ lowRegularityStateRadius Ctop B1 ρ P →
      2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal) F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        G * ((∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
          (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) ^ 2))
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N) t ∈ lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g 1 N
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N)
      (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ∂(timeMeasure T) ≤ Bd) :
    ∃ Φ3 Φ4 : ℝ,
      (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N)
          (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ3) ∧
      (∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ∂(timeMeasure T) ≤ Φ4) := by
  classical
  let U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g fseq
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => galerkinSolutionMode_continuous (I := I) (M := M) g hT.le fseq N i
  have hUinit : ∀ N i, U N 0 i = 0 :=
    fun N i => lowRegularityProjMode_zero (I := I) (M := M) g fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
            (eigenIdxFinset (I := I) (M := M) g N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine galerkinSolutionMode_hasDerivWithinAt (I := I) (M := M) g hT
      (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le N fseq i ?_ ?_ ht
    · exact galerkinProjectedForce_mode_continuous (I := I) (M := M) g gBase hδ hCtop hB0 hB1 hρ hP
        hreal htame N (U N) (fun j _ => hUcont N j (by assumption)) i
    · exact galerkinProjectedForce_mode_eq (I := I) (M := M) g
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le hT N fseq
        (hball N) (hnem N) i
  have hstate : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g N) (U N t)
          (((1 : ℕ) : ℝ) + 2))‖ ≤ lowRegularityStateRadius Ctop B1 ρ P := by
    intro N t ht
    simpa only [U] using galerkinSolutionMode_state_bound (I := I) (M := M) g hT N
      fseq (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1
        (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
        (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N)) t) (hball N) (hnem N) t ht
  let EE : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 p.1)
  have hEEc : ∀ N, Continuous (EE N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 (hUcont N)).domRestrict
  have hEEnn : ∀ N, ∀ s : ℝ, 0 ≤ EE N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEEeq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  let Pr : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE N s
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
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 t) (Set.Ici t) t := by
    intro N t ht
    have h := hPrHas N t
    rw [hEEeq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hPrbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, Pr N t ≤ Bd := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE N s = ∫ s,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 s ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEEeq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplitPr : Pr N t + ∫ s in t..T, EE N s = ∫ s in (0 : ℝ)..T, EE N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEEc N).intervalIntegrable 0 t) ((hEEc N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEEnn N s)
    have hfin := hL2H3 N
    rw [← hTint] at hfin
    linarith
  let EE4 : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 p.1)
  have hEE4c : ∀ N, Continuous (EE4 N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 (hUcont N)).domRestrict
  have hEE4nn : ∀ N, ∀ s : ℝ, 0 ≤ EE4 N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEE4eq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE4 N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  let D4 : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE4 N s
  have hD4Has : ∀ N, ∀ t : ℝ, HasDerivAt (D4 N) (EE4 N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEE4c N).intervalIntegrable 0 t)
      (hEE4c N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEE4c N).continuousAt
  have hD40 : ∀ N, D4 N 0 = 0 := fun N => intervalIntegral.integral_same
  have hD4nn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ D4 N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEE4nn N s)
  have hD4cont : ∀ N, ContinuousOn (D4 N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hD4Has N t).continuousAt)).continuousOn
  have hD4deriv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (D4 N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) (3 + 1) t)
        (Set.Ici t) t := by
    intro N t ht
    have h := hD4Has N t
    rw [hEE4eq N t ⟨ht.1, ht.2.le⟩] at h
    rw [show (3 + 1 : ℝ) = 4 by norm_num]
    exact h.hasDerivWithinAt
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  let hrealR := lowRegularityMetricRealization (I := I) (M := M) g
    (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal
  obtain ⟨Cseed, hCseed, hseed⟩ := exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g gBase
    hRpos hδ hrealR hcore
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
          tensorSobolevWeight (I := I) (M := M) i 3 *
            (U N t i * galTameForce (I := I) (M := M) g 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g N) (U N t) i) ≤
        1 * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N) (3 + 1) t +
          (0 + G * (1 + galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 t)) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 t +
          2 * Cseed 3 * Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 t) + 0 := by
    intro N t ht
    let F := eigenIdxFinset (I := I) (M := M) g N
    let arm := galerkinActionVectorBackground (I := I) (M := M) g gBase hRpos.le hδ hrealR F (U N t)
    let seed := boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hRpos.le⟩
    let force := galTameForce (I := I) (M := M) g 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
      F (U N t)
    have hsplit : ∀ i ∈ F, force i = arm.coeff i + seed.coeff i := by
      intro i hi
      dsimp only [force, arm, seed]
      rw [galForceArmBackground (I := I) (M := M) g gBase hδ hδ0 hδ3 hCtop hB1 hρ hP
        hreal hcore F (U N t) i, if_pos hi]
      simp only [galerkinActionVectorBackground]
      module
    have harm := hpair F (U N t) (by
      simpa only [F] using hstate N t ⟨ht.1, ht.2.le⟩)
    have hstat : ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (seed.coeff i) ^ 2 ≤
          Cseed 3 ^ 2 := by
      have h := hseed 3 F
      simpa only [seed, boundedDeTurckRemainderOnLowerState, Nat.cast_ofNat] using h
    have hstatPair := abs_sum_sameScale_le (I := I) (M := M) F (3 : ℝ)
      (U N t) (fun i => seed.coeff i)
    have hsqrtstat : Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (seed.coeff i) ^ 2) ≤ Cseed 3 := by
      have hs := Real.sqrt_le_sqrt hstat
      simpa only [Real.sqrt_sq (hCseed 3)] using hs
    have hstatPair' : 2 * |∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * seed.coeff i)| ≤
        2 * Cseed 3 * Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (U N t i) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtstat
        (Real.sqrt_nonneg (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (U N t i) ^ 2))
      have hpairle := hstatPair.trans hmul
      nlinarith [hpairle]
    have hsum : ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * force i) =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * arm.coeff i)) +
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * seed.coeff i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hsplit i hi]
      ring
    have hsigned : 2 * ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * force i) ≤
        2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * arm.coeff i)| +
        2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * seed.coeff i)| := by
      rw [hsum]
      nlinarith [le_abs_self (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (U N t i * arm.coeff i)),
        le_abs_self (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
            (U N t i * seed.coeff i))]
    generalize hArmPair : (2 * |∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
        (U N t i * arm.coeff i)|) = armPair at harm hsigned
    generalize hSeedPair : (2 * |∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
        (U N t i * seed.coeff i)|) = seedPair at hstatPair' hsigned
    generalize hArmBound :
      (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i) ^ 2) +
        G * ((∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
            (U N t i) ^ 2) +
          (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
            (U N t i) ^ 2) ^ 2) = armBound at harm
    generalize hSeedBound : (2 * Cseed 3 * Real.sqrt (∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
        (U N t i) ^ 2)) = seedBound at hstatPair'
    have hbound : armPair + seedPair ≤ armBound + seedBound :=
      add_le_add harm hstatPair'
    unfold galerkinEnergy
    norm_num only [one_mul, zero_add, add_zero, Nat.cast_ofNat] at ⊢
    calc
      _ ≤ armPair + seedPair := by
        dsimp only [F, force] at hsigned ⊢
        exact hsigned
      _ ≤ armBound + seedBound := hbound
      _ = _ := by
        rw [← hArmBound, ← hSeedBound]
        dsimp only [F]
        ring
  have hinit : ∀ N, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 0 ≤ 0 := by
    intro N
    have hz : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 3 0 = 0 := by
      unfold galerkinEnergy
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hUinit N i]
      ring
    rw [hz]
  obtain ⟨Bound, hBound⟩ := galRiderDiss (I := I) (M := M) (g := g)
    (r := 0) (s₀ := 2)
    (U := U) (T := T) (σ := 3)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
      (eigenIdxFinset (I := I) (M := M) g N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g N)
    (Cδ := 1) (Cmid := 0) (seed := 2 * Cseed 3) (B0 := 0)
    (c₀ := 0) (Crid := G) (B := Bd) (P := Pr) (D := D4)
    (by norm_num) le_rfl (mul_nonneg (by norm_num) (hCseed 3)) le_rfl hG
    hPr0 hPrnn hPrcont hPrderiv hPrbd hD40 hD4nn hD4cont hD4deriv
    hUcont hUderiv hclosure hinit
  have hD4time : ∀ N, D4 N T = ∫ t, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t ∂(timeMeasure T) := by
    intro N
    dsimp only [D4]
    rw [intervalIntegral.integral_congr
      (g := fun s => galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 s)
      (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEE4eq N s hs),
      intervalIntegral.integral_of_le hT.le, timeMeasure,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine ⟨Bound, Bound, ?_, ?_⟩
  · intro N t ht
    exact (hBound N t ht).1
  · intro N
    rw [← hD4time N]
    have h := (hBound N T ⟨hT.le, le_rfl⟩).2
    norm_num at h ⊢
    exact h

theorem exists_uniform_galerkin_energy_three_bound_background_of_pairing_bounds
    (g gBase : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Bd G : ℝ}
    (hT : 0 < T)
    (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ
      (lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (htame : ∀ u v : lowerState (I := I) (M := M) g 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 * ‖galLowView (I := I) (M := M) g 1
            ((u.1 : TensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 * (‖(u.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(v.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g 1
              ((u.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hG : 0 ≤ G)
    (hpair : ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ lowRegularityStateRadius Ctop B1 ρ P →
      2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
          (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal) F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        G * ((∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
          (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) ^ 2))
    (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N) t ∈ lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g 1 N
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hL2H3 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N)
      (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ∂(timeMeasure T) ≤ Bd) :
    ∃ Φ : ℝ, ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ := by
  obtain ⟨Φ3, _, hΦ3, _⟩ := exists_uniform_galerkin_energy_three_dissipation_four_bound_background_of_pairing_bounds
    (I := I) (M := M) g gBase hT hδ hδ0 hδ3 hCtop hB0 hB1 hρ hP
    hreal hcore htame hG hpair fseq hball hnem hL2H3
  exact ⟨Φ3, hΦ3⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
