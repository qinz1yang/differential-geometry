import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.GalerkinSobolevFourPairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.FatouLimitBounds

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
  (eigenIdxFinset finiteEigenComboHs galerkinEnergy galerkinEnergy_continuousOn
    galerkinEnergy_nonneg smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_galerkin_energy_four_dissipation_five_bound_at_background_of_pairing_bound
    (g gBase : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 ρ P T Φ3 Bd4 G : ℝ}
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
            ‖(u.1 : tensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 * ‖galLowView (I := I) (M := M) g 1
            ((u.1 : tensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 * (‖(u.1 : tensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(v.1 : tensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
            ‖galLowView (I := I) (M := M) g 1
              ((u.1 : tensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hG : 0 ≤ G)
    (hpair : ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
        (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ lowRegularityStateRadius Ctop B1 ρ P →
      2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le hδ
            (lowRegularityMetricRealization (I := I) (M := M) g (Ctop := Ctop) (B1 := B1)
              (ρ := ρ) hP.le hreal) F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
        G * ((∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
          (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) *
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
          (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) ^ 2))
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ∀ N : ℕ, ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N) t ∈ lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius Ctop B1 ρ P))
    (hnem : ∀ N : ℕ, ⇑(fseq N) =ᵐ[timeMeasure T]
      fun t => projNfun (I := I) (M := M) g 1 N
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
            (fseq N)) t))
    (hE3 : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ3)
    (hL2H4 : ∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N)
      (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ∂(timeMeasure T) ≤ Bd4) :
    ∃ Φ4 Φ5 : ℝ,
      (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N)
          (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ≤ Φ4) ∧
      (∀ N : ℕ, ∫ t, galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 5 t ∂(timeMeasure T) ≤ Φ5) := by
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
          (0 : tensorHs (I := I) (M := M) g 0 2 (((1 : ℕ) : ℝ) + 2))
          (fseq N)) t) (hball N) (hnem N) t ht
  have hΦ3 : 0 ≤ Φ3 := le_trans
    (galerkinEnergy_nonneg (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g 0) (U 0) 3 0)
    (by simpa only [U] using hE3 0 0 ⟨le_rfl, hT.le⟩)
  let EE4 : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 p.1)
  have hEE4c : ∀ N, Continuous (EE4 N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 (hUcont N)).restrict
  have hEE4nn : ∀ N, ∀ s : ℝ, 0 ≤ EE4 N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEE4eq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE4 N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  let P4 : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE4 N s
  have hP4Has : ∀ N, ∀ t : ℝ, HasDerivAt (P4 N) (EE4 N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEE4c N).intervalIntegrable 0 t)
      (hEE4c N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEE4c N).continuousAt
  have hP40 : ∀ N, P4 N 0 = 0 := fun N => intervalIntegral.integral_same
  have hP4nn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ P4 N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEE4nn N s)
  have hP4cont : ∀ N, ContinuousOn (P4 N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hP4Has N t).continuousAt)).continuousOn
  have hP4deriv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (P4 N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t) (Set.Ici t) t := by
    intro N t ht
    have h := hP4Has N t
    rw [hEE4eq N t ⟨ht.1, ht.2.le⟩] at h
    exact h.hasDerivWithinAt
  have hP4bd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, P4 N t ≤ Bd4 := by
    intro N t ht
    have hTint : ∫ s in (0 : ℝ)..T, EE4 N s = ∫ s,
        galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 s ∂(timeMeasure T) := by
      rw [intervalIntegral.integral_congr
        (g := fun s => galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 s)
        (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEE4eq N s hs),
        intervalIntegral.integral_of_le hT.le, timeMeasure,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hsplit : P4 N t + ∫ s in t..T, EE4 N s = ∫ s in (0 : ℝ)..T, EE4 N s :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hEE4c N).intervalIntegrable 0 t) ((hEE4c N).intervalIntegrable t T)
    have hrest : 0 ≤ ∫ s in t..T, EE4 N s :=
      intervalIntegral.integral_nonneg ht.2 (fun s _ => hEE4nn N s)
    have hfin := hL2H4 N
    rw [← hTint] at hfin
    linarith
  let EE5 : ℕ → ℝ → ℝ := fun N => Set.IccExtend hT.le
    (fun p : Set.Icc (0 : ℝ) T => galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 p.1)
  have hEE5c : ∀ N, Continuous (EE5 N) := by
    intro N
    exact Continuous.Icc_extend'
      (galerkinEnergy_continuousOn (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 (hUcont N)).restrict
  have hEE5nn : ∀ N, ∀ s : ℝ, 0 ≤ EE5 N s := fun N s =>
    galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
  have hEE5eq : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      EE5 N s = galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 s :=
    fun N s hs => Set.IccExtend_of_mem hT.le _ hs
  let D5 : ℕ → ℝ → ℝ := fun N t => ∫ s in (0 : ℝ)..t, EE5 N s
  have hD5Has : ∀ N, ∀ t : ℝ, HasDerivAt (D5 N) (EE5 N t) t := by
    intro N t
    exact intervalIntegral.integral_hasDerivAt_right
      ((hEE5c N).intervalIntegrable 0 t)
      (hEE5c N).aestronglyMeasurable.stronglyMeasurableAtFilter
      (hEE5c N).continuousAt
  have hD50 : ∀ N, D5 N 0 = 0 := fun N => intervalIntegral.integral_same
  have hD5nn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ D5 N t := by
    intro N t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => hEE5nn N s)
  have hD5cont : ∀ N, ContinuousOn (D5 N) (Set.Icc (0 : ℝ) T) := by
    intro N
    exact (continuous_iff_continuousAt.2
      (fun t => (hD5Has N t).continuousAt)).continuousOn
  have hD5deriv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (D5 N)
        (galerkinEnergy (I := I) (M := M)
          (eigenIdxFinset (I := I) (M := M) g N) (U N) (4 + 1) t)
        (Set.Ici t) t := by
    intro N t ht
    have h := hD5Has N t
    rw [hEE5eq N t ⟨ht.1, ht.2.le⟩] at h
    convert h.hasDerivWithinAt using 1
    all_goals norm_num
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  let hrealR := lowRegularityMetricRealization (I := I) (M := M) g
    (Ctop := Ctop) (B1 := B1) (ρ := ρ) hP.le hreal
  obtain ⟨Cseed, hCseed, hseed⟩ := exists_zero_state_deTurck_remainder_spectral_bound (I := I) (M := M) g gBase
    hRpos hδ hrealR hcore
  have hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
          tensorSobolevWeight (I := I) (M := M) i 4 *
            (U N t i * galTameForce (I := I) (M := M) g 1 hRpos.le
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
              (eigenIdxFinset (I := I) (M := M) g N) (U N t) i) ≤
        1 * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N) (4 + 1) t +
          (G * (1 + Φ3) + 0 * (1 + galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t)) *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t +
          2 * Cseed 4 * Real.sqrt (galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 t) +
          G * Φ3 ^ 2 := by
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
      exact add_comm _ _
    have harm := hpair F (U N t) (by
      simpa only [F] using hstate N t ⟨ht.1, ht.2.le⟩)
    have hstat : ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (seed.coeff i) ^ 2 ≤
          Cseed 4 ^ 2 := by
      have h := hseed 4 F
      simpa only [seed, Nat.cast_ofNat] using h
    have hstatPair := abs_sum_sameScale_le (I := I) (M := M) F (4 : ℝ)
      (U N t) (fun i => seed.coeff i)
    have hsqrtstat : Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (seed.coeff i) ^ 2) ≤ Cseed 4 := by
      have hs := Real.sqrt_le_sqrt hstat
      simpa only [Real.sqrt_sq (hCseed 4)] using hs
    have hstatPair' : 2 * |∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * seed.coeff i)| ≤
        2 * Cseed 4 * Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (U N t i) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtstat
        (Real.sqrt_nonneg (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (U N t i) ^ 2))
      have hpairle := hstatPair.trans hmul
      nlinarith [hpairle]
    have hsum : ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * force i) =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * arm.coeff i)) +
        ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * seed.coeff i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hsplit i hi]
      ring
    have hsigned : 2 * ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * force i) ≤
        2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * arm.coeff i)| +
        2 * |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * seed.coeff i)| := by
      rw [hsum]
      nlinarith [le_abs_self (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
          (U N t i * arm.coeff i)),
        le_abs_self (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
            (U N t i * seed.coeff i))]
    let E3 : ℝ := galerkinEnergy (I := I) (M := M) F (U N) 3 t
    let E4 : ℝ := galerkinEnergy (I := I) (M := M) F (U N) 4 t
    let E5 : ℝ := galerkinEnergy (I := I) (M := M) F (U N) 5 t
    have hE3nn : 0 ≤ E3 := galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
    have hE4nn : 0 ≤ E4 := galerkinEnergy_nonneg (I := I) (M := M) _ _ _ _
    have hE3bd : E3 ≤ Φ3 := by
      simpa only [E3, F, U] using hE3 N t ⟨ht.1, ht.2.le⟩
    have hprod : E3 * E4 ≤ Φ3 * E4 :=
      mul_le_mul_of_nonneg_right hE3bd hE4nn
    have hsq : E3 ^ 2 ≤ Φ3 ^ 2 := pow_le_pow_left₀ hE3nn hE3bd 2
    have hshape : E4 + E3 * E4 + E3 ^ 2 ≤
        (1 + Φ3) * E4 + Φ3 ^ 2 := by
      nlinarith
    dsimp only [F, force] at hsigned ⊢
    dsimp only [arm] at harm hsigned
    dsimp only [seed] at hstatPair' hsigned
    norm_num only [one_mul, zero_mul, add_zero, Nat.cast_ofNat] at harm hstatPair' hsigned ⊢
    calc
      _ ≤ 2 * |∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
            tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
              (U N t i * (galerkinActionVectorBackground (I := I) (M := M) g gBase hRpos.le hδ
                hrealR (eigenIdxFinset (I := I) (M := M) g N)
                (U N t)).coeff i)| +
          2 * |∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
            tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
              (U N t i * (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1
                hρ hP hreal ⟨0, zero_mem_lowerState (I := I) (M := M) g 1
                  hRpos.le⟩).coeff i)| := hsigned
      _ ≤ (E5 + G * (E4 + E3 * E4 + E3 ^ 2)) +
          2 * Cseed 4 * Real.sqrt E4 := add_le_add harm hstatPair'
      _ ≤ E5 + G * ((1 + Φ3) * E4 + Φ3 ^ 2) +
          2 * Cseed 4 * Real.sqrt E4 := by
        gcongr
      _ = _ := by ring
  have hinit : ∀ N, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 0 ≤ 0 := by
    intro N
    have hz : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 4 0 = 0 := by
      unfold galerkinEnergy
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hUinit N i]
      ring
    rw [hz]
  obtain ⟨Bound, hBound⟩ := galRiderDiss (I := I) (M := M) (g := g)
    (r := 0) (s₀ := 2) (U := U) (T := T) (σ := 4)
    (Fseq := fun N t => galTameForce (I := I) (M := M) g 1 hRpos.le
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase hδ hCtop hB1 hρ hP hreal)
      (eigenIdxFinset (I := I) (M := M) g N) (U N t))
    (sseq := fun N => eigenIdxFinset (I := I) (M := M) g N)
    (Cδ := 1) (Cmid := G * (1 + Φ3)) (seed := 2 * Cseed 4) (B0 := 0)
    (c₀ := G * Φ3 ^ 2) (Crid := 0) (B := Bd4) (P := P4) (D := D5)
    (by norm_num) (mul_nonneg hG (by linarith))
    (mul_nonneg (by norm_num) (hCseed 4)) (mul_nonneg hG (sq_nonneg Φ3))
    le_rfl hP40 hP4nn hP4cont hP4deriv hP4bd hD50 hD5nn hD5cont hD5deriv
    hUcont hUderiv hclosure hinit
  have hD5time : ∀ N, D5 N T = ∫ t, galerkinEnergy (I := I) (M := M)
      (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 t ∂(timeMeasure T) := by
    intro N
    dsimp only [D5]
    rw [intervalIntegral.integral_congr
      (g := fun s => galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N) (U N) 5 s)
      (by rw [Set.uIcc_of_le hT.le]; exact fun s hs => hEE5eq N s hs),
      intervalIntegral.integral_of_le hT.le, timeMeasure,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine ⟨Bound, Bound, ?_, ?_⟩
  · intro N t ht
    exact (hBound N t ht).1
  · intro N
    rw [← hD5time N]
    have h := (hBound N T ⟨hT.le, le_rfl⟩).2
    norm_num at h ⊢
    exact h

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
