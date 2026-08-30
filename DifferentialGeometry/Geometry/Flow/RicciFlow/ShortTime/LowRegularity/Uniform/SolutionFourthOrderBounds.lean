import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.GalerkinSobolevThreeFourPairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.SmallPerturbationBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.FourthOrderDissipationLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.GalerkinForcingSequence

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset finiteEigenComboHs galerkinEnergy smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_background_lowRegularity_solution_with_galerkin_energy_four_bound_and_parameter_caps
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ δcap Rcap : ℝ} (hΛ : 1 ≤ Λ)
    (hδcap : 0 < δcap) (hRcap : 0 < Rcap) :
    ∃ K : LowRegularityBoundParameters,
      HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K ∧
        K.threshold ≤ δcap ∧
        lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ Rcap ∧
        ∃ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
          ∀ (g : SmoothRiemannianMetric I M),
            MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
            (∀ a : ℕ, a ≤ 3 →
              MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
            ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
                ((1 : ℕ) : ℝ) T)
              (gforce : timeL2
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (fseq : ℕ → timeL2
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Φ3 Φ4 Φ5 : ℝ)
              (hK : HasLowRegularityBoundsAt (I := I) (M := M) g gBase K),
              IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g gBase K
                  hT hT1
                  u gforce (lowRegularityStateRadius K.top K.slope K.outer K.realize) ∧
                (∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
                  ∀ t ∈ Set.Icc (0 : ℝ) T,
                    Tendsto
                      (fun N => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
                      atTop
                      (𝓝 (perModeConv
                        (TensorEigenIdx.lambda (I := I) (M := M) i)
                        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t))) ∧
                (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
                  ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
                  HasDerivWithinAt
                    (fun s => galerkinSolutionMode (I := I) (M := M) g fseq N s i)
                    (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
                        galerkinSolutionMode (I := I) (M := M) g fseq N t i +
                      galTameForce (I := I) (M := M) g 1
                        (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                          K.outer_pos K.realize_pos).le
                        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt
                          K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hK.hreal)
                        (eigenIdxFinset (I := I) (M := M) g N)
                        (galerkinSolutionMode (I := I) (M := M) g fseq N t) i)
                    (Set.Ici t) t) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ3) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ≤ Φ4) ∧
                ∀ N : ℕ, ∫ t,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 5 t
                    ∂(timeMeasure T) ≤ Φ5 := by
  obtain ⟨delta, R0, hdelta, hdeltathird, hδcaple, hR0, _hR0one,
      hRcaple, hpairs⟩ :=
    galerkin_background_action_sobolev_three_four_pairing_bounds_of_low_view_norm_le_with_caps (I := I) (M := M)
      hDim gBase hΛ hδcap hRcap
  obtain ⟨K, hKunif, hKdelta, hKstate⟩ :=
    exists_lowBounds_at (I := I) (M := M) hDim gBase hΛ
      hdelta hdeltathird hR0
  subst delta
  let T : ℝ :=
    lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize
  have hT : 0 < T := by
    exact lowRegularityTimeHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
      K.zero_nonneg K.outer_pos K.realize_pos
  have hT1 : T ≤ 1 := lowRegularityTimeHorizon_le_one
  refine ⟨K, hKunif, hδcaple, hKstate.trans hRcaple, T, hT, hT1, ?_⟩
  intro g hEq hjet
  have hK := hKunif.bounds g hEq hjet
  obtain ⟨u, gforce, hsolve⟩ :=
    exists_background_lowRegularity_solution (I := I) (M := M) g gBase K hK hT le_rfl hT1
  let hsolveAt : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g gBase K hT hT1
      u gforce (lowRegularityStateRadius K.top K.slope K.outer K.realize) := {
    bounds := hK
    solve := hsolve
    hTτ := le_rfl
    hcap := le_rfl
  }
  obtain ⟨fseq, _hconv, hmode, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence_with_mode_convergence_background (I := I) (M := M) g gBase K hT hT1
      u gforce hsolveAt
  obtain ⟨G3, G4, hG3, hG4, hpair3G, hpair4G⟩ := hpairs g hEq hjet
  let R : ℝ := lowRegularityStateRadius K.top K.slope K.outer K.realize
  have hR : 0 ≤ R :=
    (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
      K.outer_pos K.realize_pos).le
  let hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) K.threshold :=
    lowRegularityMetricRealization (I := I) (M := M) g K.realize_pos.le hK.hreal
  have hpair3' := hpair3G hR hKstate K.threshold_lt hreal
  have hpair4' := hpair4G hR hKstate K.threshold_lt hreal
  have hpair3'' : ∀
      (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
      2 * |∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
            (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase hR
              K.threshold_lt hreal F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
          G3 * ((∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) ^ 2) := by
    intro F c hc
    simpa only [one_mul, R] using hpair3' F c hc
  have hpair4'' : ∀
      (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
      (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
      ‖galLowView (I := I) (M := M) g 1
          (finiteEigenComboHs (I := I) (M := M) g F c
            (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
      2 * |∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
            (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase hR
              K.threshold_lt hreal F c).coeff i)| ≤
        (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
          G4 * ((∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) *
              (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                  (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) ^ 2) := by
    intro F c hc
    simpa only [one_mul, R] using hpair4' F c hc
  have hL2H3 : ∀ N : ℕ, ∫ t,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ∂(timeMeasure T) ≤
      ((1 + T) * (R / 4)) ^ 2 := by
    intro N
    exact galerkin_energy_three_integral_bound (I := I) (M := M) g hT N fseq _
      ((hpack N).2.2.1) ((hpack N).2.2.2.2.2)
  obtain ⟨Φ3, ΦD4, hΦ3, hΦD4⟩ :=
    exists_uniform_galerkin_energy_three_dissipation_four_bound_background_of_pairing_bounds (I := I) (M := M) g gBase hT
      K.threshold_lt hK.threshold_nonneg hK.threshold_le_third
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.hreal hK.core_cont hK.htame hG3
      (by
        intro F c hc
        have hc' : ‖galLowView (I := I) (M := M) g 1
            (finiteEigenComboHs (I := I) (M := M) g F c
              (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
          exact hc
        have haction :
            galerkinActionVectorBackground (I := I) (M := M) g gBase
                (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                  K.outer_pos K.realize_pos).le K.threshold_lt
                (lowRegularityMetricRealization (I := I) (M := M) g
                  K.realize_pos.le hK.hreal) F c =
              galerkinActionVectorBackground (I := I) (M := M) g gBase hR
                K.threshold_lt hreal F c := by
          rfl
        rw [haction]
        exact hpair3'' F c hc') fseq
      (fun N => (hpack N).2.1) (fun N => (hpack N).2.2.1) hL2H3
  obtain ⟨Φ4, Φ5, hΦ4, hΦ5⟩ :=
    exists_uniform_galerkin_energy_four_dissipation_five_bound_at_background_of_pairing_bound (I := I) (M := M) g gBase hT
      K.threshold_lt hK.threshold_nonneg hK.threshold_le_third
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.hreal hK.core_cont hK.htame hG4
      (by
        intro F c hc
        have hc' : ‖galLowView (I := I) (M := M) g 1
            (finiteEigenComboHs (I := I) (M := M) g F c
              (((1 : ℕ) : ℝ) + 2))‖ ≤ R := by
          exact hc
        have haction :
            galerkinActionVectorBackground (I := I) (M := M) g gBase
                (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                  K.outer_pos K.realize_pos).le K.threshold_lt
                (lowRegularityMetricRealization (I := I) (M := M) g
                  K.realize_pos.le hK.hreal) F c =
              galerkinActionVectorBackground (I := I) (M := M) g gBase hR
                K.threshold_lt hreal F c := by
          rfl
        rw [haction]
        exact hpair4'' F c hc') fseq
      (fun N => (hpack N).2.1) (fun N => (hpack N).2.2.1) hΦ3 hΦD4
  let U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    galerkinSolutionMode (I := I) (M := M) g fseq
  have hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T) :=
    fun N i _ => galerkinSolutionMode_continuous (I := I) (M := M) g hT.le fseq N i
  have hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g N,
      HasDerivWithinAt (fun s => U N s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          galTameForce (I := I) (M := M) g 1 hR
            (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g gBase K.threshold_lt K.top_nonneg
              K.slope_nonneg K.outer_pos K.realize_pos hK.hreal)
            (eigenIdxFinset (I := I) (M := M) g N) (U N t) i)
        (Set.Ici t) t := by
    intro N t ht i _
    refine galerkinSolutionMode_hasDerivWithinAt (I := I) (M := M) g hT hR N fseq i ?_ ?_ ht
    · exact galerkinProjectedForce_mode_continuous (I := I) (M := M) g gBase K.threshold_lt
        K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
        hK.hreal hK.htame N (U N) (fun j _ => hUcont N j (by assumption)) i
    · exact galerkinProjectedForce_mode_eq (I := I) (M := M) g hR hT N fseq
        ((hpack N).2.1) ((hpack N).2.2.1) i
  refine ⟨u, gforce, fseq, Φ3, Φ4, Φ5, hK, hsolveAt, ?_, ?_, hΦ3, hΦ4, hΦ5⟩
  · intro i t ht
    simpa only [galerkinSolutionMode] using hmode i t ht
  · simpa only [U] using hUderiv

theorem exists_uniform_background_lowRegularity_solution_with_galerkin_energy_four_and_dissipation_five_bounds
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : LowRegularityBoundParameters,
      HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K ∧
        ∃ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
          ∀ (g : SmoothRiemannianMetric I M),
            MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
            (∀ a : ℕ, a ≤ 3 →
              MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
            ∃ (u : MaxRegSolutionSpace (I := I) (M := M)
                ((1 : ℕ) : ℝ) T)
              (gforce : timeL2
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (fseq : ℕ → timeL2
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
              (Φ3 Φ4 Φ5 : ℝ),
              IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g gBase K
                  hT hT1
                  u gforce (lowRegularityStateRadius K.top K.slope K.outer K.realize) ∧
                (∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
                  ∀ t ∈ Set.Icc (0 : ℝ) T,
                    Tendsto
                      (fun N => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
                      atTop
                      (𝓝 (perModeConv
                        (TensorEigenIdx.lambda (I := I) (M := M) i)
                        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t))) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ3) ∧
                (∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ≤ Φ4) ∧
                ∀ N : ℕ, ∫ t,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 5 t
                    ∂(timeMeasure T) ≤ Φ5 := by
  obtain ⟨K, hKunif, _hδcap, _hRcap, T, hT, hT1, hsolve⟩ :=
    exists_uniform_background_lowRegularity_solution_with_galerkin_energy_four_bound_and_parameter_caps (I := I) (M := M) hDim gBase hΛ
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  refine ⟨K, hKunif, T, hT, hT1, ?_⟩
  intro g hEq hjet
  obtain ⟨u, gforce, fseq, Φ3, Φ4, Φ5, _hK, hsolveAt, hconv,
      _hderiv, hE3, hE4, hE5⟩ := hsolve g hEq hjet
  exact ⟨u, gforce, fseq, Φ3, Φ4, Φ5, hsolveAt, hconv, hE3, hE4, hE5⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
