import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.SmallPerturbationBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Solution.FatouLimitBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Forcing.GalerkinSequence

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

theorem exists_uniform_background_lowRegularity_solution_with_galerkin_energy_three_bound
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
              (Φ : ℝ),
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
                ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  galerkinEnergy (I := I) (M := M)
                    (eigenIdxFinset (I := I) (M := M) g N)
                    (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ≤ Φ := by
  obtain ⟨delta, R0, hdelta, hdeltathird, hR0, _hR0one, hpair⟩ :=
    galerkin_background_action_sobolev_three_pairing_bound_of_low_view_norm_le (I := I) (M := M) hDim gBase hΛ one_pos
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
  refine ⟨K, hKunif, T, hT, hT1, ?_⟩
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
  obtain ⟨G, hG, hpairG⟩ := hpair g hEq hjet
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
  have hpair' := hpairG hR hKstate K.threshold_lt hreal
  have hpair'' : ∀
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
          G * ((∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) +
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                (c i) ^ 2) ^ 2) := by
    intro F c hc
    simpa only [one_mul, R] using hpair' F c hc
  have hL2H3 : ∀ N : ℕ, ∫ t,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 3 t ∂(timeMeasure T) ≤
      ((1 + T) * (R / 4)) ^ 2 := by
    intro N
    exact galerkin_energy_three_integral_bound (I := I) (M := M) g hT N fseq _
      ((hpack N).2.2.1) ((hpack N).2.2.2.2.2)
  obtain ⟨Φ, hΦ⟩ :=
    exists_uniform_galerkin_energy_three_bound_background_of_pairing_bounds (I := I) (M := M) g gBase hT
      K.threshold_lt hK.threshold_nonneg hK.threshold_le_third
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.hreal hK.core_cont hK.htame hG
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
        exact hpair'' F c hc') fseq
      (fun N => (hpack N).2.1) (fun N => (hpack N).2.2.1) hL2H3
  refine ⟨u, gforce, fseq, Φ, hsolveAt, ?_, hΦ⟩
  intro i t ht
  simpa only [galerkinSolutionMode] using hmode i t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
