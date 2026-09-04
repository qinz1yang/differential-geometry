import DifferentialGeometry.Analysis.Integration.L2.Fatou
import DifferentialGeometry.Analysis.Spectral.Intrinsic.GalerkinCompactness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Solution.FourthOrderBounds

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
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset fatou_sq_mass galerkinEnergy solFieldMass
    tendsto_eigenIdxFinset_atTop)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem weighted_mode_mass_four_bound_of_uniform_galerkin_energy
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (fseq : ℕ → timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (Φ : ℝ)
    (hconv : ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto
          (fun N => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
          atTop
          (𝓝 (perModeConv
            (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)))
    (hΦ : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 4 t ≤ Φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i 4 *
        (perModeConv
          (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2) ∧
      ∑' i, tensorSobolevWeight (I := I) (M := M) i 4 *
        (perModeConv
          (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) ^ 2 ≤ Φ := by
  intro t ht
  exact fatou_sq_mass
    (eigenIdxFinset (I := I) (M := M) g)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
    (fun i => tensorSobolevWeight (I := I) (M := M) i 4)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i 4)
    (fun N i => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
    (fun i => perModeConv
      (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
    (fun i => hconv i t ht) Φ (fun N => hΦ N t ht)

omit [BoundarylessManifold I M] in
theorem summable_solution_mode_mass_five_of_integrated_galerkin_energy
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 ≤ T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (fseq : ℕ → timeL2
      (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (Φ : ℝ)
    (hconv : ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto
          (fun N => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
          atTop
          (𝓝 (perModeConv
            (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)))
    (hΦ : ∀ N : ℕ, ∫ t,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g N)
        (galerkinSolutionMode (I := I) (M := M) g fseq N) 5 t
        ∂(timeMeasure T) ≤ Φ) :
    Summable (solFieldMass (I := I) (M := M) hT gforce 5) := by
  have hmass := integral_fatou_sq_mass
    (eigenIdxFinset (I := I) (M := M) g)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
    (fun i => tensorSobolevWeight (I := I) (M := M) i 5)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i 5)
    (fun N t i => galerkinSolutionMode (I := I) (M := M) g fseq N t i)
    (fun t i => perModeConv
      (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
    (fun N i => galerkinSolutionMode_continuous (I := I) (M := M) g hT fseq N i)
    hconv Φ (by
      intro N
      simpa only [galerkinEnergy, timeMeasure] using hΦ N)
  refine hmass.1.congr (fun i => ?_)
  unfold solFieldMass solModeCoeff
  rw [norm_perModeConvL2_sq_eq]

theorem exists_uniform_background_lowRegularity_solution_with_weighted_mode_mass_four_and_five
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
                (TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T),
              IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g gBase K
                  hT hT1
                  u gforce (lowRegularityStateRadius K.top K.slope K.outer K.realize) ∧
                (∃ C4 : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
                  Summable (fun i =>
                    tensorSobolevWeight (I := I) (M := M) i 4 *
                      (perModeConv
                        (TensorEigenIdx.lambda (I := I) (M := M) i)
                        (fun s => (timeModeCoeff (I := I) (M := M)
                          gforce i) s) t) ^ 2) ∧
                  ∑' i, tensorSobolevWeight (I := I) (M := M) i 4 *
                    (perModeConv
                      (TensorEigenIdx.lambda (I := I) (M := M) i)
                      (fun s => (timeModeCoeff (I := I) (M := M)
                        gforce i) s) t) ^ 2 ≤ C4) ∧
                Summable (solFieldMass (I := I) (M := M) hT.le gforce 5) := by
  obtain ⟨K, hKunif, T, hT, hT1, hsolve⟩ :=
    exists_uniform_background_lowRegularity_solution_with_galerkin_energy_four_and_dissipation_five_bounds (I := I) (M := M) hDim gBase hΛ
  refine ⟨K, hKunif, T, hT, hT1, ?_⟩
  intro g hEq hjet
  obtain ⟨u, gforce, fseq, _Φ3, Φ4, Φ5, hsolveAt, hconv, _hΦ3, hΦ4, hΦ5⟩ :=
    hsolve g hEq hjet
  refine ⟨u, gforce, hsolveAt, ⟨Φ4, ?_⟩, ?_⟩
  · exact weighted_mode_mass_four_bound_of_uniform_galerkin_energy
      (I := I) (M := M) g gforce fseq Φ4 hconv hΦ4
  · exact summable_solution_mode_mass_five_of_integrated_galerkin_energy
      (I := I) (M := M) g hT.le gforce fseq Φ5 hconv hΦ5

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
