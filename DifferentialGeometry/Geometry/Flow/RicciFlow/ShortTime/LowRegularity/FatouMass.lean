import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FatouIdentification
import DifferentialGeometry.Analysis.Spectral.Intrinsic.GalerkinCompactness

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
  (eigenIdxFinset fatou_sq_mass galerkinEnergy tendsto_eigenIdxFinset_atTop)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem weightedEnergyLimit_bound
    (g₀ : SmoothRiemannianMetric I M) {T σ τ Φ : ℝ}
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (fseq : ℕ → timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hconv : ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) atTop
          (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)))
    (hστ : σ ≤ τ)
    (hΦ : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N)
        (galerkinSolutionMode (I := I) (M := M) g₀ fseq N) τ t ≤ Φ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤ Φ := by
  classical
  intro t ht
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i τ := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hστ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

theorem exists_weighted_energy_bound_up_to_three_of_adapted_solution
    (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap Ctop₂ Kr2 Kr1 Kcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsAdaptedLowRegularitySolution (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap Ctop₂ Kr2 Kr1 Kcap) :
    ∀ σ : ℝ, σ ≤ 3 → ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤
          Cσ := by
  classical
  obtain ⟨fseq, hconv, Φ, hΦ⟩ :=
    exists_fatou_galerkin_approximation_energy_three_bound (I := I) (M := M) g₀ hT hT1 fLo hlo
  intro σ hσ
  refine ⟨Φ, fun t ht => ?_⟩
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i 3 := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hσ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

theorem exists_weighted_energy_bound_up_to_three (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo) :
    ∃ Ctop B1 ρ P Ctop₂ Kr2 Kr1 Cδ : ℝ,
      0 ≤ Ctop₂ ∧ 0 ≤ Kr2 ∧ 0 ≤ Kr1 ∧ 0 ≤ Cδ ∧
      ∀ {ε : ℝ}, 0 < ε →
        Ctop₂ * Cδ + Kr2 * lowRegularityStateRadius Ctop B1 ρ P +
            Kr1 * lowRegularityStateRadius Ctop B1 ρ P + ε < 1 →
        ∀ σ : ℝ, σ ≤ 3 → ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
              (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2) ∧
            ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
                (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
                  (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t) ^ 2 ≤
              Cσ := by
  classical
  obtain ⟨Ctop, B1, ρ, P, fseq, hconv, Ctop₂, Kr2, Kr1, Cδ, h2, hr2, hr1, hcδ,
    hgate⟩ := exists_fatou_galerkin_approximation_energy_three_bound_from_dimension (I := I) (M := M) hDim g₀ hT hT1 fLo hlo
  refine ⟨Ctop, B1, ρ, P, Ctop₂, Kr2, Kr1, Cδ, h2, hr2, hr1, hcδ, ?_⟩
  intro ε hε habs σ hσ
  obtain ⟨Φ, hΦ⟩ := hgate hε habs
  refine ⟨Φ, fun t ht => ?_⟩
  have hdom : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i 3 := fun i =>
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_lambda (I := I) (M := M) i)
      hσ
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i σ *
            (galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i) ^ 2 ≤ Φ := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hdom i) (sq_nonneg _))) ?_
    exact hΦ N t ht
  exact fatou_sq_mass (eigenIdxFinset (I := I) (M := M) g₀)
    (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    (fun i => tensorSobolevWeight (I := I) (M := M) i σ)
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    (fun N i => galerkinSolutionMode (I := I) (M := M) g₀ fseq N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t)
    (fun i => hconv i t ht) Φ hpartial

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
