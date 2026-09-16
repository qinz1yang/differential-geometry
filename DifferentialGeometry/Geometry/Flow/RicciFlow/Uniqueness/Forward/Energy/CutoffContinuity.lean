import DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Measure.DensityRegularity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle _root_.Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

theorem forward_uniqueness_cutoff_energy_continuousOn
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {J : Set ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) J := by
  have hf : ContinuousOn
      (fun p : ℝ × M => χ p.2 ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (J ×ˢ (univ : Set M)) :=
    ((hχ.comp continuous_snd).pow 2).continuousOn.mul
      (dens_jointContMDiffOn (I := I) g₁ g₂ hjoint₁ hjoint₂).continuousOn
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support g₁
    (fun α i j => (hjoint₁ α i j).continuousOn)
    (fun t x => χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) hf hcχ
    (fun _ _ x hx => by simp [image_eq_zero_of_notMem_tsupport hx])

theorem forward_uniqueness_cutoff_energy_continuousWithinAt_initial
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {a b : ℝ} (hab : a < b)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousWithinAt (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) (Ico a b) a :=
  forward_uniqueness_cutoff_energy_continuousOn g₁ g₂ χ hχ hcχ hjoint₁ hjoint₂ a ⟨le_rfl, hab⟩

theorem forward_uniqueness_cutoff_energy_tendsto_zero_initial
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {a b : ℝ} (hab : a < b)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (heq : g₁ a = g₂ a) :
    Tendsto (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) (𝓝[Ico a b] a) (𝓝 0) := by
  have hc := forward_uniqueness_cutoff_energy_continuousWithinAt_initial
    g₁ g₂ χ hχ hcχ hab hjoint₁ hjoint₂
  simpa only [ContinuousWithinAt, density_eq_zero_of_eq (I := I) g₁ g₂ heq,
    mul_zero, integral_zero] using hc

end DifferentialGeometry.PDE.RicciFlow
