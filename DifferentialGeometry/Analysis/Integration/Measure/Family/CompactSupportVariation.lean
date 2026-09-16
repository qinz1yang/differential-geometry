import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Analysis.Integration.Integral.CompactSupportDerivative

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem hasDerivAt_integral_riemannianMeasureFamily_of_compact_support
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : IsOpen J)
    (hg : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => f p.1 p.2) (J ×ˢ (univ : Set M)))
    {K : Set M} (hK : IsCompact K)
    (hzero : ∀ s ∈ J, ∀ x ∉ K, f s x = 0)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => ∫ x, f s x ∂riemannianMeasureFamily g s)
      (∫ x, deriv (fun s => f s x) t +
        (1 / 2) * traceTimeDerivMetric (I := I) g t x * f t x
        ∂riemannianMeasureFamily g t) t := by
  let : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (g t)
  let F : ℝ → M → ℝ := fun s x => riemannianVolumeDensity (g t) (g s) x * f s x
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => F p.1 p.2) (J ×ˢ (univ : Set M)) :=
    ((riemannianVolumeDensity_family_contMDiffOn (g t) g hJ hg).of_le (by simp)).mul hf
  have hslice {u : ℝ → M → ℝ}
      (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M => u p.1 p.2) (J ×ˢ (univ : Set M)))
      (s : ℝ) (hs : s ∈ J) (x : M) :
      HasDerivAt (fun r => u r x) (deriv (fun r => u r x) s) s := by
    have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M => u p.1 p.2) (s, x) :=
      hu.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hs, mem_univ x⟩)
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun r => u r x) s :=
      hat.comp s (contMDiffAt_id.prodMk contMDiffAt_const)
    exact ((contMDiffAt_iff_contDiffAt.mp hline).differentiableAt (by simp)).hasDerivAt
  have hdF : ContinuousOn (fun p : ℝ × M => deriv (fun s => F s p.2) p.1)
      (J ×ˢ (univ : Set M)) := by
    intro p hp
    have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun q : ℝ × M => F q.1 q.2) p :=
      hF.contMDiffAt ((hJ.prod isOpen_univ).mem_nhds hp)
    have hdAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 0
        (fun q : ℝ × M => deriv (fun s => F s q.2) q.1) p :=
      DifferentialGeometry.timeDeriv_smoothAt hat (by simp)
    exact hdAt.continuousAt.continuousWithinAt
  have hd := DifferentialGeometry.Analysis.hasDerivAt_integral_of_compact_support
    (μ := riemannianVolumeMeasure (I := I) (M := M) (g t)) hJ hK
    (fun s x hs hx => by simp only [F, hzero s hs x hx, mul_zero])
    hF.continuousOn hdF (hslice hF) ht
  have heq (s : ℝ) : (∫ x, f s x ∂riemannianMeasureFamily g s) =
      ∫ x, F s x ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    simpa only [riemannianMeasureFamily_def, smul_eq_mul, F] using
      integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (g t) (g s) (f s)
  have hder (x : M) : deriv (fun s => F s x) t =
      deriv (fun s => f s x) t + (1 / 2) * traceTimeDerivMetric (I := I) g t x * f t x := by
    have hr := hasDerivAt_riemannianVolumeDensity_of_chartGram_contMDiffOn (g t) hJ hg ht x
    have hp := hr.mul (hslice hf t ht x)
    change HasDerivAt (fun s => F s x) _ t at hp
    rw [hp.deriv, riemannianVolumeDensity_self]
    ring
  simpa only [← heq, hder, riemannianMeasureFamily_def] using hd

end DifferentialGeometry.Integral.Measure
