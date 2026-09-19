import DifferentialGeometry.Analysis.Integration.Measure.Family.DominatedIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffContinuity
import DifferentialGeometry.Analysis.Integration.CompactExhaustionCutoff

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

set_option autoImplicit false

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem intervalIntegrable_weighted_forwardUniqueDensity_on_Ioo
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (η : M → ℝ) (hηcont : Continuous η)
    {a b : ℝ} (hab : a ≤ b) {μ : Measure M} {D : ℝ}
    (hμ : ∀ t ∈ Ioo a b, riemannianMeasureFamily g₁ t ≤ μ)
    (hη : Integrable (fun x => η x ^ 2) μ)
    (hden : ∀ t ∈ Ioo a b, ∀ x, forwardUniqueDensity (I := I) g₁ g₂ t x ≤ D)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    IntervalIntegrable
      (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily g₁ t) volume a b := by
  let Kex := manifoldCompactExhaustion (I := I) (M := M)
  let χ : ℕ → M → ℝ := compactExhaustionCutoff (I := I) Kex
  have hχcont (n : ℕ) : Continuous (χ n) :=
    (compactExhaustionCutoff_spec (I := I) Kex n).1.continuous
  have hχbound (n : ℕ) (x : M) : χ n x ^ 2 ≤ 1 := by
    have h := (compactExhaustionCutoff_spec (I := I) Kex n).2.2.2.2
      (show χ n x ∈ range (χ n) from ⟨x, rfl⟩)
    nlinarith [h.1, h.2]
  apply intervalIntegrable_integral_of_dominated_measure_family_on_Ioo hab
    (μ := μ) (g := fun x => D * η x ^ 2) (χ := fun n x => χ n x ^ 2) hμ
  · exact hη.const_mul D
  · intro t ht
    exact (hηcont.pow 2 |>.mul (dens_continuous (I := I) g₁ g₂ t)).aestronglyMeasurable
  · intro t ht
    filter_upwards [] with x
    rw [Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x))]
    exact (mul_le_mul_of_nonneg_left (hden t ht x) (sq_nonneg _)).trans_eq (mul_comm _ _)
  · intro t ht n
    exact ((hχcont n).pow 2).aestronglyMeasurable
  · intro t ht n
    filter_upwards [] with x
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hχbound n x
  · intro t ht
    filter_upwards [] with x
    have hone : ∀ᶠ n in atTop, χ n x = 1 :=
      compactExhaustionCutoff_eventually_one_on_compact (I := I) Kex
        {x} isCompact_singleton |>.mono (fun n hn => hn x (mem_singleton x))
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hone] with n hn
    simp only [hn, one_pow]
  · intro n
    have hsupp : HasCompactSupport (fun x => η x * χ n x) :=
      (compactExhaustionCutoff_spec (I := I) Kex n).2.1.mul_left
    have hc := forward_uniqueness_cutoff_energy_continuousOn (I := I)
      g₁ g₂ (fun x => η x * χ n x) (hηcont.mul (hχcont n)) hsupp hjoint₁ hjoint₂
    convert hc using 1
    ext t
    congr 1
    funext x
    simp only [smul_eq_mul]
    ring

end DifferentialGeometry.PDE.RicciFlow
