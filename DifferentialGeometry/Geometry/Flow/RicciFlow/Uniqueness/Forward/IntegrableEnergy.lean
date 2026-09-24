import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.IntegratedCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Noncompact
import DifferentialGeometry.Analysis.ODE.Gronwall.Integrable

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_unique_of_uniform_bounds_of_integrable_energy
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ico a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ Ico a b,
      Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ Ico a b,
      IntervalIntegrable (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) volume a c)
    (hinitial : g₁ a = g₂ a) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  obtain ⟨K, -, hbound⟩ := forward_uniqueness_energy_sub_le_integral_of_uniform_bounds
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
    Kex χ hχsupport hχone hχrange hχgrad hden hEint
  have hzero : forwardUniqueEnergy (I := I) (M := M) g₁ g₂ a = 0 := by
    simp only [forwardUniqueEnergy, density_eq_zero_of_eq (I := I) g₁ g₂ hinitial, integral_zero]
  intro t ht
  have hEt : forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t = 0 := by
    refine eq_zero_of_nonneg_of_le_mul_integral (K := K) ht.1 (hEint t ht)
      (fun s _ => integral_nonneg fun x => density_nonneg (I := I) g₁ g₂ s x)
      ?_ t ⟨ht.1, le_rfl⟩
    intro s hs
    have hb := hbound s ⟨hs.1, hs.2.trans_lt ht.2⟩
    simpa only [hzero, sub_zero] using hb
  exact metric_eq_of_energy_zero_noncompact (I := I) g₁ g₂
    (dens_continuous (I := I) g₁ g₂ t) (hden t ht) hEt

end DifferentialGeometry.PDE.RicciFlow
