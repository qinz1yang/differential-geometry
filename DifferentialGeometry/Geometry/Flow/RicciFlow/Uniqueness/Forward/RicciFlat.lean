import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.NoncompactRicciFlat

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem metric_eq_initial_of_ricci_flat_of_complete_forward_uniqueness
    {a b : ℝ} (hab : a < b)
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen a b hab))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (S.solution.base.metric t) x 4
        (metricRm04At (I := I) (S.solution.base.metric t) x) ≤ C)
    (hunique : ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen a b hab),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a b, ∀ x : M,
        normSq0S (I := I) (S₁.solution.base.metric t) x 4
          (metricRm04At (I := I) (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a b, ∀ x : M,
        normSq0S (I := I) (S₂.solution.base.metric t) x 4
          (metricRm04At (I := I) (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric a = S₂.solution.base.metric a →
      ∀ t ∈ Ico a b, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (hRicci : ∀ (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) (S.solution.base.metric a) x v w = 0) :
    ∀ t ∈ Ico a b, S.solution.base.metric t = S.solution.base.metric a := by
  let g₀ := S.solution.base.metric a
  let g : ℝ → SmoothRiemannianMetric I M := fun _ => g₀
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    exact (Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn
      (I := I) g₀ x₀ i j).comp contMDiffOn_snd (fun p hp => hp.2)
  have hpde : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g t) x v w) (Ici a) t := by
    intro t ht x v w
    simpa only [g, g₀, hRicci, mul_zero] using
      hasDerivWithinAt_const t (Ici a) (g₀.inner x v w)
  have hcomplete : ∀ t ∈ Ico a b, RiemannianMetricComplete (I := I) (g t) := by
    intro t ht
    exact S.complete a ⟨le_rfl, hab⟩
  have hcurv := S.curvatureBound a ⟨le_rfl, hab⟩
  let S₀ := completeBoundedCurvatureSolutionOfJointRicciFlow hab g hjoint hpde hcomplete
    (fun t ht => hcurv)
  have hbound₀ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (S₀.solution.base.metric t) x 4
        (metricRm04At (I := I) (S₀.solution.base.metric t) x) ≤ C := by
    obtain ⟨C, hC, hCb⟩ := hcurv
    exact ⟨C, hC, fun t ht x => hCb x⟩
  exact hunique S S₀ hbound hbound₀ rfl

end DifferentialGeometry.PDE.RicciFlow
