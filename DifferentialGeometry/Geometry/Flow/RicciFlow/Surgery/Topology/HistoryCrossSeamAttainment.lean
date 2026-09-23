import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem exists_crossSeam_lRegularizedMin_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (K T : ℝ) (hg : RiemannianMetricComplete (S.base.metric T))
    (τ : ℝ) (hτ : 0 < τ) (hreg : Icc (T - τ) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - τ) T, ∀ z : M,
      normSq0S (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) I 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ (Real.sqrt τ) = y) :
    ∃ α : ℝ → M,
      Continuous α ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (Icc (0 : ℝ) (Real.sqrt τ)) ∧
      α 0 = x ∧ α (Real.sqrt τ) = y ∧
      lRegularizedAction S T α 0 (Real.sqrt τ) =
        lRegularizedCostC1 S T 0 (Real.sqrt τ) x y ∧
      (∀ β : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 β →
        β 0 = x → β (Real.sqrt τ) = y →
        lRegularizedAction S T α 0 (Real.sqrt τ) ≤
          lRegularizedAction S T β 0 (Real.sqrt τ)) := by
  have hsqrt : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
  have hregSq : Icc (T - (Real.sqrt τ) ^ 2) T ⊆ D.regular := by simpa only [hsq] using hreg
  have hRmSq : ∀ q ∈ Icc (T - (Real.sqrt τ) ^ 2) T, ∀ z : M,
      normSq0S (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by simpa only [hsq] using hRm
  obtain ⟨α, hcont, hC1, h0, h1, hcost, hmin, _hreg⟩ :=
    exists_lRegularizedMin_rm (I := I) S hS K T hg 0 (Real.sqrt τ) le_rfl hsqrt
      hregSq hRmSq x y α₀ hα₀ h₀ h₁
  refine ⟨α, hcont, hC1, h0, h1, hcost, ?_⟩
  exact hmin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
