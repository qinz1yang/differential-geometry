import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MetricFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.SmoothAttainment

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]

theorem reducedAction_eq_lLength {D : RealTimeInterval}
    (S : SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) D) (T τ : ℝ) (γ : ℝ → M) :
    reducedAction S.base.metric T τ γ = lLength S T γ 0 τ := by
  unfold reducedAction lLength lDensity lSpeedSq lVelocity
  congr 1
  funext s
  change Real.sqrt s * (_ + Real.sqrt _ ^ 2) = _
  rw [Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg _ _ _)]
  rfl

def isRegularizedAdmissible (γ : ℝ → M) : Prop :=
  ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 1 α ∧ squareRootReparametrization α = γ

theorem reducedLength_eq_lCost {D : RealTimeInterval}
    (S : SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) D) (T τ : ℝ) (x y : M) :
    reducedLength S.base.metric T isRegularizedAdmissible x τ y = lCost S T x y τ := by
  unfold reducedLength lCost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨γ,⟨α,hα,rfl⟩,h0,h1,hr⟩
    refine ⟨α,hα,?_,h1,?_⟩
    · simpa only [squareRootReparametrization,Real.sqrt_zero] using h0
    · rwa [reducedAction_eq_lLength] at hr
  · rintro ⟨α,hα,h0,h1,hr⟩
    refine ⟨squareRootReparametrization α,⟨α,hα,rfl⟩,?_,h1,?_⟩
    · simpa only [squareRootReparametrization,Real.sqrt_zero] using h0
    · rwa [reducedAction_eq_lLength]

variable [T2Space M] [CompactSpace M]

theorem exists_reducedAction_minimizer_of_regular_interval {D : RealTimeInterval}
    (S : SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) D) (hS : IsSolutionOn S)
    (T τ : ℝ) (hτ : 0 < τ) (hreg : Icc (T - τ) T ⊆ D.regular)
    (x y : M) (α₀ : ℝ → M) (hα₀ : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ (Real.sqrt τ) = y) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ α ∧ α 0 = x ∧ α (Real.sqrt τ) = y ∧
      isRegularizedAdmissible (squareRootReparametrization α) ∧
      reducedAction S.base.metric T τ (squareRootReparametrization α) =
        reducedLength S.base.metric T isRegularizedAdmissible x τ y := by
  obtain ⟨α,hα,h0,h1,hmin⟩ := exists_contMDiff_lCost_minimizer S hS T τ hτ hreg x y α₀ hα₀ h₀ h₁
  refine ⟨α,hα,h0,h1,⟨α,hα.of_le (by simp),rfl⟩,?_⟩
  rw [reducedAction_eq_lLength,reducedLength_eq_lCost]
  exact hmin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
