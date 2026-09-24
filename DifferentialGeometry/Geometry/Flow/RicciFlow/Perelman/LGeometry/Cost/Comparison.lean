import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D D' : RealTimeInterval}

theorem lCost_le_mul_of_metric_le_of_scalar_le [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (U : SolutionOn (I := I) (M := M) D')
    (hS : IsSolutionOn S) (hU : IsSolutionOn U)
    {T R tau A : ℝ} (htau : 0 < tau) (hA : 0 ≤ A)
    (hT : Icc (T - tau) T ⊆ D.carrier) (hR : Icc (R - tau) R ⊆ D'.carrier)
    (hscalarS : ∀ s ∈ Icc 0 tau, ∀ y : M, 0 ≤ S.scalar (T - s) y)
    (hmetric : ∀ s ∈ Icc 0 tau, ∀ y : M, ∀ v : TangentSpace I y,
      (S.base.metric (T - s)).inner y v v ≤ A * (U.base.metric (R - s)).inner y v v)
    (hscalar : ∀ s ∈ Icc 0 tau, ∀ y : M, S.scalar (T - s) y ≤ A * U.scalar (R - s) y)
    (p q : M) : lCost S T p q tau ≤ A * lCost U R p q tau := by
  have happrox (B : ℝ) (hB : lCost U R p q tau < B) : lCost S T p q tau ≤ A * B := by
    obtain ⟨alpha, halpha, hstart, hend, hact⟩ :=
      exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected U R p q tau htau B hB
    have hsquare (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt tau)) : s ^ 2 ∈ Icc 0 tau :=
      ⟨sq_nonneg _, (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).mpr hs.2 |>.trans_eq (Real.sq_sqrt htau.le)⟩
    have hleft := lCost_le_lRegularizedAction_of_scalar_nonneg S htau.le hscalarS alpha halpha
    rw [hstart, hend] at hleft
    have haction := lRegularizedAction_le_mul_of_metric_le_of_scalar_le S U hS hU
      (Real.sqrt_nonneg tau)
      (fun s hs => hT ⟨sub_le_sub_left (hsquare s hs).2 T, sub_le_self _ (hsquare s hs).1⟩)
      (fun s hs => hR ⟨sub_le_sub_left (hsquare s hs).2 R, sub_le_self _ (hsquare s hs).1⟩)
      alpha halpha (fun s hs => hmetric (s ^ 2) (hsquare s hs) _ _)
      (fun s hs => hscalar (s ^ 2) (hsquare s hs) _)
    exact hleft.trans (haction.trans (mul_le_mul_of_nonneg_left hact.le hA))
  have hlim : Tendsto (fun B : ℝ => A * B) (𝓝[>] lCost U R p q tau)
      (𝓝 (A * lCost U R p q tau)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    ((show ∀ᶠ B in 𝓝[>] lCost U R p q tau, lCost U R p q tau < B from
      self_mem_nhdsWithin).mono fun B hB => happrox B hB)

end DifferentialGeometry.PDE.RicciFlow.Perelman
