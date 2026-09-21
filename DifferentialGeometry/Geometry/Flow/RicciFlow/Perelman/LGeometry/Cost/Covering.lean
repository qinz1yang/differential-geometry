import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.CompactPoleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [PreconnectedSpace N] {D : RealTimeInterval}

theorem exists_lCost_covering_sub_le_of_compact
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (T : ℝ) (hregular : Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : M, ∀ tau : ℝ, 1 < tau →
      0 ≤ lCost (S.localPullback p hp) T x y tau - lCost S T (p x) (p y) tau ∧
      lCost (S.localPullback p hp) T x y tau - lCost S T (p x) (p y) tau ≤ C := by
  let U := S.localPullback p hp
  have hU : IsSolutionOn U := hS.localPullback p hp
  have hscalarU : ∀ t ≤ T, ∀ y : M, 0 ≤ U.scalar t y := by
    intro t ht y
    rw [SolutionOn.localPullback_scalar]
    exact hscalar t ht (p y)
  obtain ⟨C, hC, hbound⟩ := exists_lCost_basepoint_add_bound_of_compact U hU T hregular hscalarU x
  refine ⟨C, hC, ?_⟩
  intro y tau htau
  have htau0 : 0 < tau := zero_lt_one.trans htau
  constructor
  · by_contra hnot
    have hlt : lCost U T x y tau < lCost S T (p x) (p y) tau := by linarith
    obtain ⟨beta, hbeta, hb0, hbtau, hact⟩ :=
      exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected U T x y tau htau0 _ hlt
    have hpBeta : ContMDiff 𝓘(ℝ, ℝ) I 1 (p ∘ beta) :=
      (hp.contMDiff.of_le (by simp)).comp hbeta
    have hbase := lCost_le_lRegularizedAction_of_scalar_nonneg S (T := T) htau0.le
      (fun s hs z => hscalar _ (sub_le_self T hs.1) z) (p ∘ beta) hpBeta
    change lCost S T (p (beta 0)) (p (beta (Real.sqrt tau))) tau ≤ _ at hbase
    rw [hb0, hbtau, ← lRegularizedAction_localPullback S p hp T hbeta] at hbase
    exact (not_lt_of_ge hbase) hact
  · by_contra hnot
    have hlt : lCost S T (p x) (p y) tau < lCost U T x y tau - C := by linarith
    obtain ⟨alpha, halpha, ha0, hata, hact⟩ :=
      exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T (p x) (p y) tau htau0 _ hlt
    obtain ⟨beta, hbetaEnd, hproject, hbeta, haction, _⟩ :=
      exists_contMDiff_curve_lift_preserving_action S p hp hcover alpha halpha
        (Real.sqrt tau) y hata.symm
    have hupper := lCost_le_lRegularizedAction_of_scalar_nonneg U (T := T) htau0.le
      (fun s hs z => hscalarU _ (sub_le_self T hs.1) z) beta hbeta
    rw [hbetaEnd, haction T 0 (Real.sqrt tau)] at hupper
    have hcompare := hbound (beta 0) y tau htau
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
