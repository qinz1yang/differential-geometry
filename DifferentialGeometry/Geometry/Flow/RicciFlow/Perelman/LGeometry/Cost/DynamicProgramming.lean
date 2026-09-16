import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set MeasureTheory
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (K T : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hcarrier : Icc (T - b ^ 2) T ⊆ D.carrier)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (p : M) (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost S T p (alpha b) (b ^ 2) ≤
      lCost S T p (alpha a) (a ^ 2) + lRegularizedAction S T alpha a b := by
  have hb : 0 < b := ha.trans hab
  by_contra hnot
  have hlt : lCost S T p (alpha a) (a ^ 2) <
      lCost S T p (alpha b) (b ^ 2) - lRegularizedAction S T alpha a b := by
    linarith
  obtain ⟨beta, hbeta, hbeta0, hbetaa, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T p (alpha a)
      (a ^ 2) (sq_pos_of_pos ha) _ hlt
  rw [Real.sqrt_sq ha.le] at hbetaa hact
  have hclock : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    apply hcarrier
    exact ⟨sub_le_sub_left ((sq_le_sq₀ hs.1 hb.le).mpr hs.2) T,
      sub_le_self T (sq_nonneg s)⟩
  have hjoin := lCost_le_join_on_carrier_of_bounded_rm S hS T b ha hab
    beta alpha hbeta.contMDiffOn halpha.contMDiffOn hbetaa hclock ⟨K, hRm⟩
  rw [hbeta0] at hjoin
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
