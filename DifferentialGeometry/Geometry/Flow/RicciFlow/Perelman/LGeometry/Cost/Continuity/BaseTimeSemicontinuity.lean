import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.BaseTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem lCost_le_add_of_metric_antitone_of_scalar_time_lipschitz
    [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b C R T tau : ℝ} (hcarrier : D.carrier = Iic b) (hC : 0 ≤ C)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (Iic b))
    (hscalarTime : ∀ s ≤ b, ∀ t ≤ b, ∀ x : M,
      |S.scalar s x - S.scalar t x| ≤ C * |s - t|)
    (hscalar : ∀ t ≤ b, ∀ z : M, 0 ≤ S.scalar t z)
    (hRT : R ≤ T) (hT : T ≤ b) (htau : 0 < tau) (x y : M) :
    lCost S T x y tau ≤ lCost S R x y tau + 2 * Real.sqrt tau ^ 3 * C * (T - R) := by
  by_contra hnot
  have hlt : lCost S R x y tau <
      lCost S T x y tau - 2 * Real.sqrt tau ^ 3 * C * (T - R) := by linarith
  obtain ⟨alpha, halpha, hstart, hend, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S R x y tau htau _ hlt
  have hcost := lCost_le_lRegularizedAction_of_scalar_nonneg S htau.le
    (fun s hs z => hscalar (T - s) ((sub_le_self _ hs.1).trans hT) z) alpha halpha
  rw [hstart, hend] at hcost
  have haction := lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz
    S hS hcarrier hC hmetric hscalarTime hRT hT (Real.sqrt_nonneg tau) alpha halpha
  linarith

theorem lCost_lowerSemicontinuousWithinAt_of_metric_antitone_of_scalar_time_lipschitz
    [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b C T tau : ℝ} (hcarrier : D.carrier = Iic b) (hC : 0 ≤ C)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (Iic b))
    (hscalarTime : ∀ s ≤ b, ∀ t ≤ b, ∀ x : M,
      |S.scalar s x - S.scalar t x| ≤ C * |s - t|)
    (hscalar : ∀ t ≤ b, ∀ z : M, 0 ≤ S.scalar t z)
    (hT : T ≤ b) (htau : 0 < tau) (x y : M) :
    LowerSemicontinuousWithinAt (fun R => lCost S R x y tau) (Iic T) T := by
  intro A hA
  have hcont : Continuous (fun R : ℝ =>
      lCost S T x y tau - 2 * Real.sqrt tau ^ 3 * C * (T - R)) := by fun_prop
  have hmem : ∀ᶠ R in nhdsWithin T (Iic T),
      A < lCost S T x y tau - 2 * Real.sqrt tau ^ 3 * C * (T - R) :=
    (hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hA))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hmem] with R hR hRA
  have hle := lCost_le_add_of_metric_antitone_of_scalar_time_lipschitz S hS
    hcarrier hC hmetric hscalarTime hscalar hR hT htau x y
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Set
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval}

theorem lCost_upperSemicontinuousWithinAt_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdown : ∀ {a b : ℝ}, b ∈ D.carrier → a ≤ b → a ∈ D.carrier)
    (hscalar : ∀ t ∈ D.carrier, ∀ z : M, 0 ≤ S.scalar t z)
    {T tau : ℝ} (hT : T ∈ D.carrier) (htau : 0 < tau) (x y : M) :
    UpperSemicontinuousWithinAt (fun R => lCost S R x y tau) (Iic T) T := by
  intro A hA
  obtain ⟨alpha, halpha, halpha0, halphab, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T x y tau htau A hA
  have hslab : ∀ s ∈ Set.uIcc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.carrier := by
    intro s _
    exact hdown hT (sub_le_self _ (sq_nonneg s))
  have hevent := (lRegularizedAction_continuousWithinAt_of_carrier S hS hdown
    T 0 (Real.sqrt tau) hslab alpha halpha).eventually (Iio_mem_nhds hact)
  filter_upwards [self_mem_nhdsWithin, hevent] with R hR hRact
  have hscalarR : ∀ s ∈ Icc 0 tau, ∀ z : M, 0 ≤ S.scalar (R - s) z := by
    intro s hs z
    exact hscalar (R - s) (hdown hT ((sub_le_self R hs.1).trans hR)) z
  have hcost : lCost S R x y tau ≤ lRegularizedAction S R alpha 0 (Real.sqrt tau) := by
    rw [← lLength_squareRootReparametrization_eq_lRegularizedAction S R alpha tau htau.le]
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨beta, _, _, _, rfl⟩
      apply intervalIntegral.integral_nonneg htau.le
      intro s hs
      exact mul_nonneg (Real.sqrt_nonneg s) (add_nonneg
        (hscalarR s hs _) (lSpeedSq_nonneg S R _ s))
    · exact ⟨alpha, halpha, halpha0, halphab, rfl⟩
  exact hcost.trans_lt hRact

end DifferentialGeometry.PDE.RicciFlow.Perelman
