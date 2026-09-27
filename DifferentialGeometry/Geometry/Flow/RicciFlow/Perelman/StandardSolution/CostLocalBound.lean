import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.NoAdmissibleCurve
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lCost_locally_bddAbove_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K)
    (x y : M) :
    ∃ A : ℝ, ∀ᶠ q in 𝓝 y, lCost S T x q tau < A := by
  classical
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hreg
  have hclock : ∀ s ∈ Icc (0 : ℝ) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hregSq
    have hs2 : s ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  by_cases hreach : ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = y
  · obtain ⟨alpha, halpha, hstart, hend⟩ := hreach
    refine ⟨lRegularizedAction S T alpha 0 b + 1, ?_⟩
    exact lCost_lt_event_of_rm (I := I) S hS K T tau htau
      hreg hRm x y alpha halpha hstart hend
      (lRegularizedAction S T alpha 0 b + 1)
      (lt_add_one (lRegularizedAction S T alpha 0 b))
  · have hnoChart : ¬ ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧
          alpha b = (extChartAt I y).symm (extChartAt I y y) := by
      simpa only [(extChartAt I y).left_inv
        (mem_extChartAt_source (I := I) y)] using hreach
    obtain ⟨ε, hε, hnoBall⟩ :=
      lNoCurve_nhds (I := I) S hS T x b hb hclock y
        (q0 := extChartAt I y y)
        (mem_extChartAt_target (I := I) y) hnoChart
    have hball : ∀ᶠ q in 𝓝 y,
        extChartAt I y q ∈ Metric.ball (extChartAt I y y) ε :=
      (continuousAt_extChartAt (I := I) y).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hε)
    refine ⟨1, ?_⟩
    filter_upwards [extChartAt_source_mem_nhds (I := I) y, hball]
      with q hqsource hqball
    have hnoq : ¬ ∃ alpha : ℝ → M,
        ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
          alpha 0 = x ∧ alpha b = q := by
      simpa only [(extChartAt I y).left_inv hqsource] using
        hnoBall (extChartAt I y q) hqball
    have hzero : lCost S T x q tau = 0 := by
      simpa only [hb2] using
        lCost_zero_no_curve (I := I) S T x q b hb hnoq
    rw [hzero]
    norm_num

theorem lCost_bddAbove_on_compact_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K)
    (x : M) {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y ∈ Cpt, lCost S T x y tau ≤ A := by
  classical
  have hlocal (y : M) : ∃ U : Set M,
      IsOpen U ∧ y ∈ U ∧
        ∃ B : ℝ, ∀ q ∈ U, lCost S T x q tau < B := by
    obtain ⟨B, hB⟩ :=
      lCost_locally_bddAbove_of_rm (I := I) S hS K T tau htau
        hreg hRm x y
    obtain ⟨U, hUsub, hUopen, hyU⟩ := mem_nhds_iff.mp hB
    exact ⟨U, hUopen, hyU, B, fun q hq => hUsub hq⟩
  choose U hUopen hUself B hUbound using hlocal
  obtain ⟨s, hcover⟩ := hCpt.elim_finite_subcover U hUopen
    (fun y _hy => mem_iUnion.mpr ⟨y, hUself y⟩)
  refine ⟨∑ a ∈ s, max 0 (B a), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun a _ha => le_max_left 0 (B a))
  · intro y hy
    rcases mem_iUnion.mp (hcover hy) with ⟨a, ha⟩
    rcases mem_iUnion.mp ha with ⟨has, hya⟩
    calc
      lCost S T x y tau ≤ B a := (hUbound a y hya).le
      _ ≤ max 0 (B a) := le_max_right _ _
      _ ≤ ∑ a ∈ s, max 0 (B a) :=
        Finset.single_le_sum (fun a _ha => le_max_left 0 (B a)) has

end DifferentialGeometry.PDE.RicciFlow

end
