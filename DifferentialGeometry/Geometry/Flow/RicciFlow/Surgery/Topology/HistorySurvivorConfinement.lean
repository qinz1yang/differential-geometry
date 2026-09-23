import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Range
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Metric.DistancePullback

noncomputable section

open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor0SBundle

universe u

variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)
  (K : Set (H.event i).incoming.terminalRegularOpen)

private theorem survivor_metric_bound
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S) (C b : ℝ) (hb : 0 ≤ b) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (s : ℝ) (hs : s ∈ Icc 0 b)
    (x : H.backwardSurvivorFootprintInterior first i hle K) (v : TangentSpace ThreeModel x) :
    (S.base.metric (H.time i.succ)).inner x v v ≤
      Real.exp (18 * Real.sqrt C * b ^ 2) *
        (S.base.metric (H.time i.succ - s ^ 2)).inner x v v := by
  have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
  have ht : H.time i.succ - s ^ 2 ∈ Icc c (H.time i.succ) := by
    constructor <;> linarith [sq_nonneg s]
  have hm := (metric_inner_exp_bounds_of_curvature_bound S hS
    (a := c) (b := H.time i.succ) Subset.rfl Subset.rfl x (fun t ht => hRm t ht x)
    (show H.time i.succ ∈ Icc c (H.time i.succ) from ⟨hcs, le_rfl⟩) ht v).2
  have heq : |H.time i.succ - (H.time i.succ - s ^ 2)| = s ^ 2 := by
    rw [sub_sub_cancel, abs_of_nonneg (sq_nonneg s)]
  rw [heq] at hm
  have hm' : (S.base.metric (H.time i.succ)).inner x v v ≤
      Real.exp (18 * Real.sqrt C * s ^ 2) *
        (S.base.metric (H.time i.succ - s ^ 2)).inner x v v := by
    simpa [ThreeSpace, show (2 : ℝ) * 3 ^ 2 = 18 by norm_num] using hm
  exact hm'.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs2
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg C))))
    (DifferentialGeometry.metric_inner_self_nonneg _ _ _))

private theorem survivor_potential_bound
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (C b : ℝ) (hb : 0 ≤ b) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (s : ℝ) (hs : s ∈ Icc 0 b)
    (x : H.backwardSurvivorFootprintInterior first i hle K) :
    -18 * b ^ 2 * Real.sqrt C ≤ 2 * s ^ 2 * S.scalar (H.time i.succ - s ^ 2) x := by
  have hp := lRegularizedPot_lower_rm S C (H.time i.succ) b hb
    (fun t ht x => hRm t ⟨hback.trans ht.1, ht.2⟩ x) s hs x
  change -2 * b ^ 2 * ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt C) ≤ _ at hp
  have hn : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by norm_num [ThreeSpace]
  rw [hn] at hp
  convert hp using 1
  ring

theorem riemannianEDistOf_le_backwardSurvivorFootprint_of_action_le
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    (C b A : ℝ) (hb : 0 ≤ b) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (α : ℝ → H.backwardSurvivorFootprintInterior first i hle K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hact : lRegularizedAction S (H.time i.succ) α 0 b ≤ A) :
    ∀ s ∈ Icc 0 b, riemannianEDistOf (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K (α 0))
      (H.backwardSurvivorFootprintMap first i hle K (α s)) ≤
      ENNReal.ofReal (Real.sqrt b * Real.sqrt
        (2 * Real.exp (18 * Real.sqrt C * b ^ 2) * (A + 18 * b ^ 3 * Real.sqrt C))) := by
  have htime : ∀ s ∈ Icc 0 b,
      H.time i.succ - s ^ 2 ∈ (RealTimeInterval.closed c (H.time i.succ) hcs).carrier := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb).mpr hs.2
    constructor <;> linarith [sq_nonneg s]
  have hd := riemannianEDistOf_le_of_lRegularizedAction_le S hS (S.base.metric (H.time i.succ))
    (H.time i.succ) 0 b A (-18 * b ^ 2 * Real.sqrt C) (Real.exp (18 * Real.sqrt C * b ^ 2))
    hb (Real.exp_pos _).le α hα htime
    (fun s hs v => survivor_metric_bound H first i hle K hcs S hS C b hb hback hRm s hs (α s) v)
    (fun s hs => survivor_potential_bound H first i hle K hcs S C b hb hback hRm s hs (α s)) hact
  intro s hs
  have hpull := DifferentialGeometry.Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (S.base.metric (H.time i.succ)) (H.event i).terminal.metric
    (H.backwardSurvivorFootprintMap first i hle K)
    (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)
    (c := 1) zero_lt_one (fun x v => by rw [hterminal, localPullMetric_inner, one_mul]) (α 0) (α s)
  simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hpull
  refine hpull.trans ((hd s hs).trans_eq ?_)
  rw [sub_zero]
  congr 2
  congr 1
  ring

theorem backwardSurvivorFootprint_action_ge_of_reaches_radius
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    (C b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (α : ℝ → H.backwardSurvivorFootprintInterior first i hle K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hexit : ∃ s ∈ Icc 0 b, ENNReal.ofReal r ≤
      riemannianEDistOf (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K (α 0))
        (H.backwardSurvivorFootprintMap first i hle K (α s))) :
    r ^ 2 / (2 * b * Real.exp (18 * Real.sqrt C * b ^ 2)) -
        18 * b ^ 3 * Real.sqrt C ≤ lRegularizedAction S (H.time i.succ) α 0 b := by
  let A := lRegularizedAction S (H.time i.succ) α 0 b
  let Q := Real.exp (18 * Real.sqrt C * b ^ 2)
  let L := 18 * b ^ 3 * Real.sqrt C
  have hbound := H.riemannianEDistOf_le_backwardSurvivorFootprint_of_action_le first i hle K
    hcs S hS hterminal C b A hb.le hback hRm α hα le_rfl
  obtain ⟨s, hs, hradius⟩ := hexit
  have hrroot : r ≤ Real.sqrt b * Real.sqrt (2 * Q * (A + L)) := by
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg _))).mp
      (hradius.trans (hbound s hs))
  have hQ : 0 < Q := Real.exp_pos _
  have hbudget : 0 ≤ 2 * Q * (A + L) := by
    have hpot := survivor_potential_bound H first i hle K hcs S C b hb.le hback hRm
    have hnonneg : 0 ≤ A + L := by
      have ht : ∀ s ∈ Icc 0 b,
          H.time i.succ - s ^ 2 ∈ (RealTimeInterval.closed c (H.time i.succ) hcs).carrier := by
        intro s hs
        have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
        constructor <;> linarith [sq_nonneg s]
      have hLag : IntervalIntegrable (lRegularizedLagrangian S (H.time i.succ) α) volume 0 b := by
        have hmap : ContinuousOn (fun s : ℝ => (H.time i.succ, s)) (Icc 0 b) :=
          (continuous_const.prodMk continuous_id).continuousOn
        have hmaps : MapsTo (fun s : ℝ => (H.time i.succ, s)) (Icc 0 b)
            {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈
              (RealTimeInterval.closed c (H.time i.succ) hcs).carrier} := ht
        exact ((lRegularizedLagrangian_continuousOn_carrier (I := ThreeModel) S hS α hα).comp
          (f := fun s : ℝ => (H.time i.succ, s)) hmap hmaps).intervalIntegrable_of_Icc hb.le
      have hlow : (-18 * b ^ 2 * Real.sqrt C) * b ≤ A := by
        have hi := intervalIntegral.integral_mono_on hb.le intervalIntegrable_const hLag
          (fun s hs => (hpot s hs (α s)).trans (by
            change 2 * s ^ 2 * S.scalar _ (α s) ≤ (1 / 2 : ℝ) * _ + _
            have hn := DifferentialGeometry.metric_inner_self_nonneg
              (S.base.metric (H.time i.succ - s ^ 2)) (α s) (lVelocity α s)
            linarith))
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, A,
          lRegularizedAction, mul_comm] using hi
      dsimp only [L]
      nlinarith
    exact mul_nonneg (mul_pos (by norm_num) hQ).le hnonneg
  have hsquare := (sq_le_sq₀ hr
    (mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg _))).mpr hrroot
  rw [mul_pow, Real.sq_sqrt hb.le, Real.sq_sqrt hbudget] at hsquare
  have hdiv : r ^ 2 / (2 * b * Q) ≤ A + L := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * b * Q)).mpr
    nlinarith
  exact sub_le_iff_le_add.mpr hdiv

theorem backwardSurvivorFootprint_reducedAction_ge_of_reaches_radius
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    (C b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (α : ℝ → H.backwardSurvivorFootprintInterior first i hle K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hexit : ∃ s ∈ Icc 0 b, ENNReal.ofReal r ≤
      riemannianEDistOf (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K (α 0))
        (H.backwardSurvivorFootprintMap first i hle K (α s))) :
    r ^ 2 / (2 * b * Real.exp (18 * Real.sqrt C * b ^ 2)) - 18 * b ^ 3 * Real.sqrt C ≤
      reducedAction S.base.metric (H.time i.succ) (b ^ 2) (squareRootReparametrization α) := by
  rw [reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ (sq_nonneg b),
    Real.sqrt_sq hb.le]
  exact H.backwardSurvivorFootprint_action_ge_of_reaches_radius first i hle K
    hcs S hS hterminal C b r hb hr hback hRm α hα hexit

theorem backwardSurvivorFootprint_mapsTo_ball_of_reducedAction_lt
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    (C b r : ℝ) (hb : 0 < b) (hr : 0 ≤ r) (hback : c ≤ H.time i.succ - b ^ 2)
    (hRm : ∀ t ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (α : ℝ → H.backwardSurvivorFootprintInterior first i hle K)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hact : reducedAction S.base.metric (H.time i.succ) (b ^ 2) (squareRootReparametrization α) <
      r ^ 2 / (2 * b * Real.exp (18 * Real.sqrt C * b ^ 2)) - 18 * b ^ 3 * Real.sqrt C) :
    MapsTo (H.backwardSurvivorFootprintMap first i hle K ∘ α) (Icc 0 b)
      {x | riemannianEDistOf (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K (α 0)) x < ENNReal.ofReal r} := by
  intro s hs
  by_contra hnot
  have hreach : ENNReal.ofReal r ≤ riemannianEDistOf (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K (α 0))
      (H.backwardSurvivorFootprintMap first i hle K (α s)) := le_of_not_gt hnot
  exact (not_lt_of_ge (H.backwardSurvivorFootprint_reducedAction_ge_of_reaches_radius
    first i hle K hcs S hS hterminal C b r hb hr hback hRm α hα ⟨s, hs, hreach⟩)) hact

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
