import DifferentialGeometry.Topology.Manifold.CurveCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactChartAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.TimeParameter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology Interval
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [I.Boundaryless] in
private theorem action_interval_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T A B : ℝ) (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hreg : ∀ s ∈ Icc A B, T - s ^ 2 ∈ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ b ∈ Icc A B,
      |lRegularizedAction S T alpha a b| ≤ C * |b - a| := by
  have hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (Icc A B) := by
    have hm : MapsTo (fun s : ℝ => (T, s)) (Icc A B)
        {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.regular} := by
      intro s hs
      exact hreg s hs
    have hc := (lRegularizedLag_time_cont S hS alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn hm
    exact hc
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C : ℝ := max C0 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro a ha b hb
  have hbound : ∀ s ∈ Ι a b, ‖lRegularizedLagrangian S T alpha s‖ ≤ C := by
    intro s hs
    have hs' : s ∈ Icc A B := by
      have hl : A ≤ min a b := le_min ha.1 hb.1
      have hu : max a b ≤ B := max_le ha.2 hb.2
      exact ⟨hl.trans hs.1.le, hs.2.trans hu⟩
    exact (hC0 s hs').trans (le_max_left _ _)
  simpa only [lRegularizedAction, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

private theorem lCost_le_chart_ramp_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T b c : ℝ) (hc : 0 < c) (hcb : c < b)
    (x p : M) (alpha : ℝ → M)
    (halpha : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      alpha (Icc 0 c))
    (hstart : alpha 0 = x)
    (hcsrc : alpha c ∈ (chartAt H p).source)
    (z : E)
    (hreg : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.regular)
    (hbdd : BddBelow {r : ℝ | ∃ gamma : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = (extChartAt I p).symm z ∧
          lRegularizedAction S T gamma 0 b = r})
    (htar : MapsTo
      (lChartRamp (extChartAt I p (alpha c)) z
        (sub_nonneg.mpr hcb.le)).toFun
      (Icc (0 : ℝ) (b - c)) (extChartAt I p).target) :
    lCost S T x ((extChartAt I p).symm z) (b ^ 2) ≤
      lRegularizedAction S T alpha 0 c +
        lChartAction S T c p
          (lChartRamp (extChartAt I p (alpha c)) z
            (sub_nonneg.mpr hcb.le)) := by
  let y₀ : E := extChartAt I p (alpha c)
  let u := lChartRamp y₀ z (sub_nonneg.mpr hcb.le)
  let beta : ℝ → M := fun s =>
    (extChartAt I p).symm (u.toFun (s - c))
  have hu : ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) (b - c)) := by
    have haff : ContDiff ℝ 1
        (fun r : ℝ => y₀ + (r / (b - c)) • (z - y₀)) :=
      contDiff_const.add
        ((contDiff_id.div_const (b - c)).smul contDiff_const)
    apply haff.contDiffOn.congr
    intro r hr
    exact lRamp_apply (y := y₀) (z := z)
      (sub_nonneg.mpr hcb.le) hr
  have hshift : MapsTo (fun s : ℝ => s - c)
      (Icc c b) (Icc (0 : ℝ) (b - c)) := by
    intro s hs
    exact ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 c⟩
  have hcoord : ContDiffOn ℝ 1
      (fun s : ℝ => u.toFun (s - c)) (Icc c b) :=
    hu.comp (contDiff_id.sub contDiff_const).contDiffOn hshift
  have hbeta : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      beta (Icc c b) := by
    change ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      ((extChartAt I p).symm ∘ fun s : ℝ => u.toFun (s - c))
      (Icc c b)
    apply (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp
      hcoord.contMDiffOn
    intro s hs
    exact htar (hshift hs)
  have hbetaStart : beta c = alpha c := by
    change (extChartAt I p).symm (u.toFun (c - c)) = alpha c
    rw [sub_self]
    have hu0 : u.toFun 0 = y₀ :=
      lRamp_start (y := y₀) (z := z) (sub_nonneg.mpr hcb.le)
    rw [hu0]
    change (extChartAt I p).symm (extChartAt I p (alpha c)) = alpha c
    exact (extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hcsrc)
  have hbetaEnd : beta b = (extChartAt I p).symm z := by
    change (extChartAt I p).symm (u.toFun (b - c)) =
      (extChartAt I p).symm z
    have hub : u.toFun (b - c) = z :=
      lRamp_end (y := y₀) (z := z) (sub_pos.mpr hcb)
    rw [hub]
  have hregTail : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, hs.2⟩
  have haction : lRegularizedAction S T beta c b =
      lChartAction S T c p u := by
    exact lRampAct_eq (I := I) S hS T c b p
      (y := y₀) (z := z) hcb htar hregTail
  have hjoin := lCost_le_join_bdd (I := I) S hS T b
    (hc.trans hcb) x ((extChartAt I p).symm z)
    (c := c) hc hcb hbdd hreg alpha beta
    halpha hbeta hbetaStart.symm hstart hbetaEnd
  rw [haction] at hjoin
  exact hjoin

theorem lCost_lt_event_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T b : ℝ) (hb : 0 < b)
    (hreg : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hstart : alpha 0 = x) (hend : alpha b = y)
    (hbdd : ∀ z : M, BddBelow {r : ℝ | ∃ gamma : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = z ∧ lRegularizedAction S T gamma 0 b = r})
    (A : ℝ) (hA : lRegularizedAction S T alpha 0 b < A) :
    ∀ᶠ z in 𝓝 y, lCost S T x z (b ^ 2) < A := by
  subst y
  let p := alpha b
  let e := extChartAt I p
  let w := e p
  obtain ⟨R, hR, d0, hd0, V, hV, hKtar, hcoord⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_endpoint_chart_displacement_bound
      (I := I) alpha b halpha.contMDiffAt
  obtain ⟨Ca, hCa, htail⟩ := action_interval_bound S hS T 0 b alpha halpha hreg
  obtain ⟨Cg, Cs, hCg, hCs, hramp⟩ :=
    lRampAct_slab_of_compact_chart S hS T p hreg (isCompact_closedBall w R) hKtar
  let C : ℝ := Ca + (Cg / 2) * (V + 1) ^ 2 + Cs
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgap : 0 < A - lRegularizedAction S T alpha 0 b := sub_pos.mpr hA
  obtain ⟨d, hd, hdsmall⟩ := exists_between
    (lt_min hb (lt_min hd0 (div_pos hgap (show 0 < C + 1 by linarith))))
  have hdb : d < b := (lt_min_iff.mp hdsmall).1
  have hdd0 : d < d0 := (lt_min_iff.mp (lt_min_iff.mp hdsmall).2).1
  have hdgap : d < (A - lRegularizedAction S T alpha 0 b) / (C + 1) :=
    (lt_min_iff.mp (lt_min_iff.mp hdsmall).2).2
  let c := b - d
  have hc : 0 < c := sub_pos.mpr hdb
  have hcb : c < b := sub_lt_self b hd
  have hlen : b - c = d := by dsimp only [c]; ring
  have hcnear : c ∈ Icc (b - d0) b :=
    ⟨by dsimp only [c]; linarith only [hdd0], hcb.le⟩
  obtain ⟨hcsrc, hcball, hcdisp⟩ := hcoord c hcnear
  have hcK : e (alpha c) ∈ Metric.closedBall w R :=
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith only [hR]) hcball)
  have hcdisp' : ‖e (alpha c) - w‖ ≤ V * d := by
    have habs : |c - b| = d := by rw [abs_of_nonpos (sub_nonpos.mpr hcb.le)]; linarith only [hlen]
    simpa only [habs] using hcdisp
  have hzclose : ∀ᶠ z in 𝓝 p, z ∈ e.source ∧
      ‖e z - w‖ < min d (R / 2) := by
    have hecont : ContinuousAt e p := continuousAt_extChartAt p
    have hball := hecont.preimage_mem_nhds
      (Metric.ball_mem_nhds w (lt_min hd (half_pos hR)))
    filter_upwards [extChartAt_source_mem_nhds (I := I) p, hball] with z hz hzball
    exact ⟨hz, by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hzball⟩
  filter_upwards [hzclose] with z hz
  have hzK : e z ∈ Metric.closedBall w R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hz.2.trans_le (min_le_right _ _)).le.trans (by linarith only [hR])
  have hdist : ‖e z - e (alpha c)‖ ≤ (V + 1) * d := by
    calc
      ‖e z - e (alpha c)‖ ≤ ‖e z - w‖ + ‖w - e (alpha c)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖e z - w‖ + ‖e (alpha c) - w‖ := by rw [norm_sub_rev w]
      _ ≤ d + V * d := add_le_add (hz.2.trans_le (min_le_left _ _)).le hcdisp'
      _ = (V + 1) * d := by ring
  have hsquare : ‖e z - e (alpha c)‖ ^ 2 / (b - c) ≤ (V + 1) ^ 2 * d := by
    rw [hlen]
    calc
      ‖e z - e (alpha c)‖ ^ 2 / d ≤ ((V + 1) * d) ^ 2 / d :=
        div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hdist) hd.le
      _ = (V + 1) ^ 2 * d := by field_simp
  have hrange := lRamp_mapsTo (convex_closedBall w R)
    (sub_nonneg.mpr hcb.le) hcK hzK
  have hclock : ∀ r ∈ Icc 0 (b - c), c + r ∈ Icc 0 b := by
    intro r hr
    constructor <;> linarith only [hc, hr.1, hr.2]
  have hrampsmall : lChartAction S T c p
      (lChartRamp (e (alpha c)) (e z) (sub_nonneg.mpr hcb.le)) ≤
      ((Cg / 2) * (V + 1) ^ 2 + Cs) * d := by
    have h := hramp (sub_pos.mpr hcb) hclock hrange
    calc
      _ ≤ (Cg / 2) * (‖e z - e (alpha c)‖ ^ 2 / (b - c)) + Cs * (b - c) := h
      _ ≤ (Cg / 2) * ((V + 1) ^ 2 * d) + Cs * d := by
        rw [hlen]
        have hmul : (Cg / 2) * (‖e z - e (alpha c)‖ ^ 2 / d) ≤
            (Cg / 2) * ((V + 1) ^ 2 * d) :=
          mul_le_mul_of_nonneg_left (by simpa only [hlen] using hsquare) (by positivity)
        exact add_le_add hmul le_rfl
      _ = _ := by ring
  have hjoin := lCost_le_chart_ramp_bdd S hS T b c hc hcb x p alpha
    halpha.contMDiffOn hstart (by simpa only [extChartAt_source] using hcsrc)
    (e z) hreg (hbdd ((extChartAt I p).symm (e z)))
    (fun r hr => interior_subset (hKtar (hrange hr)))
  have heinv : (extChartAt I p).symm (e z) = z := e.left_inv hz.1
  rw [heinv] at hjoin
  have htailbound := htail c ⟨hc.le, hcb.le⟩ b ⟨hb.le, le_rfl⟩
  rw [hlen, abs_of_pos hd] at htailbound
  have hheadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 c hc.le
    alpha halpha.contMDiffOn (fun s hs => hreg s ⟨hs.1, hs.2.trans hcb.le⟩)
  have htailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩ T c b hcb.le
    alpha halpha.contMDiffOn (fun s hs => hreg s ⟨hc.le.trans hs.1, hs.2⟩)
  have hadd := lRegularizedAction_add S T alpha 0 c b hheadInt htailInt
  have hhead : lRegularizedAction S T alpha 0 c ≤ lRegularizedAction S T alpha 0 b + Ca * d := by
    have hneg := neg_le_abs (lRegularizedAction S T alpha c b)
    linarith only [hadd, htailbound, hneg]
  have hsmall : C * d < A - lRegularizedAction S T alpha 0 b := by
    have h := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hdgap
    nlinarith only [h, hd]
  calc
    lCost S T x z (b ^ 2) ≤ lRegularizedAction S T alpha 0 c +
        lChartAction S T c p (lChartRamp (e (alpha c)) (e z) (sub_nonneg.mpr hcb.le)) := hjoin
    _ ≤ (lRegularizedAction S T alpha 0 b + Ca * d) +
        ((Cg / 2) * (V + 1) ^ 2 + Cs) * d := add_le_add hhead hrampsmall
    _ = lRegularizedAction S T alpha 0 b + C * d := by dsimp only [C]; ring
    _ < A := by linarith only [hsmall]

theorem lCost_lt_event_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (K T tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (x y : M) (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (A : ℝ) (hA : lRegularizedAction S T alpha 0 (Real.sqrt tau) < A) :
    ∀ᶠ z in 𝓝 y, lCost S T x z tau < A := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hclock : ∀ s ∈ Icc 0 b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
        _ = tau := hb2
    constructor <;> linarith only [hs2, sq_nonneg s]
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hreg
  have hRmSq : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K := by
    simpa only [hb2] using hRm
  have h := lCost_lt_event_of_bdd S hS T b hb hclock x y alpha halpha hstart hend
    (fun z => lRegularizedCosts_bdd_rm S hS K T 0 b (by norm_num) hb.le hregSq hRmSq x z) A hA
  simpa only [hb2] using h

end DifferentialGeometry.PDE.RicciFlow
