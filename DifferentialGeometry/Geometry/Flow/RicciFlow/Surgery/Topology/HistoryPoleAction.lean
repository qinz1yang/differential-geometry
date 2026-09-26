import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators Interval
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem stage_scalar_continuousOn
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (x : (H.stage j).Carrier) :
    ContinuousOn (fun s => metricScalarAt (H.stageMetric j s) x) (H.stageDomain j) := by
  cases j using Fin.lastCases with
  | cast i =>
    have hh := (H.event i).incoming.equation.scalarCont.comp
      (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, mem_univ x⟩)
    change ContinuousOn (fun s => (H.event i).incoming.flow.scalar s x)
      (RealTimeInterval.closedOpen (H.time i.castSucc) (H.time i.succ) (H.event i).incoming.lt).carrier at hh
    simpa only [ObservedHistory.stageMetric_castSucc_apply, ObservedHistory.stageDomain,
      Fin.lastCases_castSucc, SolutionOn.scalar, SolutionFamily.scalar, RealTimeInterval.closedOpen] using hh
  | last =>
    by_cases h : H.time (Fin.last H.eventCount) < H.horizon
    · have hh := (H.finalSlab h).equation.scalarCont.comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, mem_univ x⟩)
      change ContinuousOn (fun s => (H.finalSlab h).flow.scalar s x)
        (RealTimeInterval.closed (H.time (Fin.last H.eventCount)) H.horizon h.le).carrier at hh
      simpa only [ObservedHistory.stageMetric_last_of_lt (h := h), ObservedHistory.stageDomain,
        Fin.lastCases_last, SolutionOn.scalar, SolutionFamily.scalar, RealTimeInterval.closed] using hh
    · simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dif_neg h]
      exact continuousOn_const

private theorem stage_const_lagrangian_eq
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (T : ℝ) (x : (H.stage j).Carrier) (s : ℝ) :
    H.stageRegularizedLagrangian j T (fun _ => x) s = 2 * s ^ 2 * metricScalarAt (H.stageMetric j (T-s^2)) x := by
  have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => x) s = 0 := by
    simp only [lVelocity, mfderiv_const]
    rfl
  simp only [ObservedHistory.stageRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]

private theorem trace_norm_transport {H : ObservedHistory.{u}}
    {first last j k : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {p : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle p)
    (hjk : j = k) (hj : first ≤ j) (hjl : j ≤ last)
    (hk : first ≤ k) (hkl : k ≤ last) (s : ℝ) :
    normSq0S (H.stageMetric j s) (A.point j hj hjl) 4
      (metricRm04At (H.stageMetric j s) (A.point j hj hjl)) =
    normSq0S (H.stageMetric k s) (A.point k hk hkl) 4
      (metricRm04At (H.stageMetric k s) (A.point k hk hkl)) := by
  subst k
  rfl

private theorem trace_scalar_abs_le
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {r : ℝ} (hr : 0 < r) (hA : A.isRmControlled (hat := hat) r)
    (j : H.StageInterval (H.activeStage a) (H.activeStage t)) (s : ℝ)
    (hs : s ∈ H.stageDomain j.val) (has : (a : ℝ) ≤ s) (hst : s ≤ t) :
    |metricScalarAt (H.stageMetric j.val s) (A.point j.val j.property.1 j.property.2)| ≤ 9 / r ^ 2 := by
  let v : Icc (0 : ℝ) H.horizon := ⟨s, H.stageDomain_subset j.val hs⟩
  have hj : H.activeStage v = j.val := (H.mem_stageDomain_iff v j.val).mp hs
  have hb := hA.1 v has hst
  have heq : normSq0S (H.stageMetric (H.activeStage v) s)
      (A.point (H.activeStage v) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
        (metricRm04At (H.stageMetric (H.activeStage v) s)
          (A.point (H.activeStage v) (H.activeStage_mono has) (H.activeStage_mono hst))) =
      normSq0S (H.stageMetric j.val s) (A.point j.val j.property.1 j.property.2) 4
        (metricRm04At (H.stageMetric j.val s) (A.point j.val j.property.1 j.property.2)) := by
    exact trace_norm_transport A hj _ _ _ _ s
  change r ^ 4 * normSq0S (H.stageMetric (H.activeStage v) s)
      (A.point (H.activeStage v) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
        (metricRm04At (H.stageMetric (H.activeStage v) s)
          (A.point (H.activeStage v) (H.activeStage_mono has) (H.activeStage_mono hst))) ≤ 1 at hb
  rw [heq] at hb
  simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat,
    show (3 : ℝ)^2=9 by norm_num] using
    scalar_abs_le_div_sq_of_rm_bound (H.stageMetric j.val s) (A.point j.val j.property.1 j.property.2) hr.ne' hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem trace_constant_action_integrable_bound
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) (hclock : (t : ℝ) - v ^ 2 = a)
    (hA : A.isRmControlled (hat := hat) r)
    (j : H.StageInterval (H.activeStage a) (H.activeStage t)) :
    IntervalIntegrable (H.stageRegularizedLagrangian j.val t
      (fun _ => A.point j.val j.property.1 j.property.2)) volume
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) ∧
    H.stageRegularizedAction j.val t (fun _ => A.point j.val j.property.1 j.property.2)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) ≤
        (6 / r ^ 2) * ((H.regularizedStageEnd t v j.val)^3 -
          (H.regularizedStageStart t 0 j.val)^3) := by
  let l := H.regularizedStageStart t 0 j.val
  let b := H.regularizedStageEnd t v j.val
  let z := A.point j.val j.property.1 j.property.2
  let f := H.stageRegularizedLagrangian j.val t (fun _ => z)
  have hup : (t : ℝ) - (0 : ℝ)^2 ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
    simpa only [zero_pow two_ne_zero,sub_zero] using
      (show (t : ℝ) ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) from
        ⟨H.activeStage_time_le t,H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩)
  have hlo : (t : ℝ) - v ^ 2 ∈ H.stageDomain (H.activeStage a) := by rw [hclock]; exact H.activeStage_mem a
  have hbds := H.regularizedStage_bounds le_rfl hv hup hlo j
  have hl0 : 0 ≤ l := hbds.1
  have hlb : l ≤ b := hbds.2.1
  have hbv : b ≤ v := hbds.2.2
  have hscalar : ∀ s ∈ Ioo l b, |metricScalarAt (H.stageMetric j.val ((t : ℝ)-s^2)) z| ≤ 9/r^2 := by
    intro s hs
    have hs0 : 0 ≤ s := hl0.trans hs.1.le
    have hsv : s ≤ v := hs.2.le.trans hbv
    have hs2 : s^2 ≤ v^2 := (sq_le_sq₀ hs0 hv).mpr hsv
    exact trace_scalar_abs_le A hr hA j ((t : ℝ)-s^2)
      (H.mapsTo_regularizedStage_Ioo t 0 v j.val hs) (by linarith [hclock])
      (sub_le_self _ (sq_nonneg s))
  have hcont : ContinuousOn f (Ioo l b) := by
    have hc := (stage_scalar_continuousOn H j.val z).comp
      (continuous_const.sub (continuous_id.pow 2)).continuousOn
      (H.mapsTo_regularizedStage_Ioo t 0 v j.val)
    have hp := ((continuousOn_const (c := (2 : ℝ))).mul (continuousOn_id.pow 2)).mul hc
    exact hp.congr (fun s _ => stage_const_lagrangian_eq H j.val t z s)
  have hpoly : IntervalIntegrable (fun s : ℝ => (18/r^2)*s^2) volume l b :=
    (by fun_prop : Continuous (fun s : ℝ => (18/r^2)*s^2)).intervalIntegrable _ _
  have hbound : ∀ s ∈ Ioo l b, ‖f s‖ ≤ (18/r^2)*s^2 := by
    intro s hs
    rw [Real.norm_eq_abs,show f s = _ from stage_const_lagrangian_eq H j.val t z s,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 2*s^2)]
    calc
      _ ≤ 2*s^2*(9/r^2) := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity)
      _ = _ := by ring
  have hfint : IntervalIntegrable f volume l b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hlb]
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlb).mp hpoly).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioo)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hbound s hs)
  refine ⟨hfint,?_⟩
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hlb hfint hpoly
    (fun s hs => (le_abs_self (f s)).trans (by simpa only [Real.norm_eq_abs] using hbound s hs))
  have hpolyval : (∫ s in l..b, (18/r^2)*s^2) = (6/r^2)*(b^3-l^3) := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    norm_num
    ring
  change (∫ s in l..b, f s) ≤ (6/r^2)*(b^3-l^3)
  rwa [hpolyval] at hle


theorem BackwardPointTrace.exists_regularizedC1ActionValues_le_of_isRmControlled
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) (hclock : (t : ℝ) - v ^ 2 = a)
    (hA : A.isRmControlled (hat := hat) r) :
    ∃ action : ℝ,
      action ∈ H.regularizedC1ActionValues (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) t 0 v p
        (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) ∧
      action ≤ 6 * v ^ 3 / r ^ 2 := by
  let α := fun j : H.StageInterval (H.activeStage a) (H.activeStage t) =>
    fun _ : ℝ => A.point j.val j.property.1 j.property.2
  let action := ∑ j : H.StageInterval (H.activeStage a) (H.activeStage t),
    H.stageRegularizedAction j.val t (α j)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)
  have hup : (t : ℝ) - (0 : ℝ)^2 ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) := by
    simpa only [zero_pow two_ne_zero,sub_zero] using
      (show (t : ℝ) ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) from
        ⟨H.activeStage_time_le t,H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩)
  have hlo : (t : ℝ) - v ^ 2 ∈ H.stageDomain (H.activeStage a) := by rw [hclock]; exact H.activeStage_mem a
  refine ⟨action, ⟨le_rfl,hv,hup,hlo,α,fun _ => contMDiff_const,
    fun j => (trace_constant_action_integrable_bound A hr hv hclock hA j).1,
    A.endpoint_eq,rfl,?_,rfl⟩,?_⟩
  · intro i hf hl
    obtain ⟨z, hz, hzold, hzout⟩ := A.crossing i hf hl
    exact ⟨z,hzold,hzout⟩
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      (trace_constant_action_integrable_bound A hr hv hclock hA j).2)
    have hsum := H.sum_regularizedStage_sub (fun s : ℝ => s^3) (H.activeStage_mono hat)
      le_rfl hv hup hlo
    rw [← Finset.mul_sum, hsum, zero_pow (by norm_num : (3 : ℕ) ≠ 0),sub_zero] at hh
    exact hh.trans_eq (by ring)

theorem ObservedHistory.exists_short_low_action_seed_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {r : ℝ} (h : H.isParabolicallyRmControlledBall t p r) :
    ∀ v : ℝ, 0 < v → v ≤ r / 2 →
      ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = (t : ℝ) - v ^ 2 ∧
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p,
          A.isRmControlled (hat := hat) r ∧
          ∃ action : ℝ,
            action ∈ H.regularizedC1ActionValues (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) t 0 v p
              (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) ∧
            action ≤ 6 * v ^ 3 / r ^ 2 ∧ action / (2*v) ≤ 3/4 ∧
            2*v*action - 6*v^2 < 0 := by
  intro v hv hvr
  obtain ⟨hr,a,hat,ha,htrace⟩ := h
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A,hA⟩ := htrace p hp
  have hvr' : v ≤ r := by linarith
  have hv2 : v^2 ≤ r^2 := pow_le_pow_left₀ hv.le hvr' 2
  let b : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ)-v^2, by
    have h0 := a.property.1
    rw [ha] at h0
    linarith, (sub_le_self _ (sq_nonneg v)).trans t.property.2⟩
  have hab : a ≤ b := by change (a : ℝ) ≤ (t : ℝ)-v^2; rw [ha]; linarith
  have hbt : b ≤ t := sub_le_self _ (sq_nonneg v)
  let A' := A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)
  have hA' : A'.isRmControlled (hat := hbt) r := hA.restrictFirst A hr.le le_rfl hab hbt
  obtain ⟨action,hm,hbound⟩ := A'.exists_regularizedC1ActionValues_le_of_isRmControlled
    hr hv.le rfl hA'
  have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hbound
  have hquad : 4*v^2 ≤ r^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 3*v/2)
  have habound : action ≤ 3*v/2 := (le_of_mul_le_mul_right
    (hh.trans (by nlinarith only [hmul])) (sq_pos_of_pos hr))
  refine ⟨b,hbt,rfl,A',hA',action,hm,hbound,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2*v)).mpr
    linarith
  · nlinarith [sq_pos_of_pos hv]


theorem ObservedHistory.exists_short_regularizedCost_upper_bound_of_parabolicallyRmControlledBall
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {r : ℝ} (h : H.isParabolicallyRmControlledBall t p r)
    (B : ℝ)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ z : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) z) :
    ∀ v : ℝ, 0 < v → v ≤ r/2 →
      ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = (t : ℝ)-v^2 ∧
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p,
          A.isRmControlled (hat := hat) r ∧
          ∃ action : ℝ,
            (action : WithTop ℝ) ∈ H.regularizedActionValues (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) t B 0 v p
              (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) ∧
            H.regularizedCost (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat)
              t B 0 v p (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) ≤ action ∧
            action ≤ 6*v^3/r^2 ∧ action/(2*v) ≤ 3/4 ∧ 2*v*action-6*v^2 < 0 := by
  intro v hv hvr
  obtain ⟨a,hat,hclock,A,hA,action,hmem,hbound,hred,hneg⟩ :=
    H.exists_short_low_action_seed_of_parabolicallyRmControlledBall t p h v hv hvr
  have hmemAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat)
    (fun j s hs z => hfloor j.val ((t : ℝ)-s^2) (H.mapsTo_regularizedStage_Ioo t 0 v j.val hs) z)
    p (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) hmem
  exact ⟨a,hat,hclock,A,hA,action,hmemAC,
    H.regularizedCost_le_of_competitor (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat)
      t B 0 v p _ hmemAC,hbound,hred,hneg⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem regularizedSpatialCost_le_of_parabolicallyRmControlledBall
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier) {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (v : Icc (0 : ℝ) (Real.sqrt t.val)) (hvr : v.val ≤ r) :
    H.regularizedSpatialCost t B p v ≤ ((6 * v.val ^ 3 / r ^ 2 : ℝ) : WithTop ℝ) := by
  obtain ⟨hr, a, hat, ha, htrace⟩ := hball
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨A, hA⟩ := htrace p hp
  have hv2 := pow_le_pow_left₀ v.property.1 hvr 2
  let b : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, by
    have hsquare := (Real.le_sqrt v.property.1 t.property.1).mp v.property.2
    exact ⟨sub_nonneg.mpr hsquare, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩⟩
  have hab : a ≤ b := by change a.val ≤ t.val - v.val ^ 2; rw [ha]; linarith
  have hbt : b ≤ t := by change t.val - v.val ^ 2 ≤ t.val; exact sub_le_self _ (sq_nonneg _)
  let A' := A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)
  have hA' : A'.isRmControlled (hat := hbt) r := hA.restrictFirst A hr.le le_rfl hab hbt
  obtain ⟨action, hmem, hbound⟩ :=
    A'.exists_regularizedC1ActionValues_le_of_isRmControlled hr v.property.1 rfl hA'
  have hmemAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    (H.activeStage b) (H.activeStage t) (H.activeStage_mono hbt)
    (fun j s hs x => hfloor j.val (t.val - s ^ 2)
      (H.mapsTo_regularizedStage_Ioo t 0 v.val j.val hs) x)
    p (A'.point (H.activeStage b) le_rfl (H.activeStage_mono hbt)) hmem
  have hcost := H.regularizedCost_le_of_competitor (H.activeStage b) (H.activeStage t)
    (H.activeStage_mono hbt) t B 0 v.val p _ hmemAC
  rw [H.regularizedSpatialCost_eq_of_mem_stageDomain t B p v (H.activeStage b)
    (H.activeStage_mono hbt) (H.activeStage_mem b)]
  have hlower : BddBelow (range (H.regularizedCost (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) t B 0 v.val p)) := by
    refine ⟨(-(2 * B / 3) * (v.val ^ 3 - 0 ^ 3) : ℝ), ?_⟩
    rintro _ ⟨q, rfl⟩
    exact H.regularizedCost_ge (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) t B 0 v.val p q
  exact (csInf_le hlower (mem_range_self _)).trans (hcost.trans (WithTop.coe_le_coe.mpr hbound))

theorem regularizedSpatialCost_ne_top_and_scaled_sub_sq_neg_of_parabolicallyRmControlledBall
    (t : Icc (0 : ℝ) H.horizon) (B : ℝ) (p : (H.stageAt t).Carrier) {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hfloor : ∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.stageDomain j,
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j s) x)
    (v : Icc (0 : ℝ) (Real.sqrt t.val)) (hv : 0 < v.val) (hvr : v.val ≤ r / 2) :
    H.regularizedSpatialCost t B p v ≠ ⊤ ∧
      2 * v.val * (H.regularizedSpatialCost t B p v).untopD 0 - 6 * v.val ^ 2 < 0 := by
  have hr := hball.1
  have hbound := H.regularizedSpatialCost_le_of_parabolicallyRmControlledBall t B p hball
    hfloor v (by linarith : v.val ≤ r)
  have hfinite : H.regularizedSpatialCost t B p v ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hbound
  refine ⟨hfinite, ?_⟩
  lift H.regularizedSpatialCost t B p v to ℝ using hfinite with m hm
  simp only [WithTop.untopD_coe]
  have hmbound := WithTop.coe_le_coe.mp hbound
  have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hmbound
  have hquad : 4 * v.val ^ 2 ≤ r ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 3 * v.val / 2)
  have hm : m ≤ 3 * v.val / 2 := le_of_mul_le_mul_right
    (hh.trans (by nlinarith only [hmul])) (sq_pos_of_pos hr)
  nlinarith [sq_pos_of_pos hv]

theorem regularizedSpatialCost_ne_top_and_scaled_sub_sq_neg_of_cutoff_records
    (parameters : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hscalar : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) {r : ℝ}
    (hball : H.isParabolicallyRmControlledBall t p r)
    (v : Icc (0 : ℝ) (Real.sqrt t.val)) (hv : 0 < v.val) (hvr : v.val ≤ r / 2) :
    H.regularizedSpatialCost t (3 / a₀) p v ≠ ⊤ ∧
      2 * v.val * (H.regularizedSpatialCost t (3 / a₀) p v).untopD 0 - 6 * v.val ^ 2 < 0 := by
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalar
  apply H.regularizedSpatialCost_ne_top_and_scaled_sub_sq_neg_of_parabolicallyRmControlledBall
    t (3 / a₀) p hball ?_ v hv hvr
  intro j s hs x
  have htime := (H.stageDomain_subset j hs).1
  have hratio : 3 / (a₀ + s) ≤ 3 / a₀ :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right htime)
  have hneg : -(3 / a₀) ≤ -3 / (a₀ + s) := by
    simpa only [neg_div] using neg_le_neg hratio
  exact hneg.trans (hpreserve.1 j s hs x).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
