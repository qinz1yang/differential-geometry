import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Metric.Distance.Boundary
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : MeasurableSpace U :=
  borel U

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : BorelSpace U := ⟨rfl⟩

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

namespace ObservedHistory

private theorem normSq_trace_eq_of_index_eq {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle x) {j k : Fin (H.eventCount + 1)} (hjk : j = k)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) (v : ℝ) :
    normSq0S (H.stageMetric j v) (A.point j hj hjl) 4
      (metricRm04At (H.stageMetric j v) (A.point j hj hjl)) =
    normSq0S (H.stageMetric k v) (A.point k hk hkl) 4
      (metricRm04At (H.stageMetric k v) (A.point k hk hkl)) := by
  subst hjk
  rfl

private theorem sqrt_exp_two : Real.sqrt (Real.exp 2) = Real.exp 1 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos 1).le]

private theorem sqrt_exp_two_pow_three : Real.sqrt (Real.exp 2 ^ 3) = Real.exp 3 := by
  rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * 2 = 3 + 3 by norm_num, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos 3).le]

theorem exists_isParabolicallyRmControlledBall_earlier_volume_le
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r) (t' : Icc (0 : ℝ) H.horizon)
    (ht't : (t' : ℝ) < t) (htt' : (t : ℝ) - r ^ 2 / 9 < t') :
    ∃ p' : (H.stageAt t').Carrier, H.isParabolicallyRmControlledBall t' p' (r / 8) ∧
      riemannianVolumeMeasure ThreeModel (H.stageAt t').Carrier
          (H.stageMetric (H.activeStage t') t')
          (riemannianBallOf (H.stageMetric (H.activeStage t') t') p' (r / 8)) ≤
        ENNReal.ofReal (Real.exp 3) *
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  have hr : 0 < r := hball.1
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, hterm, pU, K, hpU,
    -, hK, hpK, hfront⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall t p r hball
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hat' : a ≤ t' := show (a : ℝ) ≤ t' by rw [ha]; linarith
  have ht't' : t' ≤ t := ht't.le
  have hat'r : (a : ℝ) ≤ t' := hat'
  let j' : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage t', H.activeStage_mono hat', H.activeStage_mono ht't'⟩
  set G := H.stageMetric j'.val t' with hG
  have hS' : S.base.metric t' = localPullMetric G (f j') (hf j') :=
    hmetric j' t' ⟨hat', ht't'⟩ (H.activeStage_mem t')
  have hn3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hn : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by rw [hn3]; norm_num
  have hcurvU : ∀ y : U, ∀ u ∈ Icc (t' : ℝ) t,
      r ^ 4 * Perelman.FlowMetricBall.rmNormSq S u y ≤ 1 := fun y u hu =>
    hRm u ⟨hat'r.trans hu.1, hu.2⟩ y
  have hslab : Icc (t' : ℝ) t ⊆ (RealTimeInterval.closed a.val t.val hat).carrier :=
    fun u hu => ⟨hat'r.trans hu.1, hu.2⟩
  have hreg : Ioo (t' : ℝ) t ⊆ (RealTimeInterval.closed a.val t.val hat).regular :=
    fun u hu => ⟨lt_of_le_of_lt hat'r hu.1, hu.2⟩
  have hexp : Real.exp (2 * ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2 *
      |(t : ℝ) - t'|)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    rw [hn, abs_of_pos (sub_pos.mpr ht't)]
    have h1 : (3 : ℝ) ^ 2 / r ^ 2 * ((t : ℝ) - t') ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hr2]
      linarith
    linarith
  have hexp' : Real.exp (2 * ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2 *
      |(t' : ℝ) - t|)) ≤ Real.exp 2 := by
    rw [abs_sub_comm]
    exact hexp
  have hup : ∀ y : U, ∀ v : TangentSpace ThreeModel y,
      (S.base.metric t).inner y v v ≤ Real.exp 2 * (S.base.metric t').inner y v v := by
    intro y v
    refine (Perelman.inner_le_exp_mul_inner_of_rmNormSq_le hS hr hslab hreg (hcurvU y)
      (right_mem_Icc.mpr ht't') (left_mem_Icc.mpr ht't') v).trans ?_
    exact mul_le_mul_of_nonneg_right hexp (metric_inner_self_nonneg (S.base.metric t') y v)
  have hdown : ∀ y : U, ∀ v : TangentSpace ThreeModel y,
      (S.base.metric t').inner y v v ≤ Real.exp 2 * (S.base.metric t).inner y v v := by
    intro y v
    refine (Perelman.inner_le_exp_mul_inner_of_rmNormSq_le hS hr hslab hreg (hcurvU y)
      (left_mem_Icc.mpr ht't') (right_mem_Icc.mpr ht't') v).trans ?_
    exact mul_le_mul_of_nonneg_right hexp' (metric_inner_self_nonneg (S.base.metric t) y v)
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hfront' : ∀ q ∈ frontier K,
      ENNReal.ofReal (r / 6) ≤ riemannianEDistOf (S.base.metric t') pU q := by
    intro q hq
    by_contra hlt
    rw [not_le] at hlt
    have hsub := DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul
      (S.base.metric t') (S.base.metric t) pU (Real.exp_pos 2)
      (fun y _ v => hup y v) (r := r / 6) hlt
    rw [sqrt_exp_two] at hsub
    have hfar := hfront q hq
    have : Real.exp 1 * (r / 6) ≤ r / 2 := by nlinarith
    exact absurd (hsub.trans_le (ENNReal.ofReal_le_ofReal this)) (not_lt.mpr hfar)
  have hclosed : riemannianClosedBallOf (S.base.metric t') pU (r / 6) ⊆ K :=
    Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance
      (S.base.metric t') hK.isClosed hpK ENNReal.ofReal_ne_top hfront'
  have hcpt : IsCompact (riemannianClosedBallOf (localPullMetric G (f j') (hf j')) pU (r / 6)) := by
    rw [← hS']
    exact hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hclosed
  have hr8 : 0 < r / 8 := by positivity
  have himg := Geometry.Metric.image_riemannianBallOf_localPullMetric G (f j') (hf j') (hinj j')
    pU hr8 (by linarith : r / 8 < r / 6) hcpt
  refine ⟨f j' pU, ?_, ?_⟩
  · have hb0 : (a : ℝ) ≤ (t' : ℝ) - (r / 8) ^ 2 := by rw [ha]; nlinarith
    let b : Icc (0 : ℝ) H.horizon :=
      ⟨(t' : ℝ) - (r / 8) ^ 2, a.2.1.trans hb0, by linarith [t'.2.2, sq_nonneg (r / 8)]⟩
    have hbt : b ≤ t' := show (t' : ℝ) - (r / 8) ^ 2 ≤ t' by linarith [sq_nonneg (r / 8)]
    have hab : a ≤ b := hb0
    have hab' : H.activeStage a ≤ H.activeStage b := H.activeStage_mono hab
    have hvt' : H.activeStage t' ≤ H.activeStage t := H.activeStage_mono ht't'
    refine ⟨hr8, b, hbt, rfl, fun x hx => ?_⟩
    rw [← himg] at hx
    obtain ⟨w, -, rfl⟩ := hx
    let A : BackwardPointTrace H (H.activeStage b) (H.activeStage t') (H.activeStage_mono hbt)
        (f j' w) :=
      { point := fun k hk hkl => f ⟨k, hab'.trans hk, hkl.trans hvt'⟩ w
        endpoint_eq := rfl
        crossing := fun i hi hl => hcross i (hab'.trans hi) (hl.trans hvt') w }
    have hslabA : ∀ (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hst : s ≤ t'),
        (r / 8) ^ 4 * normSq0S (H.stageMetric (H.activeStage s) s)
          (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst)) 4
          (metricRm04At (H.stageMetric (H.activeStage s) s)
            (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst))) ≤
          1 := by
      intro s hbs hst
      have has : a ≤ s := hab.trans hbs
      have hst' : s ≤ t := hst.trans ht't'
      let js : H.StageInterval (H.activeStage a) (H.activeStage t) :=
        ⟨H.activeStage s, H.activeStage_mono has, H.activeStage_mono hst'⟩
      have hms := hmetric js s ⟨has, hst'⟩ (H.activeStage_mem s)
      have hb := hRm s ⟨has, hst'⟩ w
      change r ^ 4 * normSq0S (S.base.metric s) w 4 (metricRm04At (S.base.metric s) w) ≤ 1 at hb
      rw [hms, normSq0S_metricRm04At_localPullMetric] at hb
      have hpow : (r / 8) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hr8.le (by linarith) 4
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans hb
    refine ⟨A, hslabA, ?_⟩
    intro i hf' hl
    have hIoc := (H.crossed_event_iff_mem_Ioc b t' i).mp ⟨hf', hl⟩
    let vT : Icc (0 : ℝ) H.horizon := ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
    have havT : H.activeStage vT = i.succ := H.activeStage_at_time i.succ
    have hbT : b ≤ vT := hIoc.1.le
    have hTv : vT ≤ t' := hIoc.2
    have hb := hslabA vT hbT hTv
    rw [normSq_trace_eq_of_index_eq A havT (H.activeStage_mono hbT) (H.activeStage_mono hTv)
      (hf'.trans (Fin.castSucc_lt_succ (i := i)).le) hl] at hb
    have hx := MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.event i)
      (p := ⟨A.point i.castSucc hf' (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf' hl).mem_terminalRegularRegion (H.event i)⟩) (A.crossing i hf' hl)
    change (r / 8) ^ 4 * normSq0S (H.event i).terminal.metric _ 4 (metricRm04At _ _) ≤ 1
    rw [hx, H.event_output i, ← H.stageMetric_initial]
    exact hb
  · have hmeas : MeasurableSet (riemannianBallOf (S.base.metric t') pU (r / 8)) :=
      (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ pU)
        continuous_const).measurableSet
    have hveq := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      (localPullMetric G (f j') (hf j')) G (f j') (hf j') (hinj j')
      (fun x v w => localPullMetric_inner G (f j') (hf j') x v w) (hS' ▸ hmeas)
    rw [himg] at hveq
    have hcmp := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
      (S.base.metric t) (S.base.metric t') (Real.exp_pos 2) hmeas (fun y _ v => hdown y v)
    rw [hn3, sqrt_exp_two_pow_three] at hcmp
    have hmeasU : MeasurableSet (riemannianBallOf (S.base.metric t') pU (r / 8)) := hmeas
    have hval := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      (S.base.metric t) (H.stageMetric (H.activeStage t) t) (Subtype.val : U → _)
      (isLocalDiffeomorph_subtype_val U) Subtype.val_injective
      (fun x v w => by
        rw [hterm, ← localPullMetric_subtype_val, localPullMetric_inner]) hmeasU
    have hsubU : (Subtype.val : U → _) '' riemannianBallOf (S.base.metric t') pU (r / 8) ⊆
        riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
      rintro _ ⟨y, -, rfl⟩
      rw [← hU]
      exact y.2
    calc riemannianVolumeMeasure ThreeModel (H.stageAt t').Carrier
          (H.stageMetric (H.activeStage t') t')
          (riemannianBallOf (H.stageMetric (H.activeStage t') t') (f j' pU) (r / 8))
        = riemannianVolumeMeasure ThreeModel U (S.base.metric t')
            (riemannianBallOf (S.base.metric t') pU (r / 8)) := by
          rw [hS']
          exact hveq.symm
      _ ≤ ENNReal.ofReal (Real.exp 3) * riemannianVolumeMeasure ThreeModel U (S.base.metric t)
            (riemannianBallOf (S.base.metric t') pU (r / 8)) := hcmp
      _ ≤ _ := by
          rw [hval]
          exact mul_le_mul' le_rfl (MeasureTheory.measure_mono hsubU)

end ObservedHistory

namespace RetainedCoreHistory

def NoncollapsedAtRegularTimesBefore (H : RetainedCoreHistory.{u})
    (κ ρ t₀ : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
    (t : ℝ) < t₀ → (∀ i : Fin (H.eventCount + 1), H.time i ≠ t) → r ≤ ρ →
    H.toHistory.isParabolicallyRmControlledBall t p r →
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)

end RetainedCoreHistory

theorem exists_noncollapsedBefore_of_regularTimes :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (H : RetainedCoreHistory.{u})
      {κ ρ t₀ : ℝ}, 0 < κ → H.NoncollapsedAtRegularTimesBefore κ ρ t₀ →
        H.NoncollapsedBefore (c * κ) ρ t₀ := by
  have he : 0 < Real.exp 3 := Real.exp_pos 3
  have he1 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  refine ⟨1 / (512 * Real.exp 3), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith
  intro H κ ρ t₀ hκ hreg t p r ht hrρ hball
  have hr : 0 < r := hball.1
  have hrt : r ^ 2 ≤ (t : ℝ) := hball.radius_sq_le_time H.toHistory
  have hlt : (t : ℝ) - r ^ 2 / 9 < t := by
    have := pow_pos hr 2
    linarith
  obtain ⟨s, ⟨hs1, hs2⟩, hsreg⟩ :=
    ((Set.Ioo_infinite hlt).sdiff (Set.finite_range H.time)).nonempty
  have hs0 : 0 ≤ s := by
    have := pow_pos hr 2
    linarith
  let t' : Icc (0 : ℝ) H.toHistory.horizon := ⟨s, hs0, hs2.le.trans t.2.2⟩
  obtain ⟨p', hball', hvol⟩ :=
    H.toHistory.exists_isParabolicallyRmControlledBall_earlier_volume_le t p r hball t' hs2 hs1
  have hκr := hreg t' p' (r / 8) (hs2.trans_le ht)
    (fun i hi => hsreg ⟨i, hi⟩) ((by linarith : r / 8 ≤ r).trans hrρ) hball'
  have hkey : ENNReal.ofReal (1 / (512 * Real.exp 3) * κ) * ENNReal.ofReal r ^ 3 *
      ENNReal.ofReal (Real.exp 3) = ENNReal.ofReal κ * ENNReal.ofReal (r / 8) ^ 3 := by
    rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hκ.le]
    congr 1
    field_simp
    ring
  have hchain := hkey.trans_le (hκr.trans hvol)
  rw [mul_comm (ENNReal.ofReal (Real.exp 3))] at hchain
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr he).ne'
    ENNReal.ofReal_ne_top).mp hchain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
