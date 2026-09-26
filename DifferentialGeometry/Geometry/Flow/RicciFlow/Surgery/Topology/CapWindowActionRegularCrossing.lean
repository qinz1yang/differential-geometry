import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction
import Mathlib.Topology.Order.LeftRight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowScalarLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PreparedCapCommonFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuityMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.EventContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.TimeContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryActionBackwardClock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBallCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapRegularCrossing
set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

open DifferentialGeometry.Tensor0SBundle in
theorem exists_uniform_prepared_survival_action_lower_bound_of_parabolicallyRmControlledBall
    (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrTest : 0 < rTest) :
    ∃ theta r qmin Cbirth : ℝ, ∃ htheta : theta ∈ Ioo (0 : ℝ) 1,
      0 < r ∧ 0 < qmin ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (Rbirth : ℝ),
      let D := max 1 (Rbirth + r + 2);
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A₀ : ℝ} {hA : 0 < A₀}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A₀ hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (capFirst : Fin (H.eventCount + 1))
        (t : Icc (0 : ℝ) H.horizon) (hbirth : H.time capFirst < t.val),
      ∀ (Jbig : standardCapWindow Dbig → (H.stage capFirst).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric capFirst).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ H.activeStage t → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin (H.eventCount + 1), capFirst ≤ j → j ≤ H.activeStage t →
        ∀ x : (H.stage j).Carrier, ∀ v ∈ Ioo (H.time j) (H.stageEndTime j), v ≤ t.val →
          q₀ < metricScalarAt (H.stageMetric j v) x →
          |derivWithin (fun a => metricScalarAt (H.stageMetric j a) x) (Iic v) v| ≤
            Cderiv * metricScalarAt (H.stageMetric j v) x ^ 2) →
      let s := min t.val (H.time capFirst + theta / q);
      let hs : H.time capFirst < s := by
        exact lt_min hbirth (lt_add_of_pos_right _ (div_pos htheta.1 hq));
      let stop : Icc (0 : ℝ) H.horizon :=
        ⟨s, (H.time_nonneg capFirst).trans hs.le, (min_le_left _ _).trans t.property.2⟩;
      let hfs : capFirst ≤ H.activeStage stop := H.le_activeStage stop capFirst hs.le;
      (∃ z : standardCapWindow D, Jbig (inc z) ∈
        range (H.backwardSurvivorMap capFirst (H.activeStage stop) hfs capFirst le_rfl hfs)) →
      qmin ≤ q → ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTest →
      let hlast : capFirst ≤ H.activeStage t := H.le_activeStage t capFirst hbirth.le;
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ capFirst) (v : ℝ),
        0 ≤ v → v ≤ Ebound →
        t.val - v ^ 2 ∈ H.stageDomain first → t.val - v ^ 2 ≤ H.time capFirst →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (alpha j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (hlast), le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      ∀ xPast : standardCapWindow Dbig, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨capFirst, hfirst, hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig xPast →
      A < ∑ j : H.StageInterval first (H.activeStage t), H.stageRegularizedAction j.val t.val (alpha j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) := by
  obtain ⟨theta, r, eta, qmin, htheta, hr, heta, hqmin, haction⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_cap_prefix_near_controlled_terminal_region
      A B Ebound (1 / rTest ^ 4) (rTest / 2) rTest hB hEbound (half_pos hrTest) hrTest
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hflow⟩ :=
    exists_uniform_prepared_cap_common_flow_until_normalized_time.{u, uE, uH, uM}
      theta Cderiv htheta.1 htheta.2
  refine ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ Rbirth D
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hflow⟩ :=
    hflow (I := I) D 1 eta hD zero_lt_one heta 2
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A₀ hA Dbig m ζ w hR hm hζ hDD inc
    H capFirst t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv s hs stop hfs hmarker hqscale p hball hlast
    first hfirst v hv hvE hlowerPath hstart alpha halpha hint hscalar hrecent hnode xPast hnormPast hbirthPath
  obtain ⟨z, hz⟩ := hmarker
  obtain ⟨hage, hstop, y, hy, capLast, hcapLast, hcapStop, G, L, hsEnd, hG,
      gcap, hgcap, hcapinj, hcapbirth, hcapcross, Scap, hScap, hcapmetric, hcurv,
      Φ, hΦ, hΦval, hmarked, hterminal, Q, hQ, hclose⟩ :=
    hflow w hR hm hζ H capFirst t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
      parameters records hfixed hlower hdelta hderiv z hz
  have hsTarget : s ≤ t.val := min_le_left _ _
  have hcapLastTarget : capLast ≤ H.activeStage t := hcapStop.trans (H.activeStage_mono hsTarget)
  obtain ⟨ta, hat, hta, U, hU, f, hf, hinj, hcross, hflast, S, hS, hmetric, hRm,
      hterminalPole, pU, K, hpU, himage, hK, hpinterior, hseparation⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall t p rTest hball
  let S' := S.timeRestrict
    (RealTimeInterval.closed (t.val - rTest ^ 2) t.val (sub_le_self _ (sq_nonneg rTest)))
  have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS
    (Icc_subset_Icc hta.le le_rfl) (Ioo_subset_Ioo hta.le le_rfl)
  have hupper : t.val ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.activeStage_time_le t, H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩
  have hcontrolled : t.val - rTest ^ 2 ∈ H.stageDomain (H.activeStage ta) := by
    rw [← hta]
    exact H.activeStage_mem ta
  have hRm' : ∀ r ∈ Icc (t.val - rTest ^ 2) t.val, ∀ x : U,
      normSq0S (S'.base.metric r) x 4 (S'.base.rm04 r x) ≤ 1 / rTest ^ 4 := by
    intro r hr x
    change normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ 1 / rTest ^ 4
    apply (le_div_iff₀ (pow_pos hrTest 4)).mpr
    simpa only [mul_comm] using hRm r ⟨hta.le.trans hr.1, hr.2⟩ x
  let xPastD : standardCapWindow D := ⟨xPast.val, by
    change ‖xPast.val‖ < D + 1
    have hd := le_max_right (1 : ℝ) (Rbirth + r + 2)
    change Rbirth + r + 2 ≤ D at hd
    linarith⟩
  have hincPast : inc xPastD = xPast := Subtype.ext rfl
  apply haction U H first capFirst capLast (H.activeStage ta) (H.activeStage t)
    hfirst hcapLast hcapLastTarget (H.activeStage_mono hat) f hf hinj hcross t.val v hv hvE S' hS'
    hupper hlowerPath hcontrolled
    (fun j r hr hstage => hmetric j r ⟨hta.le.trans hr.1, hr.2.le⟩ hstage)
    hRm' K hK pU hpinterior hseparation D Rbirth (Rbirth + r) le_rfl
    (by have hd := le_max_right (1 : ℝ) (Rbirth + r + 2); change Rbirth+r+2≤D at hd; linarith)
    gcap hgcap hcapinj hcapcross Q (H.time capFirst) s q hs hsTarget hstart hq hqscale Scap hScap
    ⟨G.lt.le, hsEnd⟩ (H.time_mem_stageDomain capFirst) hage
    (fun j r hr hstage => hcapmetric j r hstage hr.2)
    (fun r hr x k hk => ((hclose r hr).2 k hk x).le)
    alpha halpha hint hscalar ?_ hnode xPastD hnormPast ?_ ?_
  · rw [hflast, hpU]
    exact hrecent
  · rw [hcapbirth]
    change alpha ⟨capFirst, hfirst, hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig (inc xPastD)
    rw [hincPast]
    exact hbirthPath
  · exact hstop.imp id Or.inl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

open DifferentialGeometry.Tensor0SBundle in
theorem exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall
    (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrTest : 0 < rTest) :
    ∃ theta r qmin Cbirth : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧
      0 < r ∧ 0 < qmin ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (Rbirth : ℝ),
      let a := max 1 (Rbirth + r);
      ∃ D : ℝ, 0 < D ∧ a + 1 < D ∧
      ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A₀ : ℝ} {hA : 0 < A₀}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A₀ hA Dbig m ζ), R ≤ Dbig → m₀ ≤ m → ζ ≤ ζ₀ →
      ∀ (H : ObservedHistory.{u}) (capFirst : Fin (H.eventCount + 1))
        (t : Icc (0 : ℝ) H.horizon) (hbirth : H.time capFirst ≤ t.val),
      ∀ (Jbig : standardCapWindow Dbig → (H.stage capFirst).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric capFirst).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ H.activeStage t → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin (H.eventCount + 1), capFirst ≤ j → j ≤ H.activeStage t →
        ∀ x : (H.stage j).Carrier, ∀ v ∈ Ioo (H.time j) (H.stageEndTime j), v ≤ t.val →
          q₀ < metricScalarAt (H.stageMetric j v) x →
          |derivWithin (fun a => metricScalarAt (H.stageMetric j a) x) (Iic v) v| ≤
            Cderiv * metricScalarAt (H.stageMetric j v) x ^ 2) →
      qmin ≤ q → ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTest →
      let hlast : capFirst ≤ H.activeStage t := H.le_activeStage t capFirst hbirth;
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ capFirst) (v : ℝ),
        0 ≤ v → v ≤ Ebound →
        t.val - v ^ 2 ∈ H.stageDomain first → t.val - v ^ 2 ≤ H.time capFirst →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (alpha j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (hlast), le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      ∀ xPast : standardCapWindow Dbig, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨capFirst, hfirst, hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig xPast →
      A < ∑ j : H.StageInterval first (H.activeStage t), H.stageRegularizedAction j.val t.val (alpha j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) := by
  obtain ⟨theta, r, eta, qmin₀, htheta, hr, heta, hqmin₀, hCaction⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_cap_prefix_near_controlled_terminal_region
      A B Ebound (1 / rTest ^ 4) (rTest / 2) rTest hB hEbound (half_pos hrTest) hrTest
  obtain ⟨εfloor, hεfloor, hfloor⟩ := StandardCap.exists_uniform_window_scale_bound_of_rm_bound
  let qmin := max qmin₀ (19 / rTest ^ 2)
  have hqmin : 0 < qmin := hqmin₀.trans_le (le_max_left _ _)
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hevolve⟩ :=
    exists_uniform_prepared_cap_evolution.{u, uE, uH, uM} theta Cderiv htheta.1 htheta.2
  refine ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ Rbirth a
  have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
  have hgap : Rbirth + r ≤ a := le_max_right _ _
  obtain ⟨D, hD, haD, _, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hevolve⟩ :=
    hevolve (I := I) a 0 eta ha heta 2
  refine ⟨D, hD, haD, R, hDR, m₀, hm₀, min ζ₀ εfloor, δ₀, lt_min hζ₀ hεfloor, (min_le_left _ _).trans hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A₀ hA Dbig m ζ w hR hm hζ
    H capFirst t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hqscale p hball hlast
    first hfirst v hv hvE hlowerPath hstart alpha halpha hint hscalar hrecent hnode xPast hnormPast hbirthPath
  have hDD : D ≤ Dbig := by linarith
  let inc : standardCapWindow D → standardCapWindow Dbig :=
    TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)))
  have hζ₀' : ζ ≤ ζ₀ := hζ.trans (min_le_left _ _)
  have hqscale₀ : qmin₀ ≤ q := (le_max_left _ _).trans hqscale
  by_cases hstrict : H.time capFirst < t.val
  swap
  · exact False.elim (by
      have heq : H.time capFirst = t.val := le_antisymm hbirth (le_of_not_gt hstrict)
      have htstage : t = H.stageTime capFirst := Subtype.ext heq.symm
      have hac : H.activeStage t = capFirst := by rw [htstage, H.activeStage_stageTime]
      subst capFirst
      have hp : p = Jbig xPast := by
        rw [heq, sub_self, Real.sqrt_zero] at hbirthPath
        exact hrecent.symm.trans hbirthPath
      have hpball : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t.val) p rTest := by
        change riemannianEDistOf _ p p < ENNReal.ofReal rTest
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr hrTest
      have hRmBirth := hball.terminal_curvature_bound H p hpball
      rw [← heq, H.stageMetric_initial, hp] at hRmBirth
      have hbound := hfloor w (hζ.trans (min_le_right _ _)) (by omega : 2 ≤ m)
        (H.initialMetric (H.activeStage t)) Jbig hJbig q hq hzero xPast
        (by have hx := hnormPast; linarith : ‖xPast.val‖ < Dbig) rTest hRmBirth
      have hscale : 19 / rTest ^ 2 ≤ q := (le_max_right _ _).trans hqscale
      have hnineteen := (div_le_iff₀ (sq_pos_of_pos hrTest)).mp hscale
      nlinarith)
  have hevolution := hevolve w hR hm hζ₀' H capFirst t hstrict Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq
    hzero parameters records hfixed hlower hdelta hderiv
  obtain ⟨ta, hat, hta, U, hU, f, hf, hinj, hcross, hflast, S, hS, hmetric, hRm,
      hterminalPole, pU, K, hpU, himage, hK, hpinterior, hseparation⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall t p rTest hball
  let S' := S.timeRestrict
    (RealTimeInterval.closed (t.val - rTest ^ 2) t.val (sub_le_self _ (sq_nonneg rTest)))
  have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS
    (Icc_subset_Icc hta.le le_rfl) (Ioo_subset_Ioo hta.le le_rfl)
  have hupper : t.val ∈ Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.activeStage_time_le t, H.le_stageEndTime_of_mem_stageDomain (H.activeStage_mem t)⟩
  have hcontrolled : t.val - rTest ^ 2 ∈ H.stageDomain (H.activeStage ta) := by
    rw [← hta]
    exact H.activeStage_mem ta
  have hRm' : ∀ u ∈ Icc (t.val - rTest ^ 2) t.val, ∀ x : U,
      normSq0S (S'.base.metric u) x 4 (S'.base.rm04 u x) ≤ 1 / rTest ^ 4 := by
    intro u hu x
    change normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ 1 / rTest ^ 4
    apply (le_div_iff₀ (pow_pos hrTest 4)).mpr
    simpa only [mul_comm] using hRm u ⟨hta.le.trans hu.1, hu.2⟩ x
  let xPastD : standardCapWindow D := ⟨xPast.val, by change ‖xPast.val‖ < D + 1; linarith⟩
  have hincPast : inc xPastD = xPast := Subtype.ext rfl
  have hrecent' : alpha ⟨H.activeStage t, hfirst.trans hlast, le_rfl⟩ 0 =
      f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ pU := by
    rw [hflast, hpU]
    exact hrecent
  rcases hevolution with hsurvive | hdiscard
  · obtain ⟨s, hbs, hsT, hage, hstop, capLast, hcapLast, hcapLastTarget, G, L, hsEnd, hG,
      gcap, hgcap, hcapinj, hcapbirth, hcapcross, Scap, hScap, hcapmetric, hcurv,
      Φ, hΦ, hΦval, hterminal, Q, hQ, hclose⟩ := hsurvive
    apply hCaction U H first capFirst capLast (H.activeStage ta) (H.activeStage t)
      hfirst hcapLast hcapLastTarget (H.activeStage_mono hat) f hf hinj hcross t.val v hv hvE S' hS'
      hupper hlowerPath hcontrolled
      (fun j u hu hstage => hmetric j u ⟨hta.le.trans hu.1, hu.2.le⟩ hstage)
      hRm' K hK pU hpinterior hseparation D Rbirth a hgap (by linarith)
      gcap hgcap hcapinj hcapcross Q (H.time capFirst) s q hbs hsT hstart hq hqscale₀ Scap hScap
      ⟨G.lt.le, hsEnd⟩ (H.time_mem_stageDomain capFirst) hage
      (fun j u hu hstage => hcapmetric j u hstage hu.2)
      (fun u hu x k hk => ((hclose u hu).2 k hk x).le)
      alpha halpha hint hscalar hrecent' hnode xPastD hnormPast ?_ (hstop.imp id Or.inl)
    rw [hcapbirth]
    change alpha ⟨capFirst, hfirst, hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig (inc xPastD)
    rw [hincPast]
    exact hbirthPath
  · obtain ⟨i, hfi, hit, hiT, hage, gcap, hgcap, hcapinj, hcapbirth, hcapcross,
      Scap, hScap, hinit, hcapmetric, hcurv, Φ, hΦ, hΦval, hterminal, hdiscarded, Q, hQ, hclose⟩ := hdiscard
    have hcaplast : i.castSucc ≤ H.activeStage t := i.castSucc_lt_succ.le.trans hit
    have hbs : H.time capFirst < H.time i.succ := H.time_strictMono (hfi.trans_lt i.castSucc_lt_succ)
    have hdisjoint : Disjoint (gcap ⟨i.castSucc, hfi, le_rfl⟩ ''
        {y : standardCapWindow D | ‖y.val‖ ≤ a}) (range (fun y : (H.event i).old => y.val.val)) := by
      apply (H.event i).disjoint_old_image_of_discarded_core
      intro y hy
      obtain ⟨z, hz, dd, hdd⟩ := hdiscarded y hy
      exact ⟨z, hz.trans (congrFun hΦval y), dd, hdd⟩
    apply hCaction U H first capFirst i.castSucc (H.activeStage ta) (H.activeStage t)
      hfirst hfi hcaplast (H.activeStage_mono hat) f hf hinj hcross t.val v hv hvE S' hS'
      hupper hlowerPath hcontrolled
      (fun j u hu hstage => hmetric j u ⟨hta.le.trans hu.1, hu.2.le⟩ hstage)
      hRm' K hK pU hpinterior hseparation D Rbirth a hgap (by linarith)
      gcap hgcap hcapinj hcapcross Q (H.time capFirst) (H.time i.succ) q hbs hiT hstart hq hqscale₀ Scap hScap
      (by rw [H.stageEndTime_castSucc]; exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
      (H.time_mem_stageDomain capFirst) hage
      (fun j u hu hstage => hcapmetric j u hstage hu.2)
      (fun u hu x k hk => ((hclose u hu).2 k hk x).le)
      alpha halpha hint hscalar hrecent' hnode xPastD hnormPast ?_ ?_
    · rw [hcapbirth]
      change alpha ⟨capFirst, hfirst, hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig (inc xPastD)
      rw [hincPast]
      exact hbirthPath
    · right
      right
      refine ⟨⟨i.castSucc, hfi, le_rfl⟩, ?_⟩
      intro hstay
      have hclock : H.regularizedStageStart t.val (Real.sqrt (t.val - H.time i.succ)) i.castSucc =
          Real.sqrt (t.val - H.time i.succ) := by
        apply H.regularizedStageStart_eq_of_mem_Icc (Real.sqrt_nonneg _)
        rw [Real.sq_sqrt (sub_nonneg.mpr hiT), sub_sub_cancel, H.stageEndTime_castSucc]
        exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
      have hbounds := H.regularizedStage_bounds (Real.sqrt_nonneg (t.val - H.time i.succ))
        (Real.sqrt_le_sqrt (sub_le_sub_left hbs.le t.val))
        (show t.val - Real.sqrt (t.val - H.time i.succ) ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) by
          rw [Real.sq_sqrt (sub_nonneg.mpr hiT), sub_sub_cancel, H.stageEndTime_castSucc]
          exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
        (show t.val - Real.sqrt (t.val - H.time capFirst) ^ 2 ∈ H.stageDomain capFirst by
          rw [Real.sq_sqrt (sub_nonneg.mpr (hbs.le.trans hiT)), sub_sub_cancel]
          exact H.time_mem_stageDomain capFirst)
        (⟨i.castSucc, hfi, le_rfl⟩ : H.StageInterval capFirst i.castSucc)
      have hinside := hstay (show Real.sqrt (t.val - H.time i.succ) ∈ Icc
          (H.regularizedStageStart t.val (Real.sqrt (t.val - H.time i.succ)) i.castSucc)
          (H.regularizedStageEnd t.val (Real.sqrt (t.val - H.time capFirst)) i.castSucc) by
        rw [hclock] at hbounds ⊢
        exact ⟨le_rfl, hbounds.2.1⟩)
      obtain ⟨old, hold, _⟩ := hnode i (hfirst.trans hfi) hit
      exact Set.disjoint_left.mp hdisjoint hinside ⟨old, hold⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

section

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_canonical_cap_birth_action_lower_bound
    (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrTest : 0 < rTest) :
    ∃ qmin Cbirth R : ℝ, 0 < qmin ∧ 0 < Cbirth ∧ StandardCap.transitionEnd < R ∧
      ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (event : Fin H.eventCount)
        (t : Icc (0 : ℝ) H.horizon) (hevent : event.succ ≤ H.activeStage t)
        (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
        (boundary : (H.event event).RetainedBoundaryIndex),
      let cap := (records event).static boundary;
      let q := cap.neck.scale;
      cap.hasCanonicalWindow → R ≤ parameters.modelRadius → m₀ ≤ parameters.modelOrder →
      parameters.modelAccuracy ≤ ζ₀ →
      ∀ (q₀ a₀ : ℝ), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, event.succ ≤ j.castSucc → j.succ ≤ H.activeStage t → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin (H.eventCount + 1), event.succ ≤ j → j ≤ H.activeStage t →
        ∀ x : (H.stage j).Carrier, ∀ v ∈ Ioo (H.time j) (H.stageEndTime j), v ≤ t.val →
          q₀ < metricScalarAt (H.stageMetric j v) x →
          |derivWithin (fun a => metricScalarAt (H.stageMetric j a) x) (Iic v) v| ≤
            Cderiv * metricScalarAt (H.stageMetric j v) x ^ 2) →
      qmin ≤ q → ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTest →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ event.succ) (v : ℝ),
        0 ≤ v → v ≤ Ebound → t.val - v ^ 2 ∈ H.stageDomain first → t.val - v ^ 2 ≤ H.time event.succ →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (alpha j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      (∀ j, ∀ s ∈ Ioo (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans hevent, le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (t.val - H.time i.succ))) →
      ∀ z : ThreeBall,
      alpha ⟨event.succ, hfirst, hevent⟩ (Real.sqrt (t.val - H.time event.succ)) =
        cap.inclusion (cap.witness.cap z) →
      A < ∑ j : H.StageInterval first (H.activeStage t), H.stageRegularizedAction j.val t.val (alpha j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) := by
  obtain ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, hprepared⟩ :=
    exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall.{u, 0, 0, u}
      A B Ebound rTest Cderiv hB hEbound hrTest
  obtain ⟨D, hD, haD, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hprepared⟩ :=
    hprepared (I := ThreeModel) StandardCap.transitionEnd
  have hR : StandardCap.transitionEnd < R := by
    have hh := le_max_right (1 : ℝ) (StandardCap.transitionEnd + r)
    linarith
  refine ⟨qmin, Cbirth, R, hqmin, hCbirth, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H event t hevent parameters records boundary cap q hcanonical hRadius hm hζ
    q₀ a₀ hq₀ hqbirth haq hfixed hlower hdelta hderiv hqmin' p hball
    first hfirst v hv hvE hlowerPath hstart alpha halpha hint hscalar hrecent hnode z hbirthPath
  obtain ⟨x₀, δ, k, datum, w, _, hmetric, hcap⟩ := hcanonical
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hzero : ∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      q * (H.initialMetric event.succ).inner (cap.window x)
        (mfderiv ThreeModel ThreeModel cap.window x v) (mfderiv ThreeModel ThreeModel cap.window x z) := by
    intro x v z
    rw [← H.event_output event]
    exact hmetric x v z
  apply hprepared w hRadius hm hζ H event.succ t
    ((H.time_strictMono.monotone hevent).trans (H.activeStage_time_le t))
    cap.window cap.window_smooth q q₀ a₀ cap.neck.scale_pos hq₀ hqbirth haq hzero parameters records
    hfixed hlower hdelta hderiv hqmin' p hball first hfirst v hv hvE hlowerPath hstart
    alpha halpha hint hscalar hrecent hnode x hx
  exact hbirthPath.trans hpoint.symm

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_interior_old_nodes_of_action_le
    (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrTest : 0 < rTest) :
    ∃ qmin Cbirth R : ℝ, 0 < qmin ∧ 0 < Cbirth ∧ StandardCap.transitionEnd < R ∧
      ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (event : Fin H.eventCount)
        (t : Icc (0 : ℝ) H.horizon) (hevent : event.succ ≤ H.activeStage t)
        (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
        ,
      (∀ b : (H.event event).RetainedBoundaryIndex, ((records event).static b).hasCanonicalWindow) → R ≤ parameters.modelRadius → m₀ ≤ parameters.modelOrder →
      parameters.modelAccuracy ≤ ζ₀ →
      ∀ (q₀ a₀ : ℝ), 0 < q₀ → (∀ b : (H.event event).RetainedBoundaryIndex, q₀ ≤ Cbirth * ((records event).static b).neck.scale) →
      (∀ b : (H.event event).RetainedBoundaryIndex, 1 ≤ a₀ * ((records event).static b).neck.scale) →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, event.succ ≤ j.castSucc → j.succ ≤ H.activeStage t → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin (H.eventCount + 1), event.succ ≤ j → j ≤ H.activeStage t →
        ∀ x : (H.stage j).Carrier, ∀ v ∈ Ioo (H.time j) (H.stageEndTime j), v ≤ t.val →
          q₀ < metricScalarAt (H.stageMetric j v) x →
          |derivWithin (fun a => metricScalarAt (H.stageMetric j a) x) (Iic v) v| ≤
            Cderiv * metricScalarAt (H.stageMetric j v) x ^ 2) →
      (∀ b : (H.event event).RetainedBoundaryIndex, qmin ≤ ((records event).static b).neck.scale) → ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p rTest →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ event.castSucc) (v : ℝ),
        0 ≤ v → v ≤ Ebound → t.val - v ^ 2 ∈ H.stageDomain first →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (alpha j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      (∀ j, ∀ s ∈ Ioo (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (event.castSucc_lt_succ.le.trans hevent), le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (t.val - H.time i.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t), H.stageRegularizedAction j.val t.val (alpha j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ A →
      ∀ z : (H.event event).old,
        (H.event event).oldOutput z =
          alpha ⟨event.succ, hfirst.trans event.castSucc_lt_succ.le, hevent⟩
            (Real.sqrt (t.val - H.time event.succ)) →
        letI : ChartedSpace (EuclideanHalfSpace 3) (H.event event).old := (H.event event).oldCharts
        (𝓡∂ 3).IsInteriorPoint z := by
  obtain ⟨qmin, Cbirth, R, hqmin, hCbirth, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, haction⟩ :=
    exists_uniform_canonical_cap_birth_action_lower_bound.{u} A B Ebound rTest Cderiv hB hEbound hrTest
  refine ⟨qmin, Cbirth, R, hqmin, hCbirth, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H event t hevent parameters records hcanonical hRadius hm hζ q₀ a₀ hq₀ hqbirth haq
    hfixed hlower hdelta hderiv hqscale p hball first hfirst v hv hvE hlowerPath
    alpha halpha hint hscalar hrecent hnode hcheap z hz
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event event).old := (H.event event).oldCharts
  by_contra hnot
  obtain ⟨boundary, x, hpres⟩ := (H.event event).exists_retained_cap_of_not_isInteriorPoint
    (records event).old_eq_retained z hnot
  have hpoint : ((records event).static boundary).inclusion
      (((records event).static boundary).witness.cap x) = (H.event event).oldOutput z :=
    Sum.inl.inj ((((records event).static boundary).cap_eq x).symm.trans hpres)
  have hstart : t.val - v ^ 2 ≤ H.time event.succ := by
    have hh := (H.le_stageEndTime_of_mem_stageDomain hlowerPath).trans (H.stageEndTime_mono hfirst)
    simpa only [H.stageEndTime_castSucc] using hh
  have hlarge := haction H event t hevent parameters records boundary (hcanonical boundary) hRadius hm hζ
    q₀ a₀ hq₀ (hqbirth boundary) (haq boundary) hfixed hlower hdelta hderiv (hqscale boundary)
    p hball first (hfirst.trans event.castSucc_lt_succ.le) v hv hvE hlowerPath hstart
    alpha halpha hint hscalar hrecent hnode x (hz.symm.trans hpoint.symm)
  exact (not_lt_of_ge hcheap) hlarge

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_sum_stageRegularizedAction_gt_of_inserted_cap_birth_at_controlled_ball
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
      ((records i).static b).hasCanonicalWindow →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ i.succ)
        (hbirth : H.time i.succ < t.val) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      t.val - v ^ 2 ≤ H.time i.succ →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (H.le_activeStage t i.succ hbirth.le), le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ z : ThreeBall,
      alpha ⟨i.succ, hfirst, H.le_activeStage t i.succ hbirth.le⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨qmin, Cbirth, R, hqmin, hCbirth, hR, m₀, hm₀, ε₀, δ₀, hε₀, hεhalf, hδ₀, haction⟩ :=
    exists_uniform_canonical_cap_birth_action_lower_bound.{u}
      A B E rTerm Cderiv hB hE hrTerm
  let Qmin := max qmin (max (qDeriv / Cbirth) (1 / a₀))
  have hQmin : 0 < Qmin := (one_div_pos.mpr ha₀).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨δscale, hδscale, hscale⟩ :=
    exists_uniform_static_cap_scale_lower_bound c ρ Qmin hc hρ hQmin
  refine ⟨m₀, R, ε₀, min δ₀ δscale, StandardCap.transitionEnd_pos.trans hR,
    hε₀, lt_min hδ₀ hδscale, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    i b hcanonical t p hball first hfirst hbirth v hv hvE hlower hstart
    alpha halpha hint hscalar hrecent hnode z hpast
  let cap := (records i).static b
  let q := cap.neck.scale
  have hcapScale := hscale H i parameters hpc
    ((hδ i).trans (min_le_right _ _)) (hρp i) (records i) b
  have hqminq : qmin ≤ q := (le_max_left _ _).trans hcapScale.le
  have hd : qDeriv / Cbirth ≤ q :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hcapScale.le
  have ha : 1 / a₀ ≤ q :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hcapScale.le
  have hqDerivQ : qDeriv ≤ Cbirth * q := by
    simpa only [mul_comm] using (div_le_iff₀ hCbirth).mp hd
  have haq : 1 ≤ a₀ * q := by simpa only [mul_comm] using (div_le_iff₀ ha₀).mp ha
  exact haction H i t (H.le_activeStage t i.succ hbirth.le) parameters records b hcanonical
    hmodelRadius hm herror qDeriv a₀ hqDeriv hqDerivQ haq hfixed hscalarInitial
    (fun j _ _ z => ((records j).delta_le z).trans ((hδ j).trans (min_le_left _ _)))
    (fun j _ _ x s hs _ => hderiv j x s hs) hqminq p hball first hfirst v hv hvE hlower hstart
    alpha halpha hint hscalar hrecent hnode z hpast

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_node_at_controlled_ball
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ¬ (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, haction⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_inserted_cap_birth_at_controlled_ball.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    t p hball first hle v hv hvE hlower alpha halpha hint hscalar hterminal hnode
    i hf hl hcanonical hbad
  have hbirth : H.time i.succ < t.val := by
    apply lt_of_le_of_ne ((H.time_strictMono.monotone hl).trans (H.activeStage_time_le t))
    intro he
    have hi : H.activeStage t = i.succ := by
      apply le_antisymm _ hl
      apply H.time_strictMono.le_iff_le.mp
      simpa only [he] using H.activeStage_time_le t
    have hindex :
        (⟨H.activeStage t, hle, le_rfl⟩ : H.StageInterval first (H.activeStage t)) =
        ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ := Subtype.ext hi
    have halphaPoint : HEq (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0) p := by
      have hpair := congrArg
        (fun j : H.StageInterval first (H.activeStage t) =>
          (⟨j, alpha j 0⟩ : Sigma fun j : H.StageInterval first (H.activeStage t) =>
            (H.stage j.val).Carrier)) hindex
      exact (Sigma.mk.inj_iff.mp hpair).2.symm.trans (heq_of_eq hterminal)
    have hpoint : alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0 =
        Eq.rec (motive := fun j _ => (H.stage j).Carrier) p hi :=
      eq_of_heq (halphaPoint.trans (eqRec_heq (φ := fun j => (H.stage j).Carrier) hi p).symm)
    have hclock : Real.sqrt (t.val - H.time i.succ) = 0 := by
      rw [he, sub_self, Real.sqrt_zero]
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    rw [hclock] at hzold hznew hbad
    apply hbad
    rw [← hzold, hpoint]
    exact hball.regularCrossing_of_oldOutput_at_event_time H i he.symm z (hznew.trans hpoint)
  have hstart : t.val - v ^ 2 < H.time i.succ := by
    let start : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - v ^ 2, H.stageDomain_subset first hlower⟩
    have hactive : H.activeStage start = first := (H.mem_stageDomain_iff start first).mp hlower
    by_contra hn
    have hi : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
  obtain ⟨b, z, hbirthLabel⟩ : ∃ (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) := by
    rcases (H.event i).regularCrossing_or_cap_of_admissible_node
        (records i).old_eq_retained (hnode i hf hl) with hregular | ⟨b, z, hcap⟩
    · exact (hbad hregular).elim
    · exact ⟨b, z, Sum.inl_injective (hcap.symm.trans (((records i).static b).cap_eq z))⟩
  exact haction H parameters hm hmodelRadius herror hpc hδ hρp records
    hfixed hscalarInitial hderiv i b (hcanonical b) t p hball first
    (hf.trans i.castSucc_lt_succ.le) hbirth v hv hvE hlower hstart.le
    alpha halpha hint hscalar hterminal hnode z hbirthLabel

theorem exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_initial_point_at_controlled_ball
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ i : Fin H.eventCount,
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (v : ℝ), 0 ≤ v → v ≤ E →
      ∀ hstart : t.val - v ^ 2 = H.time i.succ,
      let hle : i.succ ≤ H.activeStage t :=
        H.le_activeStage t i.succ (by rw [← hstart]; exact sub_le_self _ (sq_nonneg v))
      ∀ alpha : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : i.succ ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (¬ ∃ x : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing x.val (alpha ⟨i.succ, le_rfl, hle⟩ v)) →
      A < ∑ j : H.StageInterval i.succ (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, haction⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_inserted_cap_birth_at_controlled_ball.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    i hcanonical t p hball v hv hvE hstart hle alpha halpha hint hscalar hrecent hnode hnonregular
  have hb : H.time i.succ ≤ t.val := by
    rw [← hstart]
    exact sub_le_self _ (sq_nonneg v)
  have hbirth : H.time i.succ < t.val := by
    by_contra hn
    have heq : t.val = H.time i.succ := le_antisymm (not_lt.mp hn) hb
    have hvzero : v = 0 := sq_eq_zero_iff.mp (by linarith only [hstart, heq])
    let hi : H.activeStage t = i.succ := H.activeStage_eq_of_maximal t i.succ
      (by rw [heq]) (fun k hk => H.time_strictMono.le_iff_le.mp (by simpa only [heq] using hk))
    obtain ⟨x, hx⟩ := hball.exists_regularCrossing_at_event_time H i heq
    have hind : (⟨i.succ, le_rfl, hle⟩ : H.StageInterval i.succ (H.activeStage t)) =
        ⟨H.activeStage t, hle, le_rfl⟩ := Subtype.ext hi.symm
    have hpoint : HEq (alpha ⟨i.succ, le_rfl, hle⟩ 0)
        (alpha ⟨H.activeStage t, hle, le_rfl⟩ 0) := by rw [hind]
    have hcast : HEq (show (H.stage i.succ).Carrier from hi ▸ p) p :=
      eqRec_heq (φ := fun j => (H.stage j).Carrier) hi p
    have hpast : alpha ⟨i.succ, le_rfl, hle⟩ v =
        (show (H.stage i.succ).Carrier from hi ▸ p) := by
      rw [hvzero]
      exact eq_of_heq ((hpoint.trans (heq_of_eq hrecent)).trans hcast.symm)
    exact hnonregular ⟨x, hpast.symm ▸ hx⟩
  obtain ⟨b, z, hcap⟩ :=
    (H.event i).exists_regularCrossing_or_cap (records i).old_eq_retained
      (alpha ⟨i.succ, le_rfl, hle⟩ v) |>.resolve_left hnonregular
  have hlabel : alpha ⟨i.succ, le_rfl, hle⟩ v =
      ((records i).static b).inclusion (((records i).static b).witness.cap z) :=
    Sum.inl_injective (hcap.symm.trans (((records i).static b).cap_eq z))
  have hclock : Real.sqrt (t.val - H.time i.succ) = v := by
    have hdiff : t.val - H.time i.succ = v ^ 2 := by linarith only [hstart]
    rw [hdiff, Real.sqrt_sq hv]
  apply haction H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial
    hderiv i b (hcanonical b) t p hball i.succ le_rfl hbirth v hv hvE
    (hstart ▸ H.time_mem_stageDomain i.succ) hstart.le alpha halpha hint hscalar hrecent hnode z
  rw [hclock]
  exact hlabel

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uACNode

private theorem exists_contMDiff_family_action_lt
    (H : ObservedHistory.{uACNode}) {first last : Fin (H.eventCount + 1)}
    (hle : first ≤ last) {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last) (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (halpha : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ beta : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (beta j)) ∧
      (∀ j, beta j (H.regularizedStageStart T u j.val) =
        alpha j (H.regularizedStageStart T u j.val)) ∧
      (∀ j, beta j (H.regularizedStageEnd T v j.val) =
        alpha j (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (beta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) <
        (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (alpha j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) + epsilon := by
  classical
  have hne : Nonempty (H.StageInterval first last) := ⟨⟨first, le_rfl, hle⟩⟩
  let N := Fintype.card (H.StageInterval first last)
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hepsilonN : 0 < epsilon / N := div_pos hepsilon hN
  have hex (j : H.StageInterval first last) :=
    H.exists_contMDiff_stage_action_lt_of_absolutelyContinuousOnInterval hu huv hupper hpast
      alpha halpha hint hnode j hepsilonN
  choose beta hbeta hstart hend hInt hact using hex
  refine ⟨beta, hbeta, hstart, hend, hInt, ?_⟩
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr hne)
    (fun j (_ : j ∈ Finset.univ) => hact j)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hsumEpsilon : (Fintype.card (H.StageInterval first last) : ℝ) * (epsilon / N) = epsilon := by
    dsimp only [N]
    field_simp
  simpa only [hsumEpsilon] using hs

theorem exists_uniform_regularCrossing_of_sum_stageRegularizedAction_lt_at_controlled_ball
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{uACNode}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      (∀ j : H.StageInterval first (H.activeStage t),
        ∀ r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        ∀ x : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x) →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_node_at_controlled_ball.{uACNode}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    t p hball first hle v hv hvE hpast hscalar alpha halpha hint hterminal hnode hsmall
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let S := ∑ j : H.StageInterval first (H.activeStage t),
    H.stageRegularizedAction j.val t (alpha j)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)
  have hepsilon : 0 < (A - S) / 2 := half_pos (sub_pos.mpr hsmall)
  obtain ⟨beta, hbeta, hbetaStart, hbetaEnd, hbetaInt, hbetaAction⟩ :=
    H.exists_contMDiff_family_action_lt hle (le_refl 0) hv hupper hpast
      alpha halpha hint hnode hepsilon
  have hbetaSmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (beta j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    change _ < S + (A - S) / 2 at hbetaAction
    linarith only [hbetaAction, hsmall]
  have hbetaTerminal : beta ⟨H.activeStage t, hle, le_rfl⟩ 0 = p := by
    have hs := hbetaStart ⟨H.activeStage t, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc (le_refl 0) hupperIcc] at hs
    exact hs.trans hterminal
  have hbetaNode (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t) :
      ∃ z : (H.event i).old,
        z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)) ∧
        (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ)) := by
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  intro i hf hl hcanonical
  by_contra hbad
  have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
  rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
  have hlarge := hbarrier H parameters hm hmodelRadius herror hpc hδ hρp records
    hfixed hscalarInitial hderiv t p hball first hle v hv hvE hpast beta hbeta hbetaInt
    (fun j r hr => hscalar j r hr (beta j r)) hbetaTerminal hbetaNode i hf hl hcanonical
    (by simpa only [ho, hn] using hbad)
  exact (not_lt_of_ge hbetaSmall.le) hlarge

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uACInitial

theorem exists_uniform_regularCrossing_at_initial_point_of_sum_stageRegularizedAction_lt_at_controlled_ball
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{uACInitial}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ i : Fin H.eventCount,
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (v : ℝ), 0 ≤ v → v ≤ E →
      ∀ hstart : t.val - v ^ 2 = H.time i.succ,
      let hle : i.succ ≤ H.activeStage t :=
        H.le_activeStage t i.succ (by rw [← hstart]; exact sub_le_self _ (sq_nonneg v))
      (∀ j : H.StageInterval i.succ (H.activeStage t),
        ∀ r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        ∀ x : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x) →
      ∀ alpha : (j : H.StageInterval i.succ (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval i.succ (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A →
      ∃ x : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing x.val (alpha ⟨i.succ, le_rfl, hle⟩ v) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_nonregular_initial_point_at_controlled_ball.{uACInitial}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    i hcanonical t p hball v hv hvE hstart hle hscalar alpha halpha hint hterminal hnode hsmall
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hpast : t.val - v ^ 2 ∈ H.stageDomain i.succ := hstart ▸ H.time_mem_stageDomain i.succ
  let S := ∑ j : H.StageInterval i.succ (H.activeStage t),
    H.stageRegularizedAction j.val t (alpha j)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)
  have hepsilon : 0 < (A - S) / 2 := half_pos (sub_pos.mpr hsmall)
  obtain ⟨beta, hbeta, hbetaStart, hbetaEnd, hbetaInt, hbetaAction⟩ :=
    H.exists_contMDiff_family_action_lt hle (le_refl 0) hv hupper hpast
      alpha halpha hint hnode hepsilon
  have hbetaSmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t (beta j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    change _ < S + (A - S) / 2 at hbetaAction
    linarith only [hbetaAction, hsmall]
  have hbetaTerminal : beta ⟨H.activeStage t, hle, le_rfl⟩ 0 = p := by
    have hs := hbetaStart ⟨H.activeStage t, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc (le_refl 0) hupperIcc] at hs
    exact hs.trans hterminal
  have hbetaInitial : beta ⟨i.succ, le_rfl, hle⟩ v = alpha ⟨i.succ, le_rfl, hle⟩ v := by
    have hs := hbetaEnd ⟨i.succ, le_rfl, hle⟩
    rw [H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast] at hs
    exact hs
  have hbetaNode (j : Fin H.eventCount) (hf : i.succ ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t) :
      ∃ z : (H.event j).old,
        z.val.val = beta ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time j.succ)) ∧
        (H.event j).oldOutput z = beta ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time j.succ)) := by
    obtain ⟨z, hzold, hznew⟩ := hnode j hf hl
    have ho := hbetaStart ⟨j.castSucc, hf, j.castSucc_lt_succ.le.trans hl⟩
    have hn := hbetaEnd ⟨j.succ, hf.trans j.castSucc_lt_succ.le, hl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc j hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hpast j hf] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  by_contra hbad
  have hlarge := hbarrier H parameters hm hmodelRadius herror hpc hδ hρp records
    hfixed hscalarInitial hderiv i hcanonical t p hball v hv hvE hstart beta hbeta hbetaInt
    (fun j r hr => hscalar j r hr (beta j r)) hbetaTerminal hbetaNode
    (by simpa only [hbetaInitial] using hbad)
  exact (not_lt_of_ge hbetaSmall.le) hlarge

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uRegularMin

theorem exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_at_controlled_ball
    (A E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{uRegularMin}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      v ≤ E →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
      0 ≤ v ∧ t.val - v ^ 2 ∈ H.stageDomain first ∧
      ∃ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (gamma j)) volume
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) ∧
        gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
          ∃ z : (H.event i).old,
            z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
              (Real.sqrt (t.val - H.time i.succ)) ∧
            (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
              (Real.sqrt (t.val - H.time i.succ))) ∧
        H.regularizedExtendedAction first (H.activeStage t) t (3 / a₀) 0 v gamma =
          H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q ∧
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
          (H.event i).RegularCrossing
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
              (Real.sqrt (t.val - H.time i.succ)))
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
              (Real.sqrt (t.val - H.time i.succ))) := by
  have hB : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hregular⟩ :=
    exists_uniform_regularCrossing_of_sum_stageRegularizedAction_lt_at_controlled_ball.{uRegularMin}
      A (3 / a₀) E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    t p hball first hle v hvE hcanonical q hcost
  have hfinite : H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q ≠ ⊤ := by
    intro htop
    rw [htop] at hcost
    exact not_lt_of_ge le_top hcost
  have hne : (H.regularizedActionValues first (H.activeStage t) hle t (3 / a₀) 0 v p q).Nonempty := by
    by_contra hn
    exact hfinite (H.regularizedCost_eq_top_of_no_competitor first (H.activeStage t) hle
      t (3 / a₀) 0 v p q (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hv : 0 ≤ v := hvalue.2.1
  have hpast : t.val - v ^ 2 ∈ H.stageDomain first := hvalue.2.2.2.1
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val))
      (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x := by
    have hdomain := H.mapsTo_regularizedStage_Ioo t 0 v j.val hr
    have htime : 0 ≤ t.val - r ^ 2 := (H.stageDomain_subset j.val hdomain).1
    have hratio : 3 / (a₀ + (t.val - r ^ 2)) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hlower : -(3 / a₀) ≤ -3 / (a₀ + (t.val - r ^ 2)) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlower.trans (hpreserve.1 j.val (t.val - r ^ 2) hdomain x).2
  obtain ⟨gamma, hgamma, hint, hrecent, hold, hnode, hmin⟩ :=
    H.exists_regularizedCost_minimizer_of_ne_top first (H.activeStage t) hle
      t (3 / a₀) 0 v hB hupper hscalar p q hfinite
  have hext := H.regularizedExtendedAction_eq_sum_action first (H.activeStage t)
    (le_refl 0) hv hupperIcc hpast gamma hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hsmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (gamma j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    apply WithTop.coe_lt_coe.mp
    rw [← hext, hmin]
    exact hcost
  refine ⟨hv, hpast, gamma, hgamma, hint, hrecent, hold, hnode, hmin, ?_⟩
  intro i hf hl
  exact hregular H parameters hm hmodelRadius herror hpc hδ hρp records
    hfixed hscalarInitial hderiv t p hball first hle v hv hvE hpast hscalar
    gamma hgamma hint hrecent hnode hsmall i hf hl (hcanonical i hf hl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_regularCrossing_of_regularizedCost_lt_at_event_time
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ i : Fin H.eventCount,
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (v : ℝ), v ≤ E →
      ∀ hstart : t.val - v ^ 2 = H.time i.succ,
      let hle : i.succ ≤ H.activeStage t :=
        H.le_activeStage t i.succ (by rw [← hstart]; exact sub_le_self _ (sq_nonneg v))
      (∀ j : H.StageInterval i.succ (H.activeStage t),
        ∀ r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        ∀ x : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x) →
      ∀ q : (H.stage i.succ).Carrier,
        H.regularizedCost i.succ (H.activeStage t) hle t B 0 v p q < (A : WithTop ℝ) →
        ∃ x : (H.event i).incoming.terminalRegularOpen,
          (H.event i).RegularCrossing x.val q := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hcross⟩ :=
    exists_uniform_regularCrossing_at_initial_point_of_sum_stageRegularizedAction_lt_at_controlled_ball.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    i hcanonical t p hball v hvE hstart hle hscalar q hcost
  have hfinite : H.regularizedCost i.succ (H.activeStage t) hle t B 0 v p q ≠ ⊤ := by
    intro htop
    rw [htop] at hcost
    exact not_lt_of_ge le_top hcost
  have hne : (H.regularizedActionValues i.succ (H.activeStage t) hle t B 0 v p q).Nonempty := by
    by_contra hn
    exact hfinite (H.regularizedCost_eq_top_of_no_competitor i.succ (H.activeStage t) hle
      t B 0 v p q (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hv : 0 ≤ v := hvalue.2.1
  have hpast : t.val - v ^ 2 ∈ H.stageDomain i.succ := hstart ▸ H.time_mem_stageDomain i.succ
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  obtain ⟨gamma, hgamma, hint, hrecent, hold, hnode, hmin⟩ :=
    H.exists_regularizedCost_minimizer_of_ne_top i.succ (H.activeStage t) hle t B 0 v hB
      hupper hscalar p q hfinite
  have hext := H.regularizedExtendedAction_eq_sum_action i.succ (H.activeStage t)
    (le_refl 0) hv hupperIcc hpast gamma hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hsmall : (∑ j : H.StageInterval i.succ (H.activeStage t),
      H.stageRegularizedAction j.val t (gamma j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    apply WithTop.coe_lt_coe.mp
    rw [← hext, hmin]
    exact hcost
  obtain ⟨x, hx⟩ := hcross H parameters hm hmodelRadius herror hpc hδ hρp records hfixed
    hscalarInitial hderiv i hcanonical t p hball v hv hvE hstart hscalar
    gamma hgamma hint hrecent hnode hsmall
  exact ⟨x, hold ▸ hx⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_continuousAt_spatial_regularizedCost_at_event
    (A E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ i : Fin H.eventCount,
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (v : ℝ), 0 < v → v ≤ E →
      ∀ hstart : t.val - v ^ 2 = H.time i.succ,
      let hle : i.succ ≤ H.activeStage t :=
        H.le_activeStage t i.succ (by rw [← hstart]; exact sub_le_self _ (sq_nonneg v));
      (∃ q : (H.stage i.succ).Carrier,
        H.regularizedCost i.succ (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ)) →
      ContinuousAt (fun w : ℝ => if w ≤ v then
          sInf (range (H.regularizedCost i.succ (H.activeStage t) hle t (3 / a₀) 0 w p)) else
          sInf (range (H.regularizedCost i.castSucc (H.activeStage t)
            (i.castSucc_le_succ.trans hle) t (3 / a₀) 0 w p))) v := by
  classical
  have hB : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hcross⟩ :=
    exists_uniform_regularCrossing_of_regularizedCost_lt_at_event_time.{u}
      A (3 / a₀) E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    i hcanonical t p hball v hv hvE hstart hle hlow
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hfloor (first : Fin (H.eventCount + 1)) (b : ℝ)
      (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t b j.val))
      (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x := by
    have hdomain := H.mapsTo_regularizedStage_Ioo t 0 b j.val hr
    have htime : 0 ≤ t.val - r ^ 2 := (H.stageDomain_subset j.val hdomain).1
    have hratio : 3 / (a₀ + (t.val - r ^ 2)) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + (t.val - r ^ 2)) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j.val (t.val - r ^ 2) hdomain x).2
  obtain ⟨q₀, hq₀⟩ := hlow
  have hfinite : ∃ q : (H.stage i.succ).Carrier,
      H.regularizedCost i.succ (H.activeStage t) hle t (3 / a₀) 0 v p q ≠ ⊤ := by
    refine ⟨q₀, ?_⟩
    intro heq
    rw [heq] at hq₀
    exact not_lt_of_ge le_top hq₀
  obtain ⟨q, m, gamma, _, _, _, _, _, _, _, hcost, hminimum⟩ :=
    H.exists_regularizedCost_spatial_minimizer i.succ (H.activeStage t) hle t (3 / a₀) 0 v
      hupper (hfloor i.succ v) p hfinite
  have hmA : (m : WithTop ℝ) < (A : WithTop ℝ) := (hminimum q₀).trans_lt hq₀
  obtain ⟨x, hx⟩ := hcross H parameters hm hmodelRadius herror hpc hδ hρp records hfixed
    hscalarInitial hderiv i hcanonical t p hball v hvE hstart (hfloor i.succ v) q
    (by rw [hcost]; exact hmA)
  obtain ⟨z, _, _, hz⟩ := hx
  have heqInf : sInf (range (H.regularizedCost i.succ (H.activeStage t) hle t (3 / a₀) 0 v p)) =
      (m : WithTop ℝ) := by
    apply IsLeast.csInf_eq
    refine ⟨⟨q, hcost⟩, ?_⟩
    rintro y ⟨q', rfl⟩
    exact hminimum q'
  have hleft := H.tendsto_sInf_regularizedCost_left i.succ (H.activeStage t) hle t (3 / a₀) 0 v
    hv hupper (hfloor i.succ v) p hfinite
  have hright := H.tendsto_sInf_regularizedCost_after_event_of_minimum i (H.activeStage t) hle
    (b := v + 1) (by linarith : v < v + 1) hstart hupper (hfloor i.castSucc (v + 1)) p z
    (by rw [hz]; exact hcost) hminimum
  rw [← heqInf] at hright
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · change Tendsto _ (𝓝[<] v) (𝓝 _)
    simpa only [le_refl, ite_true] using hleft.congr' (by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (if_pos (show w ≤ v from le_of_lt hw)).symm)
  · change Tendsto _ (𝓝[>] v) (𝓝 _)
    simpa only [le_refl, ite_true] using hright.congr' (by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (if_neg (show ¬ w ≤ v from not_le_of_gt hw)).symm)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_continuousAt_regularizedSpatialCost
    (A E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      (∀ j : Fin H.eventCount, parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, parameters.neckRadius (H.time j.succ) ≤ ρ) →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j),
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        ((records i).static b).hasCanonicalWindow) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ v : Icc (0 : ℝ) (Real.sqrt t.val), 0 < v.val → v.val ≤ E →
      H.regularizedSpatialCost t (3 / a₀) p v < (A : WithTop ℝ) →
      ContinuousAt (H.regularizedSpatialCost t (3 / a₀) p) v := by
  classical
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hevents⟩ :=
    exists_uniform_continuousAt_spatial_regularizedCost_at_event.{u}
      A E rTerm qDeriv a₀ c ρ Cderiv hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc hδ hρp records hfixed hscalarInitial hderiv
    hcanonical t p hball v hv hvE hlow
  have hphysical (w : Icc (0 : ℝ) (Real.sqrt t.val)) :
      t.val - w.val ^ 2 ∈ Icc 0 H.horizon := by
    have hsq : w.val ^ 2 ≤ t.val := (Real.le_sqrt w.property.1 t.property.1).mp w.property.2
    exact ⟨sub_nonneg.mpr hsq, (sub_le_self _ (sq_nonneg _)).trans t.property.2⟩
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hlowAt (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t)
      (hclock : t.val - v.val ^ 2 ∈ H.stageDomain first) :
      ∃ q : (H.stage first).Carrier,
        H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v.val p q < (A : WithTop ℝ) := by
    have hh := hlow
    rw [H.regularizedSpatialCost_eq_of_mem_stageDomain t (3 / a₀) p v first hle hclock] at hh
    have hne : (range (H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v.val p)).Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty.mp hn, WithTop.sInf_empty] at hh
      exact not_lt_of_ge le_top hh
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := exists_lt_of_csInf_lt hne hh
    exact ⟨q, hq⟩
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hfloor (j : Fin (H.eventCount + 1)) (r : ℝ) (hr : r ∈ H.stageDomain j)
      (x : (H.stage j).Carrier) : -(3 / a₀) ≤ metricScalarAt (H.stageMetric j r) x := by
    have htime := (H.stageDomain_subset j hr).1
    have hratio : 3 / (a₀ + r) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀ (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + r) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve.1 j r hr x).2
  by_cases hvmax : v.val = Real.sqrt t.val
  · have hclock : t.val - v.val ^ 2 ∈ H.stageDomain 0 := by
      rw [hvmax, Real.sq_sqrt t.property.1, sub_self, ← H.time_zero]
      exact H.time_mem_stageDomain 0
    obtain ⟨q, hq⟩ := hlowAt 0 (Fin.zero_le _) hclock
    apply H.continuousAt_regularizedSpatialCost_of_eq_sqrt t (3 / a₀) p v hvmax hfloor
    refine ⟨q, ?_⟩
    intro he
    rw [he] at hq
    exact not_lt_of_ge le_top hq
  have hvT : v.val < Real.sqrt t.val := lt_of_le_of_ne v.property.2 hvmax
  by_cases hevent : ∃ i : Fin H.eventCount, t.val - v.val ^ 2 = H.time i.succ
  · obtain ⟨i, hi⟩ := hevent
    have hle : i.succ ≤ H.activeStage t :=
      H.le_activeStage t i.succ (by rw [← hi]; exact sub_le_self _ (sq_nonneg _))
    have hclock : t.val - v.val ^ 2 ∈ H.stageDomain i.succ := hi ▸ H.time_mem_stageDomain i.succ
    have hcont := hevents H parameters hm hmodelRadius herror hpc hδ hρp records hfixed
      hscalarInitial hderiv i (hcanonical i) t p hball v.val hv hvE hi (hlowAt i.succ hle hclock)
    have hswitch := H.eventually_activeStage_eq_of_backward_clock_event i hv hi
    have heq : H.regularizedSpatialCost t (3 / a₀) p =ᶠ[𝓝 v]
        (fun w : Icc (0 : ℝ) (Real.sqrt t.val) => if w.val ≤ v.val then
          sInf (range (H.regularizedCost i.succ (H.activeStage t) hle t (3 / a₀) 0 w.val p)) else
          sInf (range (H.regularizedCost i.castSucc (H.activeStage t)
            (i.castSucc_le_succ.trans hle) t (3 / a₀) 0 w.val p))) := by
      filter_upwards [continuous_subtype_val.continuousAt.eventually hswitch] with w hw
      have hh := hw (hphysical w)
      split_ifs with hwv
      · apply H.regularizedSpatialCost_eq_of_mem_stageDomain
        apply (H.mem_stageDomain_iff ⟨t.val - w.val ^ 2, hphysical w⟩ i.succ).mpr
        simpa only [if_pos hwv] using hh
      · apply H.regularizedSpatialCost_eq_of_mem_stageDomain
        apply (H.mem_stageDomain_iff ⟨t.val - w.val ^ 2, hphysical w⟩ i.castSucc).mpr
        simpa only [if_neg hwv] using hh
    exact (continuousAt_congr heq).mpr (hcont.comp continuous_subtype_val.continuousAt)
  · let s : Icc (0 : ℝ) H.horizon := ⟨t.val - v.val ^ 2, hphysical v⟩
    let first := H.activeStage s
    have hle : first ≤ H.activeStage t :=
      H.activeStage_mono (by change t.val - v.val ^ 2 ≤ t.val; exact sub_le_self _ (sq_nonneg _))
    have hclock : t.val - v.val ^ 2 ∈ H.stageDomain first := H.activeStage_mem s
    have hstart : H.time first < t.val - v.val ^ 2 := by
      have hbase := H.activeStage_time_le s
      change H.time first ≤ t.val - v.val ^ 2 at hbase
      refine lt_of_le_of_ne hbase ?_
      intro he
      rcases Fin.eq_zero_or_eq_succ first with hf | ⟨i, hf⟩
      · rw [hf, H.time_zero] at he
        have hsq : v.val ^ 2 < t.val := (Real.lt_sqrt v.property.1).mp hvT
        linarith
      · exact hevent ⟨i, by rw [← hf]; exact he.symm⟩
    have hend : t.val - v.val ^ 2 < H.stageEndTime first := by
      rcases Fin.eq_castSucc_or_eq_last first with ⟨i, hi⟩ | hi
      · rw [hi, stageDomain, Fin.lastCases_castSucc] at hclock
        simpa only [hi, H.stageEndTime_castSucc] using hclock.2
      · rw [hi, H.stageEndTime_last]
        exact (sub_lt_self _ (sq_pos_of_pos hv)).trans_le t.property.2
    obtain ⟨q, hq⟩ := hlowAt first hle hclock
    have hfinite : H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v.val p q ≠ ⊤ := by
      intro he
      rw [he] at hq
      exact not_lt_of_ge le_top hq
    have hcont := H.continuousAt_sInf_regularizedCost_of_mem_stage_interior first (H.activeStage t)
      hle t (3 / a₀) 0 v.val hv hupper ⟨hstart, hend⟩ hfloor p ⟨q, hfinite⟩
    have hnear := H.eventually_mem_stageDomain_of_backward_clock_mem_Ioo first ⟨hstart, hend⟩
    have heq : H.regularizedSpatialCost t (3 / a₀) p =ᶠ[𝓝 v]
        (fun w : Icc (0 : ℝ) (Real.sqrt t.val) =>
          sInf (range (H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 w.val p))) := by
      filter_upwards [continuous_subtype_val.continuousAt.eventually hnear] with w hw
      exact H.regularizedSpatialCost_eq_of_mem_stageDomain t (3 / a₀) p w first hle hw
    exact (continuousAt_congr heq).mpr (hcont.comp continuous_subtype_val.continuousAt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
