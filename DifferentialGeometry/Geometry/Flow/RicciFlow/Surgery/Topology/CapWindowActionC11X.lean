import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction

/-!
# CapWindowActionC11X（S-CH11-EXT2，extension of 已跟踪宿主 `Topology/CapWindowAction.lean`）

astra 新增 `exists_uniform_prepared_cap_birth_action_lower_bound_of_`
`parabolicallyRmControlledBall_with_window_scale_bound`
（cap birth action 下界，附带 window scale bound `qWindow * ell ^ 2 ≤ 18`）；旧
`…_of_parabolicallyRmControlledBall` 在 donor 里改写成它的推论。W8 宿主保持不变；本文件逐字抄写
新增定理。直接用户：`CapWindowActionRecentNode`（EXT1 的 port）。
-/

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
theorem exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall_with_window_scale_bound
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
      (∀ (Ppost : OrientedThreeStage.{u}) (gPost : Ppost.Metric)
          (J : standardCapWindow Dbig → Ppost.Carrier),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ qWindow : ℝ, 0 < qWindow →
        (∀ x (V Z : TangentSpace ThreeModel x), w.windowMetric.inner x V Z =
          qWindow * gPost.inner (J x) (mfderiv ThreeModel ThreeModel J x V)
            (mfderiv ThreeModel ThreeModel J x Z)) →
        ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → ∀ ell : ℝ,
          ell ^ 4 * normSq0S gPost (J x) 4 (metricRm04At gPost (J x)) ≤ 1 →
          qWindow * ell ^ 2 ≤ 18) ∧
      (∀ (H : ObservedHistory.{u}) (capFirst : Fin (H.eventCount + 1))
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
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) := by
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
  refine ⟨?_, ?_⟩
  · intro Ppost gPost J hJ qWindow hqWindow hinner x hx ell hRm
    exact hfloor w (hζ.trans (min_le_right _ _)) (by omega : 2 ≤ m)
      gPost J hJ qWindow hqWindow hinner x hx ell hRm
  intro H capFirst t hbirth Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
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
