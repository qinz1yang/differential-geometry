import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen
  ObservedHistory.scaleMetric_restrictOpenOfSubset
  ObservedHistory.comp_inclusion_eq_of_backward_maps ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.exists_curvDerivNorm_bound_of_window
  ObservedHistory.scaled_volume_ball_ge_of_isTracedRegion
  ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.riemannianClosedBallOf_scaleMetric_eq
  ObservedHistory.exists_small_volume_radius from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : MeasurableSpace U :=
  borel U

private local instance {M : Type u} [TopologicalSpace M] (U : Opens M) : BorelSpace U := ⟨rfl⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private def isScaledSurvivorData (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (y : (H.stageAt t).Carrier) (R ρ θ K : ℝ) (hR : 0 < R) (W : Opens (H.stageAt t).Carrier)
    (g : ℝ → SmoothRiemannianMetric ThreeModel W) : Prop :=
  (W : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) y ρ ∧
  (∀ θ' : ℝ, ∀ hθ' : 0 ≤ θ', θ' ≤ θ → IsSolutionOn ({ base.metric := g } :
    SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed (-θ') 0 (neg_nonpos.mpr hθ')))) ∧
  g 0 = (scaleMetric R hR (H.stageMetric (H.activeStage t) t)).restrictOpen W ∧
  (∀ s ∈ Icc (-θ) 0, ∀ x : W, curvDerivNormSq 0 (g s) x ≤ K ^ 2) ∧
  (∀ s ∈ Icc (-θ) 0, (t : ℝ) + s / R ∈ H.stageDomain (H.activeStage t) →
    g s = scaleMetric R hR
      ((H.stageMetric (H.activeStage t) ((t : ℝ) + s / R)).restrictOpen W)) ∧
  ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = t - θ / R ∧
    ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
        (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ j, Function.Injective (f j)) ∧
        (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
            (hl : i.succ ≤ H.activeStage t), ∀ x : W,
          (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
            (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
        (∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
        ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
          (t : ℝ) + s / R ∈ H.stageDomain j.val →
            g s = scaleMetric R hR
              (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))

private theorem exists_isScaledSurvivorData_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ θ K : ℝ} (hR : 0 < R)
    (hθ : 0 < θ) (h : H.isTracedRegion t y ρ (θ / R) (K * R)) :
    ∃ (W : Opens (H.stageAt t).Carrier) (g : ℝ → SmoothRiemannianMetric ThreeModel W),
      H.isScaledSurvivorData t y R ρ θ K hR W g := by
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, hcurrent, -⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t y h
  refine ⟨U, (S.parabolicClosedWindow t R θ hR hθ.le).base.metric, hU, ?_, ?_, ?_, ?_,
    a, hat, ha, f, hf, hinj, hcross, hlast, ?_⟩
  · intro θ' hθ' hle
    have hsub : θ' / R ≤ θ / R := div_le_div_of_nonneg_right hle hR.le
    exact isSolutionOn_parabolicClosedWindow S hS (T := (t : ℝ)) hR hθ'
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩) (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
  · change scaleMetric R hR (S.base.metric ((t : ℝ) + 0 / R)) = _
    rw [zero_div, add_zero, hcurrent t ⟨hat, le_rfl⟩ (H.activeStage_mem t),
      ObservedHistory.scaleMetric_restrictOpen]
  · intro s hs x
    change curvDerivNormSq 0 (scaleMetric R hR (S.base.metric ((t : ℝ) + s / R))) x ≤ K ^ 2
    rw [curvDerivNormSq_scaleMetric]
    have hb : curvDerivNormSq 0 (S.base.metric ((t : ℝ) + s / R)) x ≤ (K * R) ^ 2 :=
      hRm _ (ObservedHistory.mem_Icc_of_mem_window hR ha hs) x
    have hR2 : R⁻¹ ^ (0 + 2) * (K * R) ^ 2 = K ^ 2 := by
      rw [zero_add]
      field_simp
    calc R⁻¹ ^ (0 + 2) * curvDerivNormSq 0 (S.base.metric ((t : ℝ) + s / R)) x
        ≤ R⁻¹ ^ (0 + 2) * (K * R) ^ 2 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K ^ 2 := hR2
  · intro s hs hdom
    change scaleMetric R hR (S.base.metric ((t : ℝ) + s / R)) = _
    rw [hcurrent _ (ObservedHistory.mem_Icc_of_mem_window hR ha hs) hdom]
  · intro s hs j hdom
    change scaleMetric R hR (S.base.metric ((t : ℝ) + s / R)) = _
    rw [hmetric j _ (ObservedHistory.mem_Icc_of_mem_window hR ha hs) hdom]

private theorem trace_normSq_eq_of_index_eq {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (A : BackwardPointTrace K first last hle x) {j k : Fin (K.eventCount + 1)} (hjk : j = k)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) (v : ℝ) :
    normSq0S (K.stageMetric j v) (A.point j hj hjl) 4
      (metricRm04At (K.stageMetric j v) (A.point j hj hjl)) =
    normSq0S (K.stageMetric k v) (A.point k hk hkl) 4
      (metricRm04At (K.stageMetric k v) (A.point k hk hkl)) := by
  subst hjk
  rfl

private theorem pow_four_mul_le_one_of_scaled {r r'' R N : ℝ} (hR : 0 < R) (hr'' : 0 ≤ r'')
    (hle : r'' ≤ r / Real.sqrt R) (hN : 0 ≤ N) (h : r ^ 4 * (R⁻¹ ^ (0 + 2) * N) ≤ 1) :
    r'' ^ 4 * N ≤ 1 := by
  have hs : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have h4 : (r / Real.sqrt R) ^ 4 = r ^ 4 * R⁻¹ ^ 2 := by
    rw [div_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt R), hs, div_eq_mul_inv,
      inv_pow]
  have hpow := pow_le_pow_left₀ hr'' hle 4
  rw [h4] at hpow
  calc r'' ^ 4 * N ≤ r ^ 4 * R⁻¹ ^ 2 * N := mul_le_mul_of_nonneg_right hpow hN
    _ = r ^ 4 * (R⁻¹ ^ (0 + 2) * N) := by ring
    _ ≤ 1 := h

private theorem isParabolicallyRmControlledBall_of_isScaledSurvivorData
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    {R θ : ℝ} (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W}
    (a : Icc (0 : ℝ) H.horizon) (ha : (a : ℝ) = t - θ / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hc : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hp : ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        g s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j)))
    {σ r r'' : ℝ} (hr'' : 0 < r'') (hr''r : r'' ≤ r / Real.sqrt R) (hwin : -θ ≤ σ - r ^ 2)
    (hσ : σ ≤ 0) (vI : Icc (0 : ℝ) H.horizon) (hv : (vI : ℝ) = t + σ / R) (hav : a ≤ vI)
    (hvt : vI ≤ t) (b : Icc (0 : ℝ) H.horizon) (hbv : b ≤ vI) (hb : (b : ℝ) = vI - r'' ^ 2)
    (w : W) (hcurv : ∀ s ∈ Icc (σ - r ^ 2) σ, r ^ 4 * curvDerivNormSq 0 (g s) w ≤ 1) :
    ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage vI) (H.activeStage_mono hbv)
        (f ⟨H.activeStage vI, H.activeStage_mono hav, H.activeStage_mono hvt⟩ w),
      A.isRmControlled (hat := hbv) r'' := by
  have hsR := Real.sqrt_pos.mpr hR
  have hr2 : r'' ^ 2 ≤ r ^ 2 / R := by
    have := pow_le_pow_left₀ hr''.le hr''r 2
    rwa [div_pow, Real.sq_sqrt hR.le] at this
  have hr2R : r'' ^ 2 * R ≤ r ^ 2 := by rwa [le_div_iff₀ hR] at hr2
  have hab0 : (a : ℝ) ≤ vI - r'' ^ 2 := by
    rw [hv, ha]
    have h1 : -θ / R ≤ (σ - r ^ 2) / R := div_le_div_of_nonneg_right hwin hR.le
    have h2 : (σ - r ^ 2) / R = σ / R - r ^ 2 / R := sub_div _ _ _
    rw [neg_div] at h1
    linarith
  have hab : a ≤ b := show (a : ℝ) ≤ b by rw [hb]; exact hab0
  have hab' : H.activeStage a ≤ H.activeStage b := H.activeStage_mono hab
  have hvt' : H.activeStage vI ≤ H.activeStage t := H.activeStage_mono hvt
  let A : BackwardPointTrace H (H.activeStage b) (H.activeStage vI) (H.activeStage_mono hbv)
      (f ⟨H.activeStage vI, H.activeStage_mono hav, hvt'⟩ w) :=
    { point := fun i hi hl => f ⟨i, hab'.trans hi, hl.trans hvt'⟩ w
      endpoint_eq := rfl
      crossing := fun i hi hl => hc i (hab'.trans hi) (hl.trans hvt') w }
  have hslab : ∀ (s : Icc (0 : ℝ) H.horizon) (hbs : b ≤ s) (hsv : s ≤ vI),
      r'' ^ 4 * normSq0S (H.stageMetric (H.activeStage s) s)
        (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hsv)) 4
        (metricRm04At (H.stageMetric (H.activeStage s) s)
          (A.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hsv))) ≤
        1 := by
    intro s hbs hsv
    have hbs' : (vI : ℝ) - r'' ^ 2 ≤ s := hb ▸ hbs
    have hsv' : (s : ℝ) ≤ vI := hsv
    set τ := ((s : ℝ) - t) * R with hτ
    have hts : (t : ℝ) + τ / R = s := by
      rw [hτ]
      field_simp
      ring
    have hτσ : τ ∈ Icc (σ - r ^ 2) σ := by
      have hsvR : ((s : ℝ) - vI) * R ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hR.le
      have hvs : -(r'' ^ 2 * R) ≤ ((s : ℝ) - vI) * R := by nlinarith
      have hvR : ((vI : ℝ) - t) * R = σ := by rw [hv]; field_simp; ring
      have hsplit : τ = ((s : ℝ) - vI) * R + ((vI : ℝ) - t) * R := by rw [hτ]; ring
      constructor <;> linarith
    have hτθ : τ ∈ Icc (-θ) 0 := ⟨by linarith [hτσ.1], by linarith [hτσ.2]⟩
    have hdom : (t : ℝ) + τ / R ∈
        H.stageDomain (⟨H.activeStage s, hab'.trans (H.activeStage_mono hbs),
          (H.activeStage_mono hsv).trans hvt'⟩ :
            H.StageInterval (H.activeStage a) (H.activeStage t)).val := by
      rw [hts]
      exact H.activeStage_mem s
    have hb := hcurv τ hτσ
    rw [hp τ hτθ _ hdom, curvDerivNormSq_scaleMetric, curvDerivNormSq_localPullMetric,
      hts] at hb
    exact pow_four_mul_le_one_of_scaled hR hr''.le hr''r (normSq0S_nonneg _ _ _ _) hb
  refine ⟨A, hslab, ?_⟩
  intro i hf' hl
  have hIoc := (H.crossed_event_iff_mem_Ioc b vI i).mp ⟨hf', hl⟩
  let vT : Icc (0 : ℝ) H.horizon :=
    ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
  have havT : H.activeStage vT = i.succ := H.activeStage_at_time i.succ
  have hbT : b ≤ vT := hIoc.1.le
  have hTv : vT ≤ vI := hIoc.2
  have hb := hslab vT hbT hTv
  rw [trace_normSq_eq_of_index_eq A havT (H.activeStage_mono hbT) (H.activeStage_mono hTv)
    (hf'.trans (Fin.castSucc_lt_succ (i := i)).le) hl] at hb
  have hx := MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.event i)
    (p := ⟨A.point i.castSucc hf' (i.castSucc_lt_succ.le.trans hl),
      (A.crossing i hf' hl).mem_terminalRegularRegion (H.event i)⟩) (A.crossing i hf' hl)
  change r'' ^ 4 * normSq0S (H.event i).terminal.metric _ 4 (metricRm04At _ _) ≤ 1
  rw [hx, H.event_output i, ← H.stageMetric_initial]
  exact hb

private theorem volume_ball_ge_of_isScaledSurvivorData (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ θ K κ ρnc : ℝ}
    (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W} (hd : H.isScaledSurvivorData t y R ρ θ K hR W g)
    (hκ : 0 ≤ κ)
    (hnc : ∀ (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier) (r : ℝ), (v : ℝ) ≤ t →
      r ≤ ρnc → H.isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) p r))
    {σ r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρnc * Real.sqrt R) (hwin : -θ ≤ σ - r ^ 2) (hσ : σ ≤ 0)
    (z : W) (hcpt : IsCompact (riemannianClosedBallOf (g σ) z r))
    (hcurv : ∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (g σ) z r,
      r ^ 4 * curvDerivNormSq 0 (g s) w ≤ 1) :
    ENNReal.ofReal (κ * r ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (g σ) (riemannianBallOf (g σ) z r) := by
  obtain ⟨a, hat, ha, f, hf, hinj, hc, -, hp⟩ := hd.2.2.2.2.2
  have hsR := Real.sqrt_pos.mpr hR
  have hσθ : σ ∈ Icc (-θ) 0 := ⟨by nlinarith, hσ⟩
  have hvI := ObservedHistory.mem_Icc_of_mem_window hR ha hσθ
  let vI : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + σ / R, a.2.1.trans hvI.1, hvI.2.trans t.2.2⟩
  have hav : a ≤ vI := hvI.1
  have hvt : vI ≤ t := hvI.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage vI, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hgσ := hp σ hσθ j (H.activeStage_mem vI)
  set G := H.stageMetric j.val ((t : ℝ) + σ / R) with hG
  set r' := r / Real.sqrt R with hr'
  have hr'0 : 0 < r' := div_pos hr hsR
  have hsr : Real.sqrt R * r' = r := by rw [hr']; field_simp
  have hcpt' : IsCompact (riemannianClosedBallOf (localPullMetric G (f j) (hf j)) z r') := by
    rw [hgσ, ObservedHistory.riemannianClosedBallOf_scaleMetric_eq] at hcpt
    exact hcpt
  have hball' : riemannianBallOf (g σ) z r =
      riemannianBallOf (localPullMetric G (f j) (hf j)) z r' := by
    rw [hgσ, ObservedHistory.riemannianBallOf_scaleMetric_eq]
  have hsmall : ∀ r'' ∈ Ioo 0 r', ENNReal.ofReal (κ * r'' ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (localPullMetric G (f j) (hf j))
        (riemannianBallOf (localPullMetric G (f j) (hf j)) z r') := by
    intro r'' hr''
    have himg := Geometry.Metric.image_riemannianBallOf_localPullMetric G (f j) (hf j) (hinj j) z
      hr''.1 hr''.2 hcpt'
    have hmeas : MeasurableSet (riemannianBallOf (localPullMetric G (f j) (hf j)) z r'') :=
      (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ z)
        continuous_const).measurableSet
    have hveq := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      (localPullMetric G (f j) (hf j)) G (f j) (hf j) (hinj j)
      (fun x v w => localPullMetric_inner G (f j) (hf j) x v w) hmeas
    rw [himg] at hveq
    have hpc : H.isParabolicallyRmControlledBall vI (f j z) r'' := by
      have hb0 : (a : ℝ) ≤ vI - r'' ^ 2 := by
        have h2 : r'' ^ 2 ≤ r ^ 2 / R := by
          have := pow_le_pow_left₀ hr''.1.le hr''.2.le 2
          rwa [hr', div_pow, Real.sq_sqrt hR.le] at this
        change (a : ℝ) ≤ (t : ℝ) + σ / R - r'' ^ 2
        rw [ha]
        have h1 : -θ / R ≤ (σ - r ^ 2) / R := div_le_div_of_nonneg_right hwin hR.le
        rw [neg_div, sub_div] at h1
        linarith
      let b : Icc (0 : ℝ) H.horizon :=
        ⟨vI - r'' ^ 2, a.2.1.trans hb0, by linarith [vI.2.2, sq_nonneg r'']⟩
      have hbv : b ≤ vI := show (vI : ℝ) - r'' ^ 2 ≤ vI by linarith [sq_nonneg r'']
      refine ⟨hr''.1, b, hbv, rfl, fun x hx => ?_⟩
      have hx' : x ∈ f j '' riemannianBallOf (localPullMetric G (f j) (hf j)) z r'' := by
        rw [himg]
        exact hx
      obtain ⟨w, hw, rfl⟩ := hx'
      exact H.isParabolicallyRmControlledBall_of_isScaledSurvivorData t hR a ha f hf hc hp hr''.1
        hr''.2.le hwin hσ vI rfl hav hvt b hbv rfl w (fun s hs => hcurv s hs w (by
          rw [hball']
          exact riemannianBallOf_mono _ _ hr''.2.le hw))
    have hv := hnc vI (f j z) r'' hvt (hr''.2.le.trans (by
      rw [hr', div_le_iff₀ hsR]
      exact hrρ)) hpc
    rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hr''.1.le]
    refine hv.trans ?_
    rw [← hveq]
    exact MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hr''.2.le)
  have hlim : ENNReal.ofReal (κ * r' ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (localPullMetric G (f j) (hf j))
        (riemannianBallOf (localPullMetric G (f j) (hf j)) z r') := by
    have htend : Tendsto (fun x : ℝ => ENNReal.ofReal (κ * x ^ 3)) (𝓝[<] r')
        (𝓝 (ENNReal.ofReal (κ * r' ^ 3))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 3))).tendsto
        r').mono_left nhdsWithin_le_nhds
    exact le_of_tendsto htend (Filter.mem_of_superset (Ioo_mem_nhdsLT hr'0) hsmall)
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hiff := (Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (localPullMetric G (f j) (hf j)) R hR z r' (ENNReal.ofReal κ)).2 (by
      rw [hfin, ← ENNReal.ofReal_pow hr'0.le, ← ENNReal.ofReal_mul hκ]
      exact hlim)
  rw [hsr, hfin, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hκ] at hiff
  rw [hgσ]
  exact hiff

theorem exists_ancient_pointed_flow_limit_with_survivor_maps_of_isTracedRegion
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) ≤ t n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
        (∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - 2 * ((k + 2 : ℕ) : ℝ) / R n ∧
          ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
              W k n → ((H n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
                ((H n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                        (hf j))) ∧
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j),
                IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ G : ℝ → SmoothRiemannianMetric ThreeModel P.M,
                G 0 = P.metric ∧
                IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                  (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
  intro X
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  choose K hK0 hKev using fun k : ℕ => htraced ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
    (by positivity) (hθ k)
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n) →
        (H n).isScaledSurvivorData (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        (H n).exists_isScaledSurvivorData_of_isTracedRegion (t n) (y n) (hR n) (hθ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      (H n).isScaledSurvivorData (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : (H n).isScaledSurvivorData (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n) _ _).symm
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  have hsubW (k n : ℕ) (hn : (H n).isScaledSurvivorData (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) ⊆
        W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by push_cast; linarith))
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact (riemannianClosedBallOf_mono _ _ (by push_cast; linarith)).trans (hsubW k n hn)
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _)
      (by have := (Nat.cast_nonneg (k + 2) : (0 : ℝ) ≤ _); linarith)
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    obtain ⟨B, hB0, hB⟩ := ObservedHistory.exists_curvDerivNorm_bound_of_window (hθ k) (K := K k)
    refine ⟨B m, hB0 m, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) x 1) := by
      rw [hn.2.2.1]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      refine (riemannianClosedBallOf_subset_of_add_radius_le _ (Nat.cast_nonneg _) zero_le_one
        ?_ hx).trans (hsubW k n hn)
      push_cast
      linarith
    refine hB (h k n) (hn.2.1 _ (hθ k).le le_rfl) hn.2.2.2.1 x hcpt m s ⟨?_, hs.2⟩
    have := hs.1
    push_cast at this ⊢
    linarith
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hs
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, -, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, -, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hkl := min_le_left (k : ℝ) (l : ℝ)
    have hlk := min_le_right (k : ℝ) (l : ℝ)
    have hs1 := hs.1
    push_cast at hs1
    have hsk : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hsl : s ∈ Icc (-(2 * ((l + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hv₁ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₁ hsk
    have hv₂ := ObservedHistory.mem_Icc_of_mem_window (hR n) ha₂ hsl
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + s / R n, a₁.2.1.trans hv₁.1, hv₁.2.trans (t n).2.2⟩
    have hja₁ : (H n).activeStage a₁ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₁ ≤ v from hv₁.1)
    have hja₂ : (H n).activeStage a₂ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₂ ≤ v from hv₂.1)
    have hjt : (H n).activeStage v ≤ (H n).activeStage (t n) :=
      (H n).activeStage_mono (show v ≤ t n from hv₁.2)
    have hdom := (H n).activeStage_mem v
    rw [hp₁ s hsk ⟨_, hja₁, hjt⟩ hdom, hp₂ s hsl ⟨_, hja₂, hjt⟩ hdom,
      ObservedHistory.scaleMetric_restrictOpenOfSubset,
      ObservedHistory.scaleMetric_restrictOpenOfSubset]
    congr 1
    exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
      (ObservedHistory.comp_inclusion_eq_of_backward_maps (H n) hat₁ hat₂ f₁ hc₁ hl₁ f₂ hc₂ hl₂ _
        hja₁ hja₂
        hjt)
  have hvolX : ∀ r R' : ℝ, 0 < r → r < R' → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ' * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    intro r R' hr hrR' C hC
    obtain ⟨K', hK'0, hK'ev⟩ := htraced (r + 1) 1 (by linarith) one_pos
    obtain ⟨a, ha0, ha1, hra, haC, haK⟩ := ObservedHistory.exists_small_volume_radius hrR' hC hK'0
    refine ⟨a, κ, ha0, hκ, hra, haC, ?_⟩
    filter_upwards [hK'ev, hRlim.eventually_ge_atTop ((a / ρ) ^ 2)] with n htr hRn x hx
    have haρ : a / Real.sqrt (R n) ≤ ρ := by
      have hsq : a / ρ ≤ Real.sqrt (R n) := Real.le_sqrt_of_sq_le hRn
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (hR n))]
      rw [div_le_iff₀ hρ] at hsq
      linarith
    exact ObservedHistory.scaled_volume_ball_ge_of_isTracedRegion (H n) (t n) (y n) (hR n) hr.le
      ha0 ha1 hK'0 haK hκ.le haρ htr (fun p r hr hpc => hnc n (t n) p r le_rfl hr hpc) x hx
  refine ⟨W, h, fun k => ?_, exists_ancient_pointed_flow_limit_of_local_solutions X hcompact
    hvolX W h hball hsol hzero hjets hcompat⟩
  filter_upwards [hsurv k] with n hn
  refine ⟨hWset k n hn, hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith),
    fun s hs hdom => hn.2.2.2.2.1 s ⟨?_, hs.2⟩ hdom, hn.2.2.2.2.2, ?_⟩
  · have := hs.1
    push_cast at this ⊢
    linarith
  intro σ hσ z r hr hrρ hsub hcpt hcurv
  have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
  refine volume_ball_ge_of_isScaledSurvivorData (H n) (t n) (y n) (hR n) hn hκ.le (hnc n) hr
    hrρ ?_ hσ.2 z hcpt hcurv
  push_cast at hlow ⊢
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
