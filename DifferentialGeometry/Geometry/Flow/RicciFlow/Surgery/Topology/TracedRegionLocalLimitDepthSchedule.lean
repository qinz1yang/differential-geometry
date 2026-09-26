import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalPointedFlowLimit

/-!
# Local pointed flow limits of traced regions on a depth schedule

For a blow-up sequence of observed histories whose traced regions of radius `k + 3` reach back
to the rescaled depth `τ k`, the rescaled survivor flows subconverge to a pointed limit carrying,
over each ball `B((k + 1) / 2)`, a local Ricci flow on the inner window
`[-(k + 1) / (k + 2) · τ k, 0]`. The approximants keep their survivor maps, time-Lipschitz
control, scalar bounds, metric comparison and the windowed parabolic `κ`-test.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.isScaledSurvivorData
  ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.scaleMetric_restrictOpenOfSubset
  ObservedHistory.comp_inclusion_eq_of_backward_maps ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.exists_small_volume_radius from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

open private ObservedHistory.metricScalarAt_le_of_curvDerivNormSq_zero_le
  ObservedHistory.riemannianVolumeMeasure_restrictOpen_le
  ObservedHistory.volume_ball_ge_of_isScaledSurvivorData_of_admissible from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitTimeControl

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn
  (neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt)

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

private theorem volume_ball_ge_of_isScaledSurvivorData_at_depth (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ θ K κ ρnc : ℝ}
    (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W}
    (hd : ObservedHistory.isScaledSurvivorData H t y R ρ θ K hR W g)
    (hκ : 0 < κ) {A : ℝ → Prop}
    (hnc : ∀ (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier) (r : ℝ), (v : ℝ) ≤ t →
      A v → r ≤ ρnc → H.isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) p r))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haθ : a ^ 2 ≤ θ) (haK : a ^ 2 * K ≤ 1) (hK : 0 ≤ K)
    (haρ : a ≤ ρnc * Real.sqrt R) (hA : A ((t : ℝ) + -(a ^ 2 / 4) / R)) (x : W)
    (hcpt : IsCompact (riemannianClosedBallOf (g 0) x 25)) :
    ENNReal.ofReal (κ * (Real.exp (-(9 / 4)) * (1 / 2)) ^ 3 * Real.exp (-(27 / 4)) * a ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (g 0) (riemannianBallOf (g 0) x a) := by
  have hθ0 : 0 ≤ θ := (sq_nonneg a).trans haθ
  let D := RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ0)
  let S : SolutionOn (I := ThreeModel) (M := W) D := { base.metric := g }
  have hS : IsSolutionOn S := hd.2.1 θ hθ0 le_rfl
  have hreg : interior D.carrier ⊆ D.regular := by
    change interior (Icc (-θ) 0) ⊆ Ioo (-θ) 0
    rw [interior_Icc]
  have hrm : ∀ s ∈ Icc (-θ) 0, ∀ w : W, Perelman.FlowMetricBall.rmNormSq S s w ≤ K ^ 2 := by
    intro s hs w
    have hsq := curvNormSq_eq S 0 s w
    simp only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] at hsq
    change normSq0S (S.base.metric s) w 4 (S.base.rm04 s w) ≤ K ^ 2
    rw [← hsq]
    exact hd.2.2.2.1 s hs w
  have ha4 : ∀ r' : ℝ, 0 < r' → r' ≤ a → ∀ c : ℝ, 0 ≤ c → c ≤ K ^ 2 → r' ^ 4 * c ≤ 1 := by
    intro r' hr' hra c hc hcK
    have h1 : r' ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ hr'.le hra 4
    have h2 : a ^ 4 * K ^ 2 ≤ 1 := by
      have : (a ^ 2 * K) ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg a) hK]
      nlinarith
    nlinarith [mul_le_mul h1 hcK hc (by positivity)]
  let T : D.FlowTime := ⟨0, ⟨by linarith, le_rfl⟩⟩
  let B : Perelman.FlowMetricBall S T := ⟨x, a, ha⟩
  have hwinB : Icc ((T : ℝ) - B.radius ^ 2) (T : ℝ) ⊆ Icc (-θ) 0 := by
    intro s hs
    change s ∈ Icc (0 - a ^ 2) 0 at hs
    exact ⟨by nlinarith [hs.1], hs.2⟩
  have hB : B.IsParabolicallyRmControlled := ⟨hwinB, fun s hs w _ =>
    ha4 a ha le_rfl _ (normSq0S_nonneg _ _ _ _) (hrm s (hwinB hs) w)⟩
  have hlt : ∀ (t' : D.FlowTime) (B' : Perelman.FlowMetricBall S t'),
      (t' : ℝ) = (T : ℝ) - B.radius ^ 2 * (1 / 2) ^ 2 → B'.center = B.center →
      B'.radius ≤ B.radius → B'.IsParabolicallyRmControlled → B'.IsKappaNoncollapsed κ := by
    intro t' B' ht' hc hrad hB'
    have hr' := B'.radius_pos
    have hra : B'.radius ≤ a := hrad
    have ht'' : (t' : ℝ) = -(a ^ 2 / 4) := by rw [ht']; change 0 - a ^ 2 * (1 / 2) ^ 2 = _; ring
    have hwin' := hB'.1
    have hlo : -θ ≤ (t' : ℝ) - B'.radius ^ 2 := (hwin' ⟨le_rfl, by nlinarith⟩).1
    have ht'0 : (t' : ℝ) ≤ 0 := t'.2.2
    have htθ : -θ ≤ (t' : ℝ) := by rw [ht'']; nlinarith
    have hct : 0 < Real.exp (-(9 / 4)) := Real.exp_pos _
    have hbound : ∀ w : W, riemannianEDistOf (g 0) x w ≤ ENNReal.ofReal (B'.radius / Real.exp
        (-(9 / 4)) + 1) → ∀ v : TangentSpace ThreeModel w,
        Real.exp (-(9 / 4)) ^ 2 * (g 0).inner w v v ≤ (g (t' : ℝ)).inner w v v := by
      intro w _ v
      have hcmp := Perelman.inner_le_exp_mul_inner_of_rmNormSq_le hS ha
        (T := (t' : ℝ)) (t := 0) (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
        (fun s hs => ⟨by linarith [hs.1], hs.2⟩)
        (fun u hu => ha4 a ha le_rfl _ (normSq0S_nonneg _ _ _ _)
          (hrm u ⟨by linarith [hu.1], hu.2⟩ w))
        (s₁ := 0) (s₂ := (t' : ℝ)) ⟨by linarith, le_rfl⟩ ⟨le_rfl, ht'0⟩ v
      have hexp : 2 * ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / a ^ 2 * |0 - (t' : ℝ)|) =
          9 / 2 := by
        rw [ht'', show (0 : ℝ) - -(a ^ 2 / 4) = a ^ 2 / 4 by ring, abs_of_pos (by positivity)]
        have hfin : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
        rw [hfin]
        field_simp
        norm_num
      rw [hexp] at hcmp
      have he : Real.exp (-(9 / 4)) ^ 2 * Real.exp (9 / 2) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        norm_num
      have hn0 := metric_inner_self_nonneg (g (t' : ℝ)) w v
      calc Real.exp (-(9 / 4)) ^ 2 * (g 0).inner w v v
          ≤ Real.exp (-(9 / 4)) ^ 2 * (Real.exp (9 / 2) * (g (t' : ℝ)).inner w v v) :=
            mul_le_mul_of_nonneg_left hcmp (by positivity)
        _ = (g (t' : ℝ)).inner w v v := by rw [← mul_assoc, he, one_mul]
    have hcpt' : IsCompact (riemannianClosedBallOf (g (t' : ℝ)) x B'.radius) := by
      refine hcpt.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) ?_
      intro w hw
      have hw' : riemannianEDistOf (g (t' : ℝ)) x w ≤ ENNReal.ofReal B'.radius := hw
      have hne : riemannianEDistOf (g (t' : ℝ)) x w ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw'
      have hlt' : riemannianEDistOf (g (t' : ℝ)) x w <
          ENNReal.ofReal (Real.exp (-(9 / 4)) * (B'.radius / Real.exp (-(9 / 4)) + 1)) := by
        refine lt_of_le_of_lt hw' ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
        rw [mul_add, mul_div_cancel₀ _ hct.ne', mul_one]
        linarith
      have hd0 := Geometry.Riemannian.riemannianEDistOf_le_of_metric_lower_on_ball (g 0)
        (g (t' : ℝ)) x w hct hbound hlt'
      have htr : (riemannianEDistOf (g (t' : ℝ)) x w).toReal ≤ B'.radius :=
        ENNReal.toReal_le_of_le_ofReal hr'.le hw'
      have he3 : Real.exp (9 / 4) ≤ 25 := by
        have h1 : Real.exp (9 / 4) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
        have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have h3 := Real.exp_one_lt_d9
        have h4 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 :=
          pow_lt_pow_left₀ h3 (Real.exp_pos 1).le (by norm_num)
        nlinarith
      have hdiv : (riemannianEDistOf (g (t' : ℝ)) x w).toReal / Real.exp (-(9 / 4)) ≤ 25 := by
        rw [div_le_iff₀ hct]
        have hinv : Real.exp (-(9 / 4)) * Real.exp (9 / 4) = 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (9 / 4), mul_le_mul_of_nonneg_left he3 hct.le]
      exact hd0.trans (ENNReal.ofReal_le_ofReal hdiv)
    have hcurv' : ∀ s ∈ Icc ((t' : ℝ) - B'.radius ^ 2) (t' : ℝ),
        ∀ w ∈ riemannianBallOf (g (t' : ℝ)) x B'.radius,
          B'.radius ^ 4 * curvDerivNormSq 0 (g s) w ≤ 1 := by
      intro s hs w _
      exact ha4 B'.radius hr' hra _ (normSq0S_nonneg _ _ _ _)
        (hd.2.2.2.1 s ⟨by linarith [hs.1], hs.2.trans ht'0⟩ w)
    have hv := ObservedHistory.volume_ball_ge_of_isScaledSurvivorData_of_admissible H t y hR hd
      hκ.le hnc hr' (hra.trans haρ) hlo ht'0 (by rw [ht'']; exact hA) x hcpt' hcurv'
    refine ⟨hκ, ?_⟩
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hfin, ← ENNReal.ofReal_pow hr'.le, ← ENNReal.ofReal_mul hκ.le]
    change _ ≤ Integral.Measure.riemannianVolumeMeasure ThreeModel W (g (t' : ℝ))
      (riemannianBallOf (g (t' : ℝ)) B'.center B'.radius)
    rw [hc]
    exact hv
  obtain ⟨-, hvol⟩ := Perelman.FlowMetricBall.volume_ge_of_isKappaNoncollapsed_at_earlier_time hS
    hreg (by norm_num) le_rfl B hB hlt
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have heq : κ * (Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / B.radius ^ 2 *
      (B.radius ^ 2 * (1 / 2) ^ 2))) * (B.radius * (1 - 1 / 2))) ^ Module.finrank ℝ ThreeSpace *
      Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 3 / B.radius ^ 2 *
        (B.radius ^ 2 * (1 / 2) ^ 2))) =
      κ * (Real.exp (-(9 / 4)) * (1 / 2)) ^ 3 * Real.exp (-(27 / 4)) * a ^ 3 := by
    change κ * (Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / a ^ 2 *
      (a ^ 2 * (1 / 2) ^ 2))) * (a * (1 - 1 / 2))) ^ Module.finrank ℝ ThreeSpace *
      Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 3 / a ^ 2 * (a ^ 2 * (1 / 2) ^ 2))) = _
    have ha2 : a ^ 2 ≠ 0 := by positivity
    have e1 : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / a ^ 2 * (a ^ 2 * (1 / 2) ^ 2) = 9 / 4 := by
      rw [hfin]; field_simp; norm_num
    have e2 : (Module.finrank ℝ ThreeSpace : ℝ) ^ 3 / a ^ 2 * (a ^ 2 * (1 / 2) ^ 2) = 27 / 4 := by
      rw [hfin]; field_simp; norm_num
    rw [e1, e2, hfin]
    ring
  rw [heq] at hvol
  exact hvol

private theorem exists_curvDerivNorm_bound_of_inner_window {θ c K r₀ : ℝ} (hc : 0 < c)
    (hcθ : c < θ) (hr₀ : 0 < r₀) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : ℝ → SmoothRiemannianMetric ThreeModel M),
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := M)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr (hc.trans hcθ).le))) →
        (∀ s ∈ Icc (-θ) 0, ∀ x : M, curvDerivNormSq 0 (g s) x ≤ K ^ 2) →
        (∀ s ∈ Icc (-c) 0, ∀ (x : M) (u : TangentSpace ThreeModel x),
          (g 0).inner x u u ≤ Real.exp 2 * (g s).inner x u u) →
        ∀ p : M, IsCompact (riemannianClosedBallOf (g 0) p r₀) →
        ∀ m : ℕ, ∀ s ∈ Icc (-c) 0, curvDerivNorm m (g s) p ≤ B m := by
  have hK' : 0 < |K| + 1 := by positivity
  have hδ : 0 < θ - c := by linarith
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  refine ⟨fun m => shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m
      ((|K| + 1) * ((θ - c) / 4))
      ((r₀ * Real.exp (-1) / (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) *
        (θ - c)))) * Real.sqrt (|K| + 1) /
        (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) * ((θ - c) / 4)))) *
      (|K| + 1) / Real.sqrt ((θ - c) / 4) ^ m, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK'.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  intro M _ _ _ _ _ g hsol hcurv hlow p hcompact m s hs
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace ThreeModel M
  have hKK : K ^ 2 ≤ (|K| + 1) ^ 2 := by
    rw [← sq_abs K]
    exact pow_le_pow_left₀ (abs_nonneg K) (by linarith) 2
  have hbd : ∀ y : M, riemannianEDistOf (g 0) p y ≤ ENNReal.ofReal (2 * r₀) →
      ∀ v : TangentSpace ThreeModel y,
        Real.exp (-1) ^ 2 * (g 0).inner y v v ≤ (g s).inner y v v := by
    intro y _ v
    have h1 := hlow s hs y v
    have h2 : Real.exp (-1) ^ 2 * Real.exp 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    calc Real.exp (-1) ^ 2 * (g 0).inner y v v
        ≤ Real.exp (-1) ^ 2 * (Real.exp 2 * (g s).inner y v v) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (g s).inner y v v := by rw [← mul_assoc, h2, one_mul]
  have hsub : riemannianClosedBallOf (g s) p (r₀ * Real.exp (-1)) ⊆
      riemannianClosedBallOf (g 0) p r₀ := by
    intro w hw
    have hw' : riemannianEDistOf (g s) p w ≤ ENNReal.ofReal (r₀ * Real.exp (-1)) := hw
    have hlt : riemannianEDistOf (g s) p w < ENNReal.ofReal (Real.exp (-1) * (2 * r₀)) :=
      lt_of_le_of_lt hw' ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith))
    have hd := Geometry.Riemannian.riemannianEDistOf_le_of_metric_lower_on_ball (g 0) (g s) p w
      he hbd hlt
    have htr : (riemannianEDistOf (g s) p w).toReal ≤ r₀ * Real.exp (-1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hw'
    refine hd.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ he]
    exact htr
  have hcpt : IsCompact (riemannianClosedBallOf (g s) p (r₀ * Real.exp (-1))) :=
    hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hsub
  have key := shi_curvDerivNorm_on_terminal_ball ({ base.metric := g } :
      SolutionOn (I := ThreeModel) (M := M)
        (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr (hc.trans hcθ).le))) hsol
    (a := s - (θ - c)) (b := s) (by linarith) hK' (by positivity)
    (fun v hv => ⟨by linarith [hv.1, hs.1], hv.2.trans hs.2⟩)
    (fun v hv => ⟨by linarith [hv.1, hs.1], hv.2.trans_le hs.2⟩) p hcpt
    (fun v hv z _ => (hcurv v ⟨by linarith [hv.1, hs.1], hv.2.trans hs.2⟩ z).trans hKK) m s
    ⟨by linarith, le_rfl⟩ p
    (by rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]; exact bot_le)
  have hab : s - (s - (θ - c)) = θ - c := by ring
  simp only [hab] at key
  exact key

theorem exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
        (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    {t₀ : ℕ → ℝ} (hsliver : Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0))
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
      ∀ x : ((H n).stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) :
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
          (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) ∧
        (∀ s ∈ Icc (-τ k) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
        (∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
          (a : ℝ) = t n - τ k / R n ∧
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
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                  (t n : ℝ) + s / R n ∈ (H n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / R n)) (f j)
                        (hf j))) ∧
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
          (t n : ℝ) + σ / R n < t₀ n → ∀ z : W k n, ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop,
        ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
        ∀ σ' ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ z : W k n,
          (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
        ∀ (x : W k n) (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n s) x (metricAlgebraicCurvatureTensorAt (h k n s) x)
          (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n s) x))) ∧
      (∀ k : ℕ, ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, σ < 0 →
        ∀ᶠ n in atTop, ∀ z : W k n, ∀ r : ℝ, 0 < r → r ≤ ρ * Real.sqrt (R n) →
          Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
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
              ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k),
                (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
                (∀ k, IsSolutionOn ({ base.metric := Gloc k } :
                  SolutionOn (I := ThreeModel) (M := V k)
                    (RealTimeInterval.closed (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0
                      (neg_nonpos.mpr (mul_pos (by positivity) (hτ k)).le)))) ∧
                (∀ k l, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
                  s ∈ Icc (-(((l + 1 : ℕ) : ℝ) / ((l + 2 : ℕ) : ℝ) * τ l)) 0 →
                  (Gloc k s).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
                    (Gloc l s).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          (Gloc k s) (P.metric.restrictOpen (V k)) < η := by
  intro X
  have hβ0 (k : ℕ) : 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by positivity
  have hβ1 (k : ℕ) : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast
    linarith
  have hc (k : ℕ) : 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k := mul_pos (hβ0 k) (hτ k)
  have hcτ (k : ℕ) : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k < τ k := by
    have := hτ k
    nlinarith [hβ1 k]
  have hA : ∀ s : ℝ, s < 0 → ∀ᶠ n in atTop, (t n : ℝ) + s / R n < t₀ n := by
    intro s hs
    filter_upwards [hsliver.eventually (gt_mem_nhds (show (0 : ℝ) < -s by linarith))] with n hn
    have h1 : t n - t₀ n < -s / R n := by
      rw [lt_div_iff₀ (hR n)]
      linarith
    have h2 : s / R n = -(-s / R n) := by ring
    linarith
  have hnc' (n : ℕ) : ∀ (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) ≤ t n → (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r) :=
    fun v p r _ hv hr hpc => hnc n v p r hv hr hpc
  choose K hK0 hKev using htraced
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
          (K k * R n) →
        ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k) (K k) (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (τ k / R n) (K k * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion (H n) (t n) (y n) (hR n)
          (hτ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k) (K k) (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k) (K k) (hR n) (W k n) (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n) _ _).symm
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  have hsubW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k) (K k) (hR n) (W k n) (h k n)) {r : ℝ}
      (hr : r < ((k + 3 : ℕ) : ℝ)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r ⊆ W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hr)
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hsubW k n hn (by push_cast; linarith)
  have hsolτ : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 (τ k) (hτ k).le le_rfl
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  have hcptW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k) (K k) (hR n) (W k n) (h k n)) (x : W k n)
      {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr0 : 0 ≤ r) (hx : (x : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r)
      (hr : r + r₀ < ((k + 3 : ℕ) : ℝ)) :
      IsCompact (riemannianClosedBallOf (h k n 0) x r₀) := by
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    rw [hn.2.2.1]
    apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
    exact (riemannianClosedBallOf_subset_of_add_radius_le _ hr0 hr₀ le_rfl hx).trans
      (hsubW k n hn hr)
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-τ k) 0,
      ∀ x : W k n, curvatureOperatorLowerBoundAt (h k n q) x
        (metricAlgebraicCurvatureTensorAt (h k n q) x)
        (Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) := by
    intro k
    filter_upwards [hsurv k] with n hn q hqθ x
    obtain ⟨a, -, ha, f, hf, -, -, -, hp⟩ := hn.2.2.2.2.2
    have hv := ObservedHistory.mem_Icc_of_mem_window (hR n) ha hqθ
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + q / R n, a.2.1.trans hv.1, hv.2.trans (t n).2.2⟩
    let j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)) :=
      ⟨(H n).activeStage v, (H n).activeStage_mono (show a ≤ v from hv.1),
        (H n).activeStage_mono (show v ≤ t n from hv.2)⟩
    have hq' := hp q hqθ j ((H n).activeStage_mem v)
    have hpull := (curvatureOperatorLowerBoundAt_localPullMetric_iff _ (f j) (hf j) x _).mpr
      (hpinch n v hv.2 (f j x))
    rw [hq', curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
      metricScalarAt_localPull]
    unfold Perelman.rescalePinchingFunction
    simp only [mul_inv_cancel_left₀ (hR n).ne']
    exact hpull
  have hlowW : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
      (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u := by
    intro k
    set c := ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k with hcdef
    have hc0 : 0 < c := hc k
    filter_upwards [hsurv k, Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto hPhi
      hRlim ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|) (1 / (2 * c))
      (one_div_pos.mpr (by linarith)), hpinchW k] with n hn hδ hpw s hs x u
    have hsk : -τ k < s := lt_of_lt_of_le (neg_lt_neg (hcτ k)) hs.1
    let S : SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le)) :=
      { base.metric := h k n }
    have hS : IsSolutionOn S := hn.2.1 (τ k) (hτ k).le le_rfl
    have hRic : ∀ q ∈ Ioo s 0, -(1 / c) * (S.base.metric q).inner x u u ≤
        S.ricciAt q x (vec2 u u) := by
      intro q hq
      have hqθ : q ∈ Icc (-τ k) 0 := ⟨by linarith [hq.1], hq.2.le⟩
      have hscal := hpw q hqθ x
      have hric := neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt
        (h k n q) x hscal u
      have hle := hδ _ (ObservedHistory.metricScalarAt_le_of_curvDerivNormSq_zero_le (h k n q) x
        (hn.2.2.2.1 q hqθ x))
      have hn0 := metric_inner_self_nonneg (h k n q) x u
      have hδeq : 2 * (1 / (2 * c)) = 1 / c := by
        field_simp
      change -(1 / c) * (h k n q).inner x u u ≤ metricRicciAt (h k n q) x (vec2 u u)
      have hmono : -(1 / c) * (h k n q).inner x u u ≤
          -(2 * Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) *
            (h k n q).inner x u u := by
        rw [← hδeq]
        exact mul_le_mul_of_nonneg_right (by linarith) hn0
      exact hmono.trans hric
    have hB2 := metric_inner_le_exp_mul_of_ricci_lower_bound S hS hs.2
      (fun r hr => ⟨by linarith [hr.1], hr.2⟩) (fun r hr => ⟨by linarith [hr.1], hr.2⟩) x u hRic
    refine hB2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
      (metric_inner_self_nonneg _ _ _))
    have hs1 : -s ≤ c := by linarith [hs.1]
    rw [show 2 * (1 / c) * (0 - s) = 2 * (-s / c) by ring]
    have : -s / c ≤ 1 := (div_le_one hc0).mpr hs1
    linarith
  have hjetsB (k : ℕ) := exists_curvDerivNorm_bound_of_inner_window (K := K k) (hc k) (hcτ k)
    (by norm_num : (0 : ℝ) < 1 / 2)
  choose Bj hBj0 hBj using hjetsB
  have hjetsAt (k : ℕ) : ∀ᶠ n in atTop, ∀ m : ℕ,
      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (((k + 2 : ℕ) : ℝ) + 1 / 4) →
        curvDerivNorm m (h k n s) x ≤ Bj k m := by
    filter_upwards [hsurv k, hlowW k] with n hn hlow m s hs x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    exact hBj k (h k n) (hn.2.1 (τ k) (hτ k).le le_rfl) (hn.2.2.2.1) hlow x
      (hcptW k n hn x (by norm_num) (by positivity) hx (by push_cast; linarith)) m s hs
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    refine ⟨Bj k m, hBj0 k m, ?_⟩
    filter_upwards [hjetsAt k] with n hn s hs x hx
    exact hn m s hs x (riemannianClosedBallOf_mono _ _ (by push_cast; linarith) hx)
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
      s ∈ Icc (-(((l + 1 : ℕ) : ℝ) / ((l + 2 : ℕ) : ℝ) * τ l)) 0 →
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hsk' hsl'
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, -, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, -, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hsk : s ∈ Icc (-τ k) 0 := ⟨(neg_le_neg (hcτ k).le).trans hsk'.1, hsk'.2⟩
    have hsl : s ∈ Icc (-τ l) 0 := ⟨(neg_le_neg (hcτ l).le).trans hsl'.1, hsl'.2⟩
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
        hja₁ hja₂ hjt)
  have hvolX : ∀ r R' : ℝ, 0 < r → r < R' → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ' * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    intro r R' hr hrR' C hC
    set k : ℕ := ⌈r⌉₊ + 25 with hkdef
    have hrk : r + 25 < ((k + 3 : ℕ) : ℝ) := by
      have := Nat.le_ceil r
      rw [hkdef]
      push_cast
      linarith
    obtain ⟨a, ha0, ha1, hra, haC, haK'⟩ :=
      ObservedHistory.exists_small_volume_radius hrR' hC
        (le_max_of_le_left (hK0 k) : 0 ≤ max (K k) (1 / τ k))
    have haK : a ^ 2 * K k ≤ 1 :=
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg a)).trans haK'
    have haθ : a ^ 2 ≤ τ k := by
      have h1 : a ^ 2 * (1 / τ k) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg a)).trans haK'
      rw [mul_one_div, div_le_one (hτ k)] at h1
      exact h1
    refine ⟨a, κ * (Real.exp (-(9 / 4)) * (1 / 2)) ^ 3 * Real.exp (-(27 / 4)), ha0,
      by positivity, hra, haC, ?_⟩
    filter_upwards [hsurv k, hA (-(a ^ 2 / 4)) (by have := pow_pos ha0 2; linarith),
      hRlim.eventually_ge_atTop ((a / ρ) ^ 2)] with n hn hAn hRn x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hxr : riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x ≤ ENNReal.ofReal r := hx
    have hsubX : riemannianClosedBallOf (X.obj n).metric x 25 ⊆ W k n :=
      (riemannianClosedBallOf_subset_of_add_radius_le _ hr.le (by norm_num) le_rfl hx).trans
        (hsubW k n hn hrk)
    have hxW : x ∈ W k n := hsubX (by
      change riemannianEDistOf _ x x ≤ _
      rw [riemannianEDistOf_self]
      exact bot_le)
    have haρ : a ≤ ρ * Real.sqrt (R n) := by
      have hsq : a / ρ ≤ Real.sqrt (R n) := Real.le_sqrt_of_sq_le hRn
      rw [div_le_iff₀ hρ] at hsq
      linarith
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) ⟨x, hxW⟩ 25) := by
      rw [hn.2.2.1]
      exact ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen _ _ _ _ hsubX
    have hW := volume_ball_ge_of_isScaledSurvivorData_at_depth (H n) (t n) (y n) (hR n) hn hκ
      (A := fun v : ℝ => v < t₀ n) (hnc' n) ha0 ha1 haθ haK (hK0 k) haρ hAn ⟨x, hxW⟩ hcpt
    rw [hn.2.2.1] at hW
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hfin]
    refine hW.trans ?_
    exact ObservedHistory.riemannianVolumeMeasure_restrictOpen_le (X.obj n).metric (W k n)
      (by
        let : MeasurableSpace (X.obj n).M := borel _
        have : BorelSpace (X.obj n).M := ⟨rfl⟩
        exact (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ x)
          continuous_const).measurableSet)
      (fun w hw => lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen _ _ _ _) hw)
  have hlipW : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop,
      ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
      ∀ σ' ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, ∀ z : W k n,
        (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
        ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'| := by
    intro k p
    obtain ⟨L, -, hL⟩ :=
      exists_metricDerivNorm_terminal_reference_time_lipschitz_of_curvature_jets.{u}
        (I := ThreeModel) p (hc k) (hcτ k) (Bj k)
    refine ⟨L, ?_⟩
    filter_upwards [hsurv k, hjetsAt k] with n hn hjn σ hσ σ' hσ' z hz a ha
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hopen : IsOpen (riemannianBallOf (X.obj n).metric (X.obj n).basepoint
        (((k + 2 : ℕ) : ℝ) + 1 / 4)) :=
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    let U : Opens (W k n) := ⟨Subtype.val ⁻¹' riemannianBallOf (X.obj n).metric
      (X.obj n).basepoint (((k + 2 : ℕ) : ℝ) + 1 / 4), hopen.preimage continuous_subtype_val⟩
    let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
    have hS : IsSolutionOn ({ base.metric := h k n } : SolutionOn (I := ThreeModel)
        (M := W k n) (RealTimeInterval.closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le))) :=
      hn.2.1 (τ k) (hτ k).le le_rfl
    have hSU := isSolutionOn_restrictOpen _ hS U
    have hjU : ∀ m ≤ p, ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
        ∀ w : U, curvDerivNorm m ((h k n s).restrictOpen U) w ≤ Bj k m := by
      intro m _ s hs w
      rw [curvDerivNorm_restrictOpen]
      exact hjn m s hs (w : W k n) (le_of_lt (show riemannianEDistOf (X.obj n).metric
        (X.obj n).basepoint ((w : W k n) : (X.obj n).M) <
          ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 4) from w.2))
    have hz' : z ∈ U := by
      change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (z : (X.obj n).M) <
        ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 4)
      exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
    have key := hL (fun s => (h k n s).restrictOpen U) hSU hjU σ hσ σ' hσ' ⟨z, hz'⟩ a ha
    rwa [metricDerivNorm_restrictOpen] at key
  have hscalW : ∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0,
      ∀ x : W k n, metricScalarAt (h k n s) x ≤ B := by
    intro k
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x
    exact ObservedHistory.metricScalarAt_le_of_curvDerivNormSq_zero_le (h k n s) x
      (hn.2.2.2.1 s hs x)
  obtain ⟨f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hG,
    hGcompat, ψ, hψ, hconv⟩ :=
    exists_pointed_local_flow_limits_of_local_solutions X hcompact hvolX τ
      (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k) hc hcτ W h hball hsolτ hzero hjets
      hcompat
  have hncW : ∀ k : ℕ, ∀ σ ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0, σ < 0 →
      ∀ᶠ n in atTop, ∀ z : W k n, ∀ r : ℝ, 0 < r → r ≤ ρ * Real.sqrt (R n) →
        Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
        IsCompact (riemannianClosedBallOf (h k n σ) z r) →
        (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
          r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
        ENNReal.ofReal (κ * r ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
            (riemannianBallOf (h k n σ) z r) := by
    intro k σ hσ hσ0
    filter_upwards [hsurv k, hA σ hσ0] with n hn hAn z r hr hrρ hsub hcpt hcurv
    exact ObservedHistory.volume_ball_ge_of_isScaledSurvivorData_of_admissible (H n) (t n) (y n)
      (hR n) hn hκ.le (A := fun v : ℝ => v < t₀ n) (hnc' n) hr hrρ
      (hsub ⟨le_rfl, by nlinarith⟩).1 hσ.2 hAn z hcpt hcurv
  refine ⟨W, h, fun k => ?_, hlipW, hscalW, hlowW, hpinchW, hncW, f, hf, P, F, hCd, hPc, hconn,
    hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hG, hGcompat, ψ, hψ, hconv⟩
  filter_upwards [hsurv k] with n hn
  refine ⟨hWset k n hn, hn.2.1 (τ k) (hτ k).le le_rfl, fun s hs hdom => hn.2.2.2.2.1 s hs hdom,
    hn.2.2.2.2.2, ?_⟩
  intro σ hσ hσt z r hr hrρ hsub hcpt hcurv
  have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
  exact ObservedHistory.volume_ball_ge_of_isScaledSurvivorData_of_admissible (H n) (t n) (y n)
    (hR n) hn hκ.le (A := fun v : ℝ => v < t₀ n) (hnc' n) hr hrρ hlow hσ.2 hσt z hcpt hcurv

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
