import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalMetricTimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.RicciLowerMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingRicciLowerBound
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Curvature.OperatorScaling
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitTerminalNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.EarlierTimeVolume
import DifferentialGeometry.Geometry.Comparison.Volume.DiffeomorphVolume

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.isScaledSurvivorData
  ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion
  ObservedHistory.isParabolicallyRmControlledBall_of_isScaledSurvivorData from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.scaleMetric_restrictOpenOfSubset
  ObservedHistory.comp_inclusion_eq_of_backward_maps ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.exists_curvDerivNorm_bound_of_window
  ObservedHistory.scaled_volume_ball_ge_of_isTracedRegion
  ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.riemannianClosedBallOf_scaleMetric_eq
  ObservedHistory.exists_small_volume_radius from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn
  (neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt
    parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt)

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

private theorem metricScalarAt_le_of_curvDerivNormSq_zero_le {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {K : ℝ}
    (h : curvDerivNormSq 0 g x ≤ K ^ 2) :
    metricScalarAt g x ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K| := by
  have hsq : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |K| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  exact (le_abs_self _).trans ((scalar_abs_le_rm g x).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity)))

private theorem riemannianVolumeMeasure_restrictOpen_le {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M) [SigmaCompactSpace U]
    {A : Set U} {B : Set M} (hB : letI : MeasurableSpace M := borel M; MeasurableSet B)
    (hAB : ∀ x ∈ A, (x : M) ∈ B) :
    Integral.Measure.riemannianVolumeMeasure ThreeModel U (g.restrictOpen U) A ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel M g B := by
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hmap := congrArg (fun μ : MeasureTheory.Measure M ↦ μ B)
    (Geometry.Riemannian.VolumeComparison.riemannianVolumeMeasure_map_restrictOpen
      (I := ThreeModel) g U)
  rw [MeasureTheory.Measure.map_apply continuous_subtype_val.measurable hB,
    MeasureTheory.Measure.restrict_apply hB] at hmap
  calc Integral.Measure.riemannianVolumeMeasure ThreeModel U (g.restrictOpen U) A
      ≤ Integral.Measure.riemannianVolumeMeasure ThreeModel U (g.restrictOpen U)
          ((Subtype.val : U → M) ⁻¹' B) := MeasureTheory.measure_mono (fun x hx ↦ hAB x hx)
    _ = Integral.Measure.riemannianVolumeMeasure ThreeModel M g (B ∩ (U : Set M)) := hmap
    _ ≤ Integral.Measure.riemannianVolumeMeasure ThreeModel M g B :=
        MeasureTheory.measure_mono inter_subset_left

private theorem volume_ball_ge_of_isScaledSurvivorData_of_admissible (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ θ K κ ρnc : ℝ}
    (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W}
    (hd : ObservedHistory.isScaledSurvivorData H t y R ρ θ K hR W g)
    (hκ : 0 ≤ κ)
    {A : ℝ → Prop}
    (hnc : ∀ (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier) (r : ℝ), (v : ℝ) ≤ t →
      A v → r ≤ ρnc → H.isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) p r))
    {σ r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρnc * Real.sqrt R) (hwin : -θ ≤ σ - r ^ 2) (hσ : σ ≤ 0)
    (hA : A ((t : ℝ) + σ / R))
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
      exact ObservedHistory.isParabolicallyRmControlledBall_of_isScaledSurvivorData H t hR a ha
        f hf hc hp hr''.1
        hr''.2.le hwin hσ vI rfl hav hvt b hbv rfl w (fun s hs => hcurv s hs w (by
          rw [hball']
          exact riemannianBallOf_mono _ _ hr''.2.le hw))
    have hv := hnc vI (f j z) r'' hvt hA (hr''.2.le.trans (by
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

private theorem volume_ball_ge_of_isScaledSurvivorData_at_zero (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ K κ ρnc : ℝ} {k : ℕ}
    (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W}
    (hd : ObservedHistory.isScaledSurvivorData H t y R ρ (2 * ((k + 2 : ℕ) : ℝ)) K hR W g)
    (hκ : 0 < κ) {A : ℝ → Prop}
    (hnc : ∀ (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier) (r : ℝ), (v : ℝ) ≤ t →
      A v → r ≤ ρnc → H.isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v) p r))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haK : a ^ 2 * K ≤ 1) (hK : 0 ≤ K)
    (haρ : a ≤ ρnc * Real.sqrt R) (hA : A ((t : ℝ) + -(a ^ 2 / 4) / R)) (x : W)
    (hcpt : IsCompact (riemannianClosedBallOf (g 0) x 25)) :
    ENNReal.ofReal (κ * (Real.exp (-(9 / 4)) * (1 / 2)) ^ 3 * Real.exp (-(27 / 4)) * a ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (g 0) (riemannianBallOf (g 0) x a) := by
  set θ : ℝ := 2 * ((k + 2 : ℕ) : ℝ) with hθdef
  have hθ1 : 1 ≤ θ := by rw [hθdef]; push_cast; linarith
  let D := RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr (by linarith))
  let S : SolutionOn (I := ThreeModel) (M := W) D := { base.metric := g }
  have hS : IsSolutionOn S := hd.2.1 θ (by linarith) le_rfl
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
    have hv := volume_ball_ge_of_isScaledSurvivorData_of_admissible H t y hR hd hκ.le hnc
      hr' (hra.trans haρ) hlo ht'0 (by rw [ht'']; exact hA) x hcpt' hcurv'
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

private theorem exists_ancient_pointed_flow_limit_of_isTracedRegion_of_admissible_times
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    {A : ℕ → ℝ → Prop} (hA : ∀ s : ℝ, s < 0 → ∀ᶠ n in atTop, A n ((t n : ℝ) + s / R n))
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) ≤ t n → A n v → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
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
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, A n ((t n : ℝ) + σ / R n) → ∀ z : W k n,
          ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
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
                  (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) ∧
                  ∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                    ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (κ / 250) ρ' := by
  intro X
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  choose K hK0 hKev using fun k : ℕ => htraced ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
    (by positivity) (hθ k)
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n) →
        ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        ObservedHistory.exists_isScaledSurvivorData_of_isTracedRegion (H n) (t n) (y n) (hR n)
          (hθ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
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
  have hsubW (k n : ℕ) (hn : ObservedHistory.isScaledSurvivorData (H n) (t n) (y n) (R n)
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
    set k : ℕ := ⌈r⌉₊ + 25 with hkdef
    have hrk : r + 25 < ((k + 3 : ℕ) : ℝ) := by
      have := Nat.le_ceil r
      rw [hkdef]
      push_cast
      linarith
    obtain ⟨a, ha0, ha1, hra, haC, haK⟩ :=
      ObservedHistory.exists_small_volume_radius hrR' hC (hK0 k)
    refine ⟨a, κ * (Real.exp (-(9 / 4)) * (1 / 2)) ^ 3 * Real.exp (-(27 / 4)), ha0,
      by positivity, hra, haC, ?_⟩
    filter_upwards [hsurv k, hA (-(a ^ 2 / 4)) (by have := pow_pos ha0 2; linarith),
      hRlim.eventually_ge_atTop ((a / ρ) ^ 2)] with n hn hAn hRn x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hxr : riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x ≤ ENNReal.ofReal r := hx
    have hsubX : riemannianClosedBallOf (X.obj n).metric x 25 ⊆ W k n := by
      intro w hw
      have hw' : riemannianEDistOf (X.obj n).metric x w ≤ ENNReal.ofReal 25 := hw
      rw [hWset k n hn]
      change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w <
        ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
      calc riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w
          ≤ riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x +
              riemannianEDistOf (X.obj n).metric x w := riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal 25 := add_le_add hxr hw'
        _ = ENNReal.ofReal (r + 25) := (ENNReal.ofReal_add hr.le (by norm_num)).symm
        _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hrk
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
    have hW := volume_ball_ge_of_isScaledSurvivorData_at_zero (H n) (t n) (y n) (hR n) hn hκ
      (hnc n) ha0 ha1 haK (hK0 k) haρ hAn ⟨x, hxW⟩ hcpt
    rw [hn.2.2.1] at hW
    have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hfin]
    refine hW.trans ?_
    exact riemannianVolumeMeasure_restrictOpen_le (X.obj n).metric (W k n)
      (by
        let : MeasurableSpace (X.obj n).M := borel _
        have : BorelSpace (X.obj n).M := ⟨rfl⟩
        exact (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ x)
          continuous_const).measurableSet)
      (fun w hw => lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen _ _ _ _) hw)
  have hlipW : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
        ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'| := by
    intro k p
    obtain ⟨L, -, hL⟩ := exists_metricDerivNorm_time_lipschitz_of_curvature_bound_on_open.{u}
      (I := ThreeModel) p (T := ((k + 1 : ℕ) : ℝ)) (T₂ := ((k + 2 : ℕ) : ℝ)) (r := 1 / 4)
      (K := K k) (by positivity) (by push_cast; linarith) (by norm_num)
    refine ⟨L, ?_⟩
    filter_upwards [hsurv k] with n hn σ hσ σ' hσ' z hz a ha
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hopen : IsOpen (riemannianBallOf (X.obj n).metric (X.obj n).basepoint
        (((k + 2 : ℕ) : ℝ) + 1 / 2)) :=
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    let U : Opens (W k n) := ⟨Subtype.val ⁻¹' riemannianBallOf (X.obj n).metric
      (X.obj n).basepoint (((k + 2 : ℕ) : ℝ) + 1 / 2), hopen.preimage continuous_subtype_val⟩
    refine hL (h k n) (hn.2.1 _ (by positivity) le_rfl) hn.2.2.2.1 U ?_ σ hσ σ' hσ' z ?_ a ha
    · intro x hx
      rw [hn.2.2.1]
      apply ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
      intro w hw
      rw [hWset k n hn]
      have hx' : riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (x : (X.obj n).M) <
          ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2) := hx
      have hw' : riemannianEDistOf (X.obj n).metric (x : (X.obj n).M) w ≤
          ENNReal.ofReal (1 / 4) := hw
      change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w <
        ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
      calc riemannianEDistOf (X.obj n).metric (X.obj n).basepoint w
          ≤ riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (x : (X.obj n).M) +
              riemannianEDistOf (X.obj n).metric (x : (X.obj n).M) w :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2) + ENNReal.ofReal (1 / 4) :=
            ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw')
              hx' hw'
        _ = ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2 + 1 / 4) :=
            (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
        _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)
    · change riemannianEDistOf (X.obj n).metric (X.obj n).basepoint (z : (X.obj n).M) <
        ENNReal.ofReal (((k + 2 : ℕ) : ℝ) + 1 / 2)
      exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hscalW : ∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
      ∀ x : W k n, metricScalarAt (h k n s) x ≤ B := by
    intro k
    refine ⟨(Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x
    exact metricScalarAt_le_of_curvDerivNormSq_zero_le (h k n s) x
      (hn.2.2.2.1 s ⟨by have := hs.1; push_cast at this ⊢; linarith, hs.2⟩ x)
  have hpinchW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
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
  have hlowW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
      (u : TangentSpace ThreeModel x),
      (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u := by
    intro k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    filter_upwards [hsurv k, Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto hPhi
      hRlim ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * |K k|) (1 / (2 * ((k + 1 : ℕ) : ℝ)))
      (by positivity), hpinchW k] with n hn hδ hpw s hs x u
    have hsk : -((k + 2 : ℕ) : ℝ) < s := by have := hs.1; push_cast at this ⊢; linarith
    let S : SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))) :=
      { base.metric := h k n }
    have hS : IsSolutionOn S :=
      hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith)
    have hRic : ∀ q ∈ Ioo s 0, -(1 / ((k + 1 : ℕ) : ℝ)) * (S.base.metric q).inner x u u ≤
        S.ricciAt q x (vec2 u u) := by
      intro q hq
      have hqθ : q ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 :=
        ⟨by have := hs.1; push_cast at this ⊢; linarith [hq.1], hq.2.le⟩
      have hscal := hpw q hqθ x
      have hric := neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt
        (h k n q) x hscal u
      have hle := hδ _ (metricScalarAt_le_of_curvDerivNormSq_zero_le (h k n q) x
        (hn.2.2.2.1 q hqθ x))
      have hn0 := metric_inner_self_nonneg (h k n q) x u
      have hδeq : 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ))) = 1 / ((k + 1 : ℕ) : ℝ) := by
        field_simp
      change -(1 / ((k + 1 : ℕ) : ℝ)) * (h k n q).inner x u u ≤
        metricRicciAt (h k n q) x (vec2 u u)
      have hmono : -(1 / ((k + 1 : ℕ) : ℝ)) * (h k n q).inner x u u ≤
          -(2 * Perelman.rescalePinchingFunction (R n) Phi (metricScalarAt (h k n q) x)) *
            (h k n q).inner x u u := by
        rw [← hδeq]
        exact mul_le_mul_of_nonneg_right (by linarith) hn0
      exact hmono.trans hric
    have hB2 := metric_inner_le_exp_mul_of_ricci_lower_bound S hS hs.2
      (fun r hr => ⟨by linarith [hr.1], hr.2⟩) (fun r hr => ⟨by linarith [hr.1], hr.2⟩) x u hRic
    refine hB2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
      (metric_inner_self_nonneg _ _ _))
    have hs1 : -s ≤ ((k + 1 : ℕ) : ℝ) := by linarith [hs.1]
    rw [show 2 * (1 / ((k + 1 : ℕ) : ℝ)) * (0 - s) = 2 * (-s / ((k + 1 : ℕ) : ℝ)) by ring]
    have : -s / ((k + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hk1).mpr hs1
    linarith
  have hncW : ∀ k : ℕ, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, σ < 0 → ∀ᶠ n in atTop,
      ∀ z : W k n, ∀ r : ℝ, 0 < r → r ≤ ρ * Real.sqrt (R n) →
      Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
          (riemannianBallOf (h k n σ) z r) := by
    intro k σ hσ hσ0
    filter_upwards [hsurv k, hA σ hσ0] with n hn hAn z r hr hrρ hsub hcpt hcurv
    have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
    refine volume_ball_ge_of_isScaledSurvivorData_of_admissible (H n) (t n) (y n) (hR n) hn
      hκ.le (hnc n) hr hrρ ?_ hσ.2 hAn z hcpt hcurv
    push_cast at hlow ⊢
    linarith
  obtain ⟨f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ,
    hconv⟩ := exists_ancient_pointed_flow_limit_of_local_solutions X hcompact hvolX W h hball
      hsol hzero hjets hcompat
  refine ⟨W, h, fun k => ?_, hlipW, hscalW, hlowW, f, hf, P, F, hCd, hPc, hconn, hballF, V, N,
    hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ, hconv, fun ρ' hρ' => ?_⟩
  swap
  · exact parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt
      hsol hκ hRlim hρ hncW hf F hPc hconn hV hVF φ hφ hφF hG0 hG hψ hconv hRlim hPhi
      (fun k => (hpinchW k).mono fun n hn q hq x => hn q
        ⟨by have := hq.1; push_cast at this ⊢; linarith, hq.2⟩ x) ρ' hρ'
  filter_upwards [hsurv k] with n hn
  refine ⟨hWset k n hn, hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _) (by push_cast; linarith),
    fun s hs hdom => hn.2.2.2.2.1 s ⟨?_, hs.2⟩ hdom, hn.2.2.2.2.2, ?_⟩
  · have := hs.1
    push_cast at this ⊢
    linarith
  intro σ hσ hAσ z r hr hrρ hsub hcpt hcurv
  have hlow := (hsub ⟨le_rfl, by nlinarith⟩).1
  refine volume_ball_ge_of_isScaledSurvivorData_of_admissible (H n) (t n) (y n) (hR n) hn
    hκ.le (hnc n) hr hrρ ?_ hσ.2 hAσ z hcpt hcurv
  push_cast at hlow ⊢
  linarith

theorem exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
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
        ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, (t n : ℝ) + σ / R n < t₀ n → ∀ z : W k n,
          ∀ r : ℝ, 0 < r →
          r ≤ ρ * Real.sqrt (R n) → Icc (σ - r ^ 2) σ ⊆ Icc (-((k + 2 : ℕ) : ℝ)) 0 →
          IsCompact (riemannianClosedBallOf (h k n σ) z r) →
          (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
            r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
          ENNReal.ofReal (κ * r ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
              (riemannianBallOf (h k n σ) z r)) ∧
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
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
                  (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) ∧
                  ∀ ρ' : ℝ, 0 < ρ' → Perelman.ParabolicallyKappaNoncollapsedBelowScale
                    ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                      (RealTimeInterval.infiniteClosed 0 0 le_rfl)) (κ / 250) ρ' := by
  refine exists_ancient_pointed_flow_limit_of_isTracedRegion_of_admissible_times H t y R hR hRlim
    htraced hκ hρ (A := fun n v => v < t₀ n) ?_ (fun n v p r _ hv hr hpc => hnc n v p r hv hr hpc)
    hPhi hpinch
  intro s hs
  filter_upwards [hsliver.eventually (gt_mem_nhds (show (0 : ℝ) < -s by linarith))] with n hn
  have h1 : t n - t₀ n < -s / R n := by
    rw [lt_div_iff₀ (hR n)]
    linarith
  have h2 : s / R n = -(-s / R n) := by ring
  linarith

theorem exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_isTracedRegion
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
      (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) ∧
      (∀ k : ℕ, ∃ B : ℝ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
        metricScalarAt (h k n s) x ≤ B) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) ∧
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
  obtain ⟨W, h, hk, hlip, hscal, hlow, f, hf, P, F, hCd, hPc, hconn, hballF, V, N, hV, hVF, φ,
    hφ, hφF, G, hG0, hG, ψ, hψ, hconv, -⟩ :=
    exists_ancient_pointed_flow_limit_of_isTracedRegion_of_admissible_times H t y R hR hRlim
      htraced hκ hρ (A := fun n v => v ≤ t n)
      (fun s hs => Eventually.of_forall fun n => by
        have : s / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.le (hR n).le
        linarith)
      (fun n v p r hv _ hr hpc => hnc n v p r hv hr hpc) hPhi hpinch
  refine ⟨W, h, fun k => (hk k).mono fun n hn => ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
    fun σ hσ => hn.2.2.2.2 σ hσ ?_⟩, hlip, hscal, hlow, f, hf, P, F, hCd, hPc, hconn, hballF, V,
    N, hV, hVF, φ, hφ, hφF, G, hG0, hG, ψ, hψ, hconv⟩
  have : σ / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hσ.2 (hR n).le
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
