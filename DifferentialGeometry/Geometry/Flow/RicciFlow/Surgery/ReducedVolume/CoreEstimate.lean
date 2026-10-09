import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBallForwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.MinimizingDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ParabolicBallRange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.VolumeDistortion
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.WindowSolutionMap

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped ENNReal ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private theorem setLIntegral_le_mul_of_forall_mem_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} {f : X → ℝ≥0∞} {c : ℝ≥0∞} (hf : ∀ x ∈ s, f x ≤ c) :
    ∫⁻ x in s, f x ∂μ ≤ c * μ s := by
  rw [lintegral_def]
  refine iSup₂_le fun g hg => ?_
  have hm : MeasurableSet {x | ¬ g x ≤ c} :=
    (measurableSet_le g.measurable measurable_const).compl
  have hae : ∀ᵐ x ∂μ.restrict s, g x ≤ c := by
    rw [ae_iff, Measure.restrict_apply hm]
    have hempty : {x | ¬ g x ≤ c} ∩ s = ∅ :=
      eq_empty_of_forall_notMem fun x hx => hx.1 ((hg x).trans (hf x hx.2))
    rw [hempty, measure_empty]
  calc g.lintegral (μ.restrict s) = ∫⁻ x, g x ∂μ.restrict s :=
        (SimpleFunc.lintegral_eq_lintegral g _).symm
    _ ≤ ∫⁻ _, c ∂μ.restrict s := lintegral_mono_ae hae
    _ = c * μ s := by rw [lintegral_const, Measure.restrict_apply_univ]

variable {H : ObservedHistory.{u}}

private theorem regularizedDensity_historyLExp_le_of_scalar_lower
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v C : ℝ}
    {p : (H.stage last).Carrier} (hv : 0 < v)
    (hfloor : ∀ j, ∀ τ ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j τ) x)
    (Z : H.historyLExpDomain hle T v p) (hZ : Z.1 ∈ H.historyMinDomain hle T B v p)
    (hC : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
        -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2))
          (H.historyLCurve hle T v p Z j s)) :
    H.regularizedDensity first last hle T B v p (H.historyLExp hle T v p Z) ≤
      ENNReal.ofReal (Real.exp (C * v ^ 2 / 3 - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  obtain ⟨α, hgeo, hinit, hac, -, hmin, -⟩ := hZ
  have hq : H.historyLExp hle T v p Z = α ⟨first, le_rfl, hle⟩ v := historyLExp_eq hv Z hgeo hinit
  have heq := eqOn_historyLCurve hv Z hgeo hinit
  have hT : T ∈ H.stageDomain last := by
    obtain ⟨lo, hlo, W, x, Zx, ha, -⟩ := hinit
    simpa [ha] using W.upper
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    rw [sq, mul_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hT, H.le_stageEndTime_of_mem_stageDomain hT⟩
  have hpiece : ∀ j : H.StageInterval first last,
      ((-(2 * C / 3) * (H.regularizedStageEnd T v j.val ^ 3 -
          H.regularizedStageStart T 0 j.val ^ 3) : ℝ) : WithTop ℝ) ≤
        H.stageRegularizedExtendedAction j.val T B (α j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
    intro j
    have hbnd := H.regularizedStage_bounds le_rfl hv.le hupper hgeo.1 j
    have hBae : ∀ᵐ s ∂volume.restrict
        (Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)),
        -B ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) (α j s) :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun s hs =>
        hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T 0 v j.val hs) _
    have hCae : ∀ᵐ s ∂volume.restrict
        (Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)),
        -C ≤ metricScalarAt (H.stageMetric j.val (T - s ^ 2)) (α j s) :=
      ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => by
        rw [← heq j (Ioo_subset_Icc_self hs)]
        exact hC j s hs
    rw [H.stageRegularizedExtendedAction_congr_scalar_lower_bound_of_absolutelyContinuousOnInterval
      j.val T B C 0 v (α j) (hac j) hBae hCae]
    have hint : ∫ s in Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
        -2 * C * s ^ 2 = -(2 * C / 3) * (H.regularizedStageEnd T v j.val ^ 3 -
          H.regularizedStageStart T 0 j.val ^ 3) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbnd.2.1,
        intervalIntegral.integral_const_mul, integral_pow]
      ring
    rw [← hint]
    exact DifferentialGeometry.Analysis.integral_lower_bound_le_lowerBoundedIntegral _ _ _
  have hsum : ((-(2 * C / 3) * v ^ 3 : ℝ) : WithTop ℝ) ≤
      H.regularizedExtendedAction first last T B 0 v α := by
    have hs := H.sum_regularizedStage_sub (fun x : ℝ => -(2 * C / 3) * x ^ 3) hle le_rfl hv.le
      hupper hgeo.1
    have hv3 : -(2 * C / 3) * v ^ 3 = ∑ j : H.StageInterval first last,
        -(2 * C / 3) * (H.regularizedStageEnd T v j.val ^ 3 -
          H.regularizedStageStart T 0 j.val ^ 3) := by
      rw [show -(2 * C / 3) * v ^ 3 = -(2 * C / 3) * v ^ 3 - -(2 * C / 3) * 0 ^ 3 by ring,
        ← hs]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hv3, WithTop.coe_sum]
    exact Finset.sum_le_sum fun j _ => hpiece j
  unfold regularizedDensity
  refine iSup₂_le fun A hA => ?_
  have hcost : H.regularizedCost first last hle T B 0 v p (H.historyLExp hle T v p Z) ≤ A :=
    H.regularizedCost_le_of_competitor first last hle T B 0 v p _ hA
  rw [hq, ← hmin] at hcost
  have hAlow : -(2 * C / 3) * v ^ 3 ≤ A := WithTop.coe_le_coe.mp (hsum.trans hcost)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hdiv : -A / (2 * v) ≤ C * v ^ 2 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * v)).mpr
    nlinarith
  linarith

private theorem exists_mem_historyLExpDomain_eqOn_of_commonFlow
    {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) {T v : ℝ} (hv : 0 < v)
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    [T2Space X] [SigmaCompactSpace X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hl : first ≤ i.castSucc) (hh : i.succ ≤ last) (z : X),
      (H.event i).RegularCrossing (f ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)
        (f ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ z))
    (hupper : T ∈ H.stageDomain last) (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hreg : ∀ s ∈ Icc 0 v, T - s ^ 2 ∈ D.regular)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
        S.base.metric (T - s ^ 2) = localPullMetric (H.stageMetric j.val (T - s ^ 2)) (f j) (hf j))
    {p : (H.stage last).Carrier} {x : X} (hx : f ⟨last, hle, le_rfl⟩ x = p)
    {Zx : TangentSpace ThreeModel x} {Z : TangentSpace ThreeModel p}
    (hZ : mfderiv ThreeModel ThreeModel (f ⟨last, hle, le_rfl⟩) x Zx = Z)
    (hdom : v ∈ lRegularizedDomain S T x Zx) :
    ∃ hZd : Z ∈ H.historyLExpDomain hle T v p, ∀ j : H.StageInterval first last,
      EqOn (H.historyLCurve hle T v p ⟨Z, hZd⟩ j) (f j ∘ lRegularizedCurve S T x Zx)
        (Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) := by
  let W : H.LWindow first last T :=
    { X := X, a := 0, b := v, nonneg := le_rfl, lt := hv, le := hle
      upper := by simpa using hupper
      lower := hlower, D := D, S := S, solution := hS, regular := hreg, f := f
      localDiffeomorph := hf, injective := hinj, crossing := hcross, metric := hmetric }
  have hgeoS := isLRegularizedGeodesicOn_lRegularizedCurve S hS T x Zx
  have hsub : Icc 0 v ⊆ lRegularizedDomain S T x Zx := fun s hs =>
    lRegularizedDomain_segment S T x Zx hdom hs.1 hs.2
  have hβ : H.IsHistoryLGeodesicOn hle T v (fun j => f j ∘ lRegularizedCurve S T x Zx) := by
    refine ⟨hlower, fun i hl hh => hcross i hl hh _, fun s hs => ⟨first, last, le_rfl, le_rfl, W,
      hs, le_rfl, lRegularizedCurve S T x Zx, fun r hr => hgeoS r (hsub ⟨hr.1.le, hr.2.le⟩),
      fun j r _ => rfl⟩, ?_⟩
    have hd := (hgeoS v (hsub ⟨hv.le, le_rfl⟩)).2.1
    exact ((hf _).contMDiff.continuous.continuousAt.comp hd.continuousAt).continuousWithinAt
  have hinit : H.HasHistoryLInitialVector T (fun j => f j ∘ lRegularizedCurve S T x Zx) p Z :=
    ⟨first, le_rfl, W, x, Zx, rfl, hx, hZ, hdom, fun _ _ _ => rfl⟩
  exact ⟨⟨_, hβ, hinit⟩, fun j => eqOn_historyLCurve hv ⟨Z, ⟨_, hβ, hinit⟩⟩ hβ hinit j⟩

private theorem exp_density_exponent_le {C v : ℝ} (hv : 0 < v) (hC : C * v ^ 2 / 3 ≤ 9) :
    Real.exp (C * v ^ 2 / 3 - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi)) ≤
      (4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 9 / v ^ 3 := by
  have h4 : 0 < 4 * Real.pi := by positivity
  have hv3 : v ^ 3 = Real.exp (3 * Real.log v) := by
    rw [show (3 : ℝ) * Real.log v = Real.log (v ^ 3) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hv 3)]
  rw [Real.rpow_def_of_pos h4, hv3, ← Real.exp_add, ← Real.exp_sub, Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

theorem exists_lintegral_image_historyMinDomain_core_le (R : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
      (p : (H.stageAt t).Carrier) (r B : ℝ), H.isParabolicallyRmControlledBall t p r →
      (t : ℝ) < H.stageEndTime (H.activeStage t) →
      (∀ j, ∀ τ ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j τ) x) →
      ∀ (hle : H.activeStage (projIcc 0 H.horizon H.horizon_nonneg (t - (σ * r) ^ 2)) ≤
        H.activeStage t),
      ∫⁻ q in H.historyLExp hle t (σ * r) p '' (Subtype.val ⁻¹'
          (H.historyMinDomain hle t B (σ * r) p ∩
            {Z | Real.sqrt ((H.stageMetric (H.activeStage t) t).inner p Z Z) ≤ R})),
          H.regularizedDensity _ _ hle t B (σ * r) p q
          ∂riemannianVolumeMeasure ThreeModel
            (H.stage (H.activeStage (projIcc 0 H.horizon H.horizon_nonneg
              (t - (σ * r) ^ 2)))).Carrier (H.stageMetric _ (t - (σ * r) ^ 2)) ≤
        ENNReal.ofReal ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 36 / (σ * r) ^ 3) *
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
            (H.stageMetric (H.activeStage t) t)
            (riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) := by
  obtain ⟨σ₀, hσ₀, hσ₀1, hG6⟩ :=
    exists_pos_lRegularizedCurve_mem_ball_of_parabolic_rm_bound.{u, 0, 0} (I := ThreeModel) R
  refine ⟨σ₀ / 2, by positivity, by linarith, ?_⟩
  intro H t p r B hball ht hfloor
  have hr : 0 < r := hball.1
  set v : ℝ := σ₀ / 2 * r with hvdef
  set first := H.activeStage (projIcc 0 H.horizon H.horizon_nonneg (t - v ^ 2))
  set last := H.activeStage t
  intro hle
  have hv : 0 < v := by positivity
  have hvr : v ≤ r / 2 := by rw [hvdef]; nlinarith
  have hv2 : v ^ 2 < r ^ 2 := by nlinarith
  obtain ⟨a, hat, ha, t₁, htt₁, U, hU, f, hf, hinj, hcross, hfx, S, hS, hSmetric, hRm, hSt, pU,
    K, hpU, hKimg, hK, -, -⟩ :=
    H.exists_common_flow_past_time_of_parabolicallyRmControlledBall t p r hball ht
  subst hpU
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have ha0 : (0 : ℝ) ≤ t - r ^ 2 := ha ▸ a.2.1
  have hproj : ((projIcc 0 H.horizon H.horizon_nonneg (t - v ^ 2) : Icc (0 : ℝ) H.horizon) : ℝ) =
      t - v ^ 2 := by
    rw [projIcc_of_mem _ ⟨by linarith, by linarith [t.2.2, sq_nonneg v]⟩]
  have hlower : (t : ℝ) - v ^ 2 ∈ H.stageDomain first := by
    have h := H.activeStage_mem (projIcc 0 H.horizon H.horizon_nonneg (t - v ^ 2))
    rwa [hproj] at h
  have hupper : (t : ℝ) ∈ H.stageDomain last := H.activeStage_mem t
  have hupper0 : (t : ℝ) - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    rw [sq, mul_zero, sub_zero]
    exact ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have haf : H.activeStage a ≤ first :=
    H.activeStage_mono (show (a : ℝ) ≤ _ by rw [hproj, ha]; linarith)
  let f' : (j : H.StageInterval first last) → U → (H.stage j.val).Carrier :=
    fun j => f ⟨j.val, haf.trans j.2.1, j.2.2⟩
  have hf' : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f' j) := fun j => hf _
  have hinj' : ∀ j, Function.Injective (f' j) := fun j => hinj _
  have hcross' : ∀ (i : Fin H.eventCount) (hl : first ≤ i.castSucc) (hh : i.succ ≤ last) (z : U),
      (H.event i).RegularCrossing (f' ⟨i.castSucc, hl, i.castSucc_lt_succ.le.trans hh⟩ z)
        (f' ⟨i.succ, hl.trans i.castSucc_lt_succ.le, hh⟩ z) :=
    fun i hl hh z => hcross i (haf.trans hl) hh z
  have hreg : ∀ s ∈ Icc 0 v, (t : ℝ) - s ^ 2 ∈
      (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)).regular :=
    fun s hs => show (t : ℝ) - s ^ 2 ∈ Ioo (a : ℝ) t₁ from
      ⟨by rw [ha]; nlinarith [hs.1, hs.2], by nlinarith [sq_nonneg s]⟩
  have hsbound : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        0 < s ∧ s < v := fun j s hs => by
    have hb := H.regularizedStage_bounds le_rfl hv.le hupper0 hlower j
    exact ⟨hb.1.trans_lt hs.1, hs.2.trans_le hb.2.2⟩
  have hmetric' : ∀ j : H.StageInterval first last,
      ∀ s ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        S.base.metric (t - s ^ 2) =
          localPullMetric (H.stageMetric j.val (t - s ^ 2)) (f' j) (hf' j) := fun j s hs => by
    obtain ⟨hs0, hsv⟩ := hsbound j s hs
    exact hSmetric ⟨j.val, haf.trans j.2.1, j.2.2⟩ (t - s ^ 2)
      ⟨by rw [ha]; nlinarith, by nlinarith [sq_nonneg s]⟩
      (H.mapsTo_regularizedStage_Ioo t 0 v j.val hs)
  have hfv : f' ⟨last, hle, le_rfl⟩ = Subtype.val := funext hfx
  have hZ : ∀ Z : TangentSpace ThreeModel pU,
      mfderiv ThreeModel ThreeModel (f' ⟨last, hle, le_rfl⟩) pU Z = Z := fun Z => by
    rw [hfv]
    exact mfderiv_subtype_val_apply (I := ThreeModel) U pU Z
  have hregG6 : Ioo ((t : ℝ) - (r / 2) ^ 2) (t : ℝ) ⊆
      (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)).regular :=
    fun s hs => show s ∈ Ioo (a : ℝ) t₁ from ⟨by rw [ha]; nlinarith [hs.1], hs.2.trans htt₁⟩
  have htreg : (t : ℝ) ∈
      (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)).regular :=
    show (t : ℝ) ∈ Ioo (a : ℝ) t₁ from ⟨by rw [ha]; nlinarith, htt₁⟩
  have hcpt : IsCompact {y : U | riemannianEDistOf (S.base.metric t) pU y ≤
      ENNReal.ofReal (r / 2 / 2)} := by
    refine hK.of_isClosed_subset
      (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist _ pU) continuous_const) ?_
    intro y hy
    have hd : riemannianEDistOf (H.stageMetric last t) (pU : (H.stageAt t).Carrier) y ≤
        ENNReal.ofReal (r / 2) := by
      calc _ ≤ riemannianEDistOf ((H.stageMetric last t).restrictOpen U) pU y :=
            riemannianEDistOf_le_restrictOpen _ U pU y
        _ = riemannianEDistOf (S.base.metric t) pU y := by rw [hSt]
        _ ≤ ENNReal.ofReal (r / 2 / 2) := hy
        _ ≤ ENNReal.ofReal (r / 2) := ENNReal.ofReal_le_ofReal (by linarith)
    have hmem : (y : (H.stageAt t).Carrier) ∈ Subtype.val '' K := by
      rw [hKimg]
      exact hd
    obtain ⟨k, hk, hky⟩ := hmem
    exact (Subtype.ext hky : k = y) ▸ hk
  have hRmG6 : ∀ τ ∈ Icc ((t : ℝ) - (r / 2) ^ 2) (t : ℝ), ∀ y : U,
      riemannianEDistOf (S.base.metric t) pU y < ENNReal.ofReal (r / 2) →
        (r / 2) ^ 4 * FlowMetricBall.rmNormSq S τ y ≤ 1 := by
    intro τ hτ y _
    have h := hRm τ ⟨by rw [ha]; nlinarith [hτ.1], hτ.2⟩ y
    have hn := Tensor0SBundle.normSq0S_nonneg (S.base.metric τ) y 4 (S.base.rm04 τ y)
    unfold FlowMetricBall.rmNormSq
    have he : (r / 2) ^ 4 * Tensor0SBundle.normSq0S (S.base.metric τ) y 4 (S.base.rm04 τ y) =
        (r ^ 4 * Tensor0SBundle.normSq0S (S.base.metric τ) y 4 (S.base.rm04 τ y)) / 16 := by
      ring
    rw [he]
    linarith [mul_nonneg (pow_nonneg hr.le 4) hn]
  have hfin : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  set C : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 / r ^ 2 with hCdef
  have hCv : C * v ^ 2 / 3 ≤ 9 := by
    have : C * v ^ 2 ≤ 9 := by
      rw [hCdef, hfin, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  set c : ℝ≥0∞ := ENNReal.ofReal ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * Real.exp 9 / v ^ 3) with hc
  have hpt : ∀ q ∈ H.historyLExp hle t v (pU : (H.stageAt t).Carrier) '' (Subtype.val ⁻¹'
      (H.historyMinDomain hle t B v (pU : (H.stageAt t).Carrier) ∩
        {Z | Real.sqrt ((H.stageMetric last t).inner (pU : (H.stageAt t).Carrier) Z Z) ≤ R})),
      H.regularizedDensity _ _ hle t B v (pU : (H.stageAt t).Carrier) q ≤ c ∧
        q ∈ f' ⟨first, le_rfl, hle⟩ '' univ := by
    rintro _ ⟨⟨Z, hZd0⟩, ⟨hZm, hZR⟩, rfl⟩
    have hZR' : (S.base.metric t).inner pU Z Z ≤ R ^ 2 := by
      rw [hSt]
      have h0 := metric_inner_self_nonneg (H.stageMetric last t) (pU : (H.stageAt t).Carrier) Z
      calc ((H.stageMetric last t).restrictOpen U).inner pU Z Z
          = (H.stageMetric last t).inner (pU : (H.stageAt t).Carrier) Z Z := rfl
        _ = Real.sqrt ((H.stageMetric last t).inner (pU : (H.stageAt t).Carrier) Z Z) ^ 2 :=
            (Real.sq_sqrt h0).symm
        _ ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hZR 2
    have hdom : v ∈ lRegularizedDomain S t pU Z := by
      have h := (hG6 S hS t (r / 2) pU (by positivity) hregG6 htreg hcpt hRmG6 Z hZR').1
      rwa [show σ₀ * (r / 2) = v by rw [hvdef]; ring] at h
    obtain ⟨hZd, heqOn⟩ := exists_mem_historyLExpDomain_eqOn_of_commonFlow hle hv S hS f' hf'
      hinj' hcross' hupper hlower hreg hmetric' (hfx pU) (hZ Z) hdom
    have hEnd : H.regularizedStageEnd t v first = v :=
      H.regularizedStageEnd_eq_of_mem_stageDomain hv.le hlower
    have hb := H.regularizedStage_bounds le_rfl hv.le hupper0 hlower ⟨first, le_rfl, hle⟩
    have himg := heqOn ⟨first, le_rfl, hle⟩ ⟨hb.2.1.trans_eq hEnd, hEnd.ge⟩
    refine ⟨?_, ⟨lRegularizedCurve S t pU Z v, mem_univ _, ?_⟩⟩
    · refine (regularizedDensity_historyLExp_le_of_scalar_lower hv hfloor ⟨Z, hZd0⟩ hZm
        (C := C) fun j s hs => ?_).trans ?_
      · obtain ⟨hs0, hsv⟩ := hsbound j s hs
        have hj := heqOn j (Ioo_subset_Icc_self hs)
        rw [hj, Function.comp_apply,
          ← metricScalarAt_localPull (H.stageMetric j.val (t - s ^ 2)) (f' j) (hf' j),
          ← hmetric' j s hs]
        have hbound := scalar_abs_le_div_sq_of_rm_bound (S.base.metric (t - s ^ 2))
          (lRegularizedCurve S t pU Z s) hr.ne'
          (hRm (t - s ^ 2) ⟨by rw [ha]; nlinarith, by nlinarith [sq_nonneg s]⟩ _)
        exact (abs_le.mp hbound).1
      · exact ENNReal.ofReal_le_ofReal (exp_density_exponent_le hv hCv)
    · exact himg.symm
  have hslab : Icc ((t : ℝ) - r ^ 2) (t : ℝ) ⊆
      (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)).carrier :=
    fun s hs => show s ∈ Icc (a : ℝ) t₁ from ⟨by rw [ha]; exact hs.1, hs.2.trans htt₁.le⟩
  have hreg8 : Ioo ((t : ℝ) - r ^ 2) (t : ℝ) ⊆
      (RealTimeInterval.closed a.val t₁ ((show (a : ℝ) ≤ t from hat).trans htt₁.le)).regular :=
    fun s hs => show s ∈ Ioo (a : ℝ) t₁ from ⟨by rw [ha]; exact hs.1, hs.2.trans htt₁⟩
  have hvol8 := riemannianVolumeMeasure_le_exp_cube_mul_of_parabolic_rmNormSq_le hS hr hslab
    hreg8 MeasurableSet.univ (fun u hu y _ => hRm u ⟨by rw [ha]; exact hu.1, hu.2⟩ y)
    (subset_refl univ) (s := (t : ℝ) - v ^ 2) ⟨by linarith, by linarith [sq_nonneg v]⟩
    ⟨by linarith [sq_nonneg r], le_rfl⟩
  have hmet : ∀ (x : U) (w₁ w₂ : TangentSpace ThreeModel x),
      (S.base.metric ((t : ℝ) - v ^ 2)).inner x w₁ w₂ =
        (H.stageMetric first ((t : ℝ) - v ^ 2)).inner (f' ⟨first, le_rfl, hle⟩ x)
          (mfderiv ThreeModel ThreeModel (f' ⟨first, le_rfl, hle⟩) x w₁)
          (mfderiv ThreeModel ThreeModel (f' ⟨first, le_rfl, hle⟩) x w₂) := by
    intro x w₁ w₂
    rw [hSmetric ⟨first, haf, hle⟩ ((t : ℝ) - v ^ 2)
      ⟨by rw [ha]; linarith, by linarith [sq_nonneg v]⟩ hlower, localPullMetric_inner]
  have hiso := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S.base.metric ((t : ℝ) - v ^ 2)) (H.stageMetric first ((t : ℝ) - v ^ 2))
    (f' ⟨first, le_rfl, hle⟩) (hf' _) (hinj' _) hmet MeasurableSet.univ
  have hball : riemannianVolumeMeasure ThreeModel U (S.base.metric t) univ =
      riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier (H.stageMetric last t)
        (riemannianBallOf (H.stageMetric last t) (pU : (H.stageAt t).Carrier) r) := by
    have h : riemannianVolumeMeasure ThreeModel U ((H.stageMetric last t).restrictOpen U)
        (Subtype.val ⁻¹' (U : Set (H.stageAt t).Carrier)) =
          riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier (H.stageMetric last t) U :=
      Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset _ U
        U.isOpen.measurableSet subset_rfl
    rw [Subtype.coe_preimage_self] at h
    rw [hSt, h, hU]
  calc _ ≤ c * riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first ((t : ℝ) - v ^ 2))
          (H.historyLExp hle t v (pU : (H.stageAt t).Carrier) '' (Subtype.val ⁻¹'
            (H.historyMinDomain hle t B v (pU : (H.stageAt t).Carrier) ∩
              {Z | Real.sqrt ((H.stageMetric last t).inner (pU : (H.stageAt t).Carrier) Z Z) ≤
                R}))) :=
        setLIntegral_le_mul_of_forall_mem_le _ fun q hq => (hpt q hq).1
    _ ≤ c * riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first ((t : ℝ) - v ^ 2)) (f' ⟨first, le_rfl, hle⟩ '' univ) :=
        mul_le_mul' le_rfl (measure_mono fun q hq => (hpt q hq).2)
    _ = c * riemannianVolumeMeasure ThreeModel U (S.base.metric ((t : ℝ) - v ^ 2)) univ := by
        rw [hiso]
    _ ≤ c * (ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 3)) *
          riemannianVolumeMeasure ThreeModel U (S.base.metric t) univ) :=
        mul_le_mul' le_rfl hvol8
    _ = _ := by
        rw [hball, ← mul_assoc, hc, ← ENNReal.ofReal_mul (by positivity), hfin]
        congr 2
        rw [show Real.exp 36 = Real.exp 9 * Real.exp ((3 : ℝ) ^ 3) by
          rw [← Real.exp_add]; norm_num]
        ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
