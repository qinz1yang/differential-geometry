import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowDiscarding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability
import Mathlib.Topology.UniformSpace.OfCompactT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius

set_option autoImplicit false
noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

universe v

open DifferentialGeometry.Tensor0SBundle in
theorem ObservedHistory.exists_uniform_time_sum_stageRegularizedAction_gt_of_point_in_standard_cap_chart
    (Lambda B E C r : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hr : 0 < r) :
    ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ theta : ℝ, 0 ≤ theta → theta < 1 →
        ∃ eta q₀ : ℝ, 0 < eta ∧ 0 < q₀ ∧
      ∀ (X : Type v) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X]
        (H : ObservedHistory.{u}) (first control last : Fin (H.eventCount + 1))
        (hcontrol : control ≤ last)
        (f : (j : H.StageInterval control last) → X → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : control ≤ i.castSucc) (hl : i.succ ≤ last), ∀ x : X,
        (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) →
      ∀ (T R v τ : ℝ), 0 < τ → τ ≤ w₀ → τ ≤ R → τ ≤ v → v ≤ E →
      ∀ (j : H.StageInterval control last) (hfirst : first ≤ j.val)
        (S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed (T - R ^ 2) T (sub_le_self _ (sq_nonneg R)))),
      IsSolutionOn S → T ∈ Icc (H.time last) (H.stageEndTime last) →
      T - v ^ 2 ∈ H.stageDomain first → T - τ ^ 2 ∈ H.stageDomain j.val →
      (∀ k : H.StageInterval control last, ∀ t ∈ Ico (T - R ^ 2) T,
        t ∈ H.stageDomain k.val →
          S.base.metric t = localPullMetric (H.stageMetric k.val t) (f k) (hf k)) →
      (∀ t ∈ Icc (T - R ^ 2) T, ∀ x : X,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) →
      ∀ (K : Set X), IsCompact K → ∀ (xRecent : X), xRecent ∈ interior K →
      (∀ x ∈ frontier K,
        ENNReal.ofReal r ≤ riemannianEDistOf (S.base.metric T) xRecent x) →
      ∀ alpha : (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier,
      (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha k)) →
      (∀ k, IntervalIntegrable (H.stageRegularizedLagrangian k.val T (alpha k)) volume
        (H.regularizedStageStart T 0 k.val) (H.regularizedStageEnd T v k.val)) →
      (∀ k, ∀ t ∈ Ioo
        (H.regularizedStageStart T 0 k.val) (H.regularizedStageEnd T v k.val),
        -B ≤ metricScalarAt (H.stageMetric k.val (T - t ^ 2)) (alpha k t)) →
      alpha ⟨last, hfirst.trans j.property.2, le_rfl⟩ 0 =
        f ⟨last, hcontrol, le_rfl⟩ xRecent →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ (Q : StandardSolution) (U : TopologicalSpace.Opens ThreeSpace)
        (Phi : U → (H.stage j.val).Carrier)
        (hPhi : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Phi)
        (q z : ℝ) (hq : 0 < q), q₀ ≤ q → z ∈ Icc 0 theta →
      (∀ x : U, ∀ k : ℕ, k ≤ 2 →
        metricDerivNorm k (localPullMetric (scaleMetric q hq (H.stageMetric j.val (T - τ ^ 2)))
          Phi hPhi) ((Q.val.metric z).restrictOpen U) (StandardCap.metric.restrictOpen U) x ≤ eta) →
      alpha ⟨j.val, hfirst, j.property.2⟩ τ ∈ range Phi →
      Lambda < ∑ k : H.StageInterval first last, H.stageRegularizedAction k.val T (alpha k)
        (H.regularizedStageStart T 0 k.val) (H.regularizedStageEnd T v k.val) := by
  obtain ⟨w₀, hw₀, hterminal⟩ :=
    ObservedHistory.exists_uniform_time_sum_stageRegularizedAction_gt_of_point_outside_controlled_image
      Lambda B E C r hB hE hr
  refine ⟨w₀, hw₀, ?_⟩
  intro theta htheta htheta1
  obtain ⟨c, eta, hc, heta, hdisjoint⟩ :=
    exists_uniform_disjointness_of_standard_metric_approximation_of_curvature_bound
      theta htheta htheta1
  let q₀ := (9 * Real.sqrt C + 1) / c
  have hq₀ : 0 < q₀ := div_pos (by positivity) hc
  refine ⟨eta, q₀, heta, hq₀, ?_⟩
  intro X _ _ _ _ H first control last hcontrol f hf hinj hcross T R v τ hτ hτw hτR hτv hvE
    j hfirst S hS hupper hlower hphysical hmetric hRm K hK xRecent hxRecent hseparation
    alpha halpha hint hscalar hrecent hnode Q U Phi hPhi q z hq hscale hz hclose hpoint
  apply hterminal X H first control last hcontrol f hf hinj hcross T R v τ hτ hτw hτR hτv hvE
    j hfirst S hS hupper hlower hphysical hmetric hRm K hK xRecent hxRecent hseparation
    alpha halpha hint hscalar hrecent hnode
  have hlarge : 9 * Real.sqrt C < c * q := by
    have h := (div_le_iff₀ hc).mp hscale
    linarith
  have htime : T - τ ^ 2 ∈ Ico (T - R ^ 2) T :=
    ⟨sub_le_sub_left (pow_le_pow_left₀ hτ.le hτR 2) T,
      sub_lt_self T (sq_pos_of_pos hτ)⟩
  have hactual (y : (H.stage j.val).Carrier) (hy : y ∈ f j '' K) :
      normSq0S (H.stageMetric j.val (T - τ ^ 2)) y 4
        (metricRm04At (H.stageMetric j.val (T - τ ^ 2)) y) ≤ C := by
    obtain ⟨x, _, rfl⟩ := hy
    have h := hRm (T - τ ^ 2) ⟨htime.1, htime.2.le⟩ x
    change normSq0S (S.base.metric (T - τ ^ 2)) x 4
      (metricRm04At (S.base.metric (T - τ ^ 2)) x) ≤ C at h
    rwa [hmetric j _ htime hphysical, normSq0S_metricRm04At_localPullMetric] at h
  have hseparate := hdisjoint (H.stage j.val).Carrier (H.stageMetric j.val (T - τ ^ 2))
    q hq Q U Phi hPhi z hz hclose (f j '' K) C hlarge hactual
  exact fun hx => Set.disjoint_left.mp hseparate hpoint hx

theorem ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_of_confined_standard_approximation
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
        (hle : first ≤ last) (U : TopologicalSpace.Opens ThreeSpace)
        (f : (j : H.StageInterval first last) → U → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : U,
        (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ z)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ z)) →
      ∀ (Q : StandardSolution) (T b s q : ℝ) (hbs : b < s), s < T → ∀ (hq : 0 < q)
        (S : SolutionOn (I := ThreeModel) (M := U) (RealTimeInterval.closed b s hbs.le)),
      IsSolutionOn S → s ∈ Icc (H.time last) (H.stageEndTime last) →
      b ∈ H.stageDomain first → q * (s - b) ≤ theta →
      (∀ j : H.StageInterval first last,
        ∀ t ∈ Ioo (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
            (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val),
          S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2))
            (f j) (hf j)) →
      (∀ t ∈ Icc 0 (q * (s - b)), ∀ x : U, ∀ j : ℕ, j ≤ 2 →
        metricDerivNorm j (scaleMetric q hq (S.base.metric (b + t / q)))
          ((Q.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U) x ≤ eta) →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, MapsTo (alpha j)
        (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val)) (range (f j))) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast xRecent : U,
      alpha ⟨last, hle, le_rfl⟩ (Real.sqrt (T - s)) = f ⟨last, hle, le_rfl⟩ xRecent →
      alpha ⟨first, le_rfl, hle⟩ (Real.sqrt (T - b)) = f ⟨first, le_rfl, hle⟩ xPast →
      (q * (s - b) = theta ∨
        ENNReal.ofReal r ≤ riemannianEDistOf StandardCap.metric xPast.val xRecent.val) →
      Real.sqrt (T - s) * Lambda <
        ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (alpha j)
          (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hmodel⟩ :=
    exists_lRegularizedAction_lower_bound_of_rescaled_standard_metric_approximation.{0}
      (2 * Lambda) (by positivity)
  refine ⟨theta, r, eta, htheta, hr, heta, ?_⟩
  intro H first last hle U f hf hinj hcross Q T b s q hbs hsT hq S hS hs hb
    horizon hmetric hclose alpha halpha hstay hnode xPast xRecent hrecent hpast halt
  have hbounds : Real.sqrt (T - s) ≤ Real.sqrt (T - b) :=
    Real.sqrt_le_sqrt (sub_le_sub_left hbs.le T)
  have hsclock : T - Real.sqrt (T - s) ^ 2 = s := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ T - s)]
    ring
  have hbclock : T - Real.sqrt (T - b) ^ 2 = b := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ T - b)]
    ring
  have htime : ∀ t ∈ Icc (Real.sqrt (T - s)) (Real.sqrt (T - b)),
      T - t ^ 2 ∈ (RealTimeInterval.closed b s hbs.le).carrier := by
    intro t ht
    change T - t ^ 2 ∈ Icc b s
    have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans ht.1
    have hlo := (sq_le_sq₀ (Real.sqrt_nonneg (T - s)) ht0).mpr ht.1
    have hhi := (sq_le_sq₀ ht0 (Real.sqrt_nonneg (T - b))).mpr ht.2
    constructor <;> linarith
  have hepsilon : 0 < Real.sqrt (T - s) * Lambda :=
    mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hsT)) hLambda
  obtain ⟨gamma, hgamma, hstart, hend, haction⟩ :=
    H.exists_lRegularizedAction_lt_of_confined_history_curves first last hle
      f hf hinj hcross S hS T (Real.sqrt_nonneg _) hbounds
      (by rwa [hsclock]) (by rwa [hbclock]) htime hmetric alpha halpha hstay hnode hepsilon
  have hstart' : gamma (Real.sqrt (T - s)) = xRecent :=
    hinj ⟨last, hle, le_rfl⟩ (hstart.trans hrecent)
  have hend' : gamma (Real.sqrt (T - b)) = xPast :=
    hinj ⟨first, le_rfl, hle⟩ (hend.trans hpast)
  have hid : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (id : U → U) :=
    (Diffeomorph.refl ThreeModel U ∞).isLocalDiffeomorph
  have hpull (g : SmoothRiemannianMetric ThreeModel U) : localPullMetric g id hid = g := by
    ext x v w
    simp only [localPullMetric_inner, mfderiv_id, id_eq, ContinuousLinearMap.id_apply]
  have hint := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T (Real.sqrt (T - s)) (Real.sqrt (T - b)) hbounds
    gamma hgamma.contMDiffOn htime
  have hlarge := hmodel U _ S Q U id hid gamma T b s q hq hbs hsT horizon
    hgamma.contMDiffOn (by simpa only [Function.id_comp] using hint)
    (fun t ht j hj => by
      rw [hpull]
      exact hclose t ht _ j hj)
    (by simpa only [hstart', hend'] using halt)
  simp only [Function.id_comp] at hlarge
  linarith

theorem ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_on_cap_prefix
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
        (hle : first ≤ last) (D Rbirth Rball : ℝ), Rbirth + r ≤ Rball → Rball < D + 1 →
      ∀ (f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ x : standardCapWindow D, (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) →
      ∀ (Q : StandardSolution) (T b s q : ℝ) (hbs : b < s), s ≤ T → ∀ (hq : 0 < q)
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed b s hbs.le)),
      IsSolutionOn S → s ∈ Icc (H.time last) (H.stageEndTime last) →
      b ∈ H.stageDomain first → q * (s - b) ≤ theta →
      (∀ j : H.StageInterval first last, ∀ t ∈ Ico b s, t ∈ H.stageDomain j.val →
        S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) →
      (∀ t ∈ Icc 0 (q * (s - b)), ∀ x : standardCapWindow D, ∀ j : ℕ, j ≤ 2 →
        metricDerivNorm j (scaleMetric q hq (S.base.metric (b + t / q)))
          ((Q.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ eta) →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast : standardCapWindow D, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨first, le_rfl, hle⟩ (Real.sqrt (T - b)) = f ⟨first, le_rfl, hle⟩ xPast →
      (q * (s - b) = theta ∨ s = T ∨ ∃ j, ¬ MapsTo (alpha j)
        (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
        (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) →
      ∃ (last' : Fin (H.eventCount + 1)) (hfirst : first ≤ last') (hlast : last' ≤ last)
          (τ : ℝ) (xRecent : standardCapWindow D),
        τ ∈ Ico (Real.sqrt (T - s)) (Real.sqrt (T - b)) ∧
        T - τ ^ 2 ∈ Icc (H.time last') (H.stageEndTime last') ∧
        (∀ j : H.StageInterval first last',
          MapsTo (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (Icc (H.regularizedStageStart T τ j.val)
              (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
            (f ⟨j.val, j.property.1, j.property.2.trans hlast⟩ ''
              {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) ∧
        f ⟨last', hfirst, hlast⟩ xRecent = alpha ⟨last', hfirst, hlast⟩ τ ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last'),
          ∃ z : (H.event i).old,
            z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans (hl.trans hlast)⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl.trans hlast⟩
              (Real.sqrt (T - H.time i.succ))) ∧
        ((τ = Real.sqrt (T - s) ∧ last' = last ∧ (q * (s - b) = theta ∨ s = T) ∧
            ∀ j, MapsTo (alpha j)
              (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
                (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
              (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) ∨
          (Real.sqrt (T - s) < τ ∧
            xRecent ∈ frontier {x : standardCapWindow D | ‖x.val‖ ≤ Rball} ∧
            ‖xRecent.val‖ = Rball ∧ T - τ ^ 2 ∈ H.stageDomain last')) ∧
        (0 < τ → τ * Lambda < ∑ j : H.StageInterval first last',
          H.stageRegularizedAction j.val T
            (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (H.regularizedStageStart T τ j.val)
            (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val)) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hmodel⟩ :=
    ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_of_confined_standard_approximation
      Lambda hLambda
  refine ⟨theta, r, eta, htheta, hr, heta, ?_⟩
  intro H first last hle D Rbirth Rball hgap hfit f hf hinj hcross Q T b s q hbs hsT hq S hS
    hs hb hage hmetric hclose alpha halpha hnode xPast hnormPast hpast hstop
  classical
  by_cases hexit : ∃ j, ¬ MapsTo (alpha j)
      (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
        (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
      (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})
  · let K := {x : standardCapWindow D | ‖x.val‖ ≤ Rball}
    have hK : IsCompact K := StandardCap.isCompact_window_norm_le hfit
    have hnorm : Continuous (fun x : standardCapWindow D => ‖x.val‖) := continuous_subtype_val.norm
    have hclosed : IsClosed K := isClosed_le hnorm continuous_const
    have hinterior : {x : standardCapWindow D | ‖x.val‖ < Rball} ⊆ interior K :=
      interior_maximal (fun x hx => show ‖x.val‖ ≤ Rball from hx.le)
        (isOpen_lt hnorm continuous_const)
    have hpastK : xPast ∈ interior K := hinterior (by change ‖xPast.val‖ < Rball; linarith)
    have hfopen (j : H.StageInterval first last) : _root_.Topology.IsOpenEmbedding (f j) :=
      .of_continuous_injective_isOpenMap (hf j).contMDiff.continuous (hinj j) (hf j).isOpenMap
    have hstart : alpha ⟨first, le_rfl, hle⟩ (Real.sqrt (T - b)) ∈
        interior (f ⟨first, le_rfl, hle⟩ '' K) := by
      rw [hpast, ← DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding
        (hfopen ⟨first, le_rfl, hle⟩) K]
      exact ⟨xPast, hpastK, rfl⟩
    have hsclock : T - Real.sqrt (T - s) ^ 2 = s := by
      rw [Real.sq_sqrt (sub_nonneg.mpr hsT)]; ring
    have hbclock : T - Real.sqrt (T - b) ^ 2 = b := by
      rw [Real.sq_sqrt (sub_nonneg.mpr (hbs.le.trans hsT))]; ring
    have hclocks : Real.sqrt (T - s) ≤ Real.sqrt (T - b) :=
      Real.sqrt_le_sqrt (sub_le_sub_left hbs.le T)
    obtain ⟨last', hfirst, hlast, τ, yPast, xRecent, hτ, _, hxRecent, hphysical,
        hstay, hpast', hrecent, hnode'⟩ :=
      H.exists_confined_birth_prefix_of_nonconfinement first last hle f hfopen K hK
        (fun i hi hl x _ => hcross i hi hl x) (Real.sqrt_nonneg _) hclocks
        (by rwa [hsclock]) (by rwa [hbclock]) alpha
        (fun j => (halpha j).continuous.continuousOn) hstart hnode hexit
    have hyPast : yPast = xPast := hinj ⟨first, le_rfl, hle⟩ (hpast'.trans hpast)
    subst yPast
    have hnormRecent : ‖xRecent.val‖ = Rball := by
      have hleR : ‖xRecent.val‖ ≤ Rball := by
        change xRecent ∈ K
        rw [← hclosed.closure_eq]
        exact hxRecent.1
      exact le_antisymm hleR (le_of_not_gt (fun hlt => hxRecent.2 (hinterior hlt)))
    have hdist : ENNReal.ofReal r ≤
        riemannianEDistOf StandardCap.metric xPast.val xRecent.val := by
      apply (ENNReal.ofReal_le_ofReal (show r ≤ |‖xRecent.val‖ - ‖xPast.val‖| from ?_)).trans
        (StandardCap.radial_difference_le_edist xPast.val xRecent.val)
      rw [hnormRecent]
      have hdiff : r ≤ Rball - ‖xPast.val‖ := by linarith
      exact hdiff.trans (le_abs_self _)
    have hτpos : 0 < τ := (Real.sqrt_nonneg _).trans_lt hτ.1
    have hτsq : τ ^ 2 < (Real.sqrt (T - b)) ^ 2 :=
      (sq_lt_sq₀ hτpos.le (Real.sqrt_nonneg _)).mpr hτ.2
    have hbτ : b < T - τ ^ 2 := by linarith
    have hsτsq : (Real.sqrt (T - s)) ^ 2 < τ ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg _) hτpos.le).mpr hτ.1
    have hτs : T - τ ^ 2 < s := by linarith
    have hτT : T - τ ^ 2 < T := sub_lt_self T (sq_pos_of_pos hτpos)
    have hτclock : Real.sqrt (T - (T - τ ^ 2)) = τ := by
      rw [sub_sub_cancel, Real.sqrt_sq hτpos.le]
    let S' := S.timeRestrict (RealTimeInterval.closed b (T - τ ^ 2) hbτ.le)
    have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS
      (Icc_subset_Icc le_rfl hτs.le) (Ioo_subset_Ioo le_rfl hτs.le)
    let f' (j : H.StageInterval first last') := f ⟨j.val, j.property.1, j.property.2.trans hlast⟩
    let alpha' (j : H.StageInterval first last') := alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩
    have hbound := hmodel H first last' hfirst (standardCapWindow D) f'
      (fun j => hf ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
      (fun j => hinj ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
      (fun i hi hl => hcross i hi (hl.trans hlast)) Q T b (T - τ ^ 2) q hbτ hτT hq S' hS'
      ⟨H.time_le_of_mem_stageDomain hphysical, H.le_stageEndTime_of_mem_stageDomain hphysical⟩ hb
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right hτs.le b) hq.le).trans hage)
      ?_ ?_ alpha' (fun j => halpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
      ?_ hnode' xPast xRecent ?_ hpast'.symm (Or.inr hdist)
    · refine ⟨last', hfirst, hlast, τ, xRecent, ⟨hτ.1.le, hτ.2⟩,
        ⟨H.time_le_of_mem_stageDomain hphysical, H.le_stageEndTime_of_mem_stageDomain hphysical⟩,
        hstay, hrecent, hnode', Or.inr ⟨hτ.1, hxRecent, hnormRecent, hphysical⟩, ?_⟩
      intro hpositive
      simpa only [hτclock] using hbound
    · intro j t ht
      rw [hτclock] at ht
      have hb' := H.regularizedStage_bounds hτpos.le hτ.2.le
        ⟨H.time_le_of_mem_stageDomain hphysical, H.le_stageEndTime_of_mem_stageDomain hphysical⟩
        (by rwa [hbclock]) j
      have httau : τ < t := hb'.1.trans_lt ht.1
      have httop : t < Real.sqrt (T - b) := ht.2.trans_le hb'.2.2
      have ht0 : 0 ≤ t := hτpos.le.trans httau.le
      have htsq : τ ^ 2 < t ^ 2 := (sq_lt_sq₀ hτpos.le ht0).mpr httau
      have htop : t ^ 2 < (Real.sqrt (T - b)) ^ 2 :=
        (sq_lt_sq₀ ht0 (Real.sqrt_nonneg _)).mpr httop
      exact hmetric ⟨j.val, j.property.1, j.property.2.trans hlast⟩ (T - t ^ 2)
        ⟨by linarith, by linarith⟩
        (H.mapsTo_regularizedStage_Ioo T τ (Real.sqrt (T - b)) j.val ht)
    · intro t ht x j hj
      exact hclose t ⟨ht.1, ht.2.trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hτs.le b) hq.le)⟩ x j hj
    · intro j t ht
      rw [hτclock] at ht
      obtain ⟨x, _, hx⟩ := hstay j ht
      exact ⟨x, hx⟩
    · simpa only [hτclock] using hrecent.symm
  · have hfull : ∀ j, MapsTo (alpha j)
        (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
        (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball}) := by
      simpa only [not_exists, not_not] using hexit
    have hfullStop : q * (s - b) = theta ∨ s = T := by
      rcases hstop with hageEq | hterminal | hexit'
      · exact Or.inl hageEq
      · exact Or.inr hterminal
      · exact False.elim (hexit hexit')
    have hsclock : T - Real.sqrt (T - s) ^ 2 = s := by
      rw [Real.sq_sqrt (sub_nonneg.mpr hsT)]; ring
    have hbclock : T - Real.sqrt (T - b) ^ 2 = b := by
      rw [Real.sq_sqrt (sub_nonneg.mpr (hbs.le.trans hsT))]; ring
    have hclocks : Real.sqrt (T - s) < Real.sqrt (T - b) :=
      Real.sqrt_lt_sqrt (sub_nonneg.mpr hsT) (sub_lt_sub_left hbs T)
    have hupper : T - Real.sqrt (T - s) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
      rwa [hsclock]
    have hlower : T - Real.sqrt (T - b) ^ 2 ∈ H.stageDomain first := by rwa [hbclock]
    have hbLast := H.regularizedStage_bounds (Real.sqrt_nonneg _) hclocks.le hupper hlower
      (⟨last, hle, le_rfl⟩ : H.StageInterval first last)
    rw [H.regularizedStageStart_eq_of_mem_Icc (Real.sqrt_nonneg _) hupper] at hbLast
    obtain ⟨xRecent, _, hrecent⟩ := hfull ⟨last, hle, le_rfl⟩
      (show Real.sqrt (T - s) ∈ Icc
          (H.regularizedStageStart T (Real.sqrt (T - s)) last)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) last) from by
        rw [H.regularizedStageStart_eq_of_mem_Icc (Real.sqrt_nonneg _) hupper]
        exact ⟨le_rfl, hbLast.2.1⟩)
    refine ⟨last, hle, le_rfl, Real.sqrt (T - s), xRecent, ⟨le_rfl, hclocks⟩,
      hupper, hfull, hrecent, hnode, Or.inl ⟨rfl, rfl, hfullStop, hfull⟩, ?_⟩
    intro hpositive
    have hsT' : s < T := sub_pos.mp (Real.sqrt_pos.mp hpositive)
    have hageEq : q * (s - b) = theta := hfullStop.resolve_right (ne_of_lt hsT')
    apply hmodel H first last hle (standardCapWindow D) f hf hinj hcross Q T b s q hbs hsT'
      hq S hS hs hb hage ?_ hclose alpha halpha ?_ hnode xPast xRecent hrecent.symm hpast
      (Or.inl hageEq)
    · intro j t ht
      have hb' := H.regularizedStage_bounds (Real.sqrt_nonneg _) hclocks.le hupper hlower j
      have htl : Real.sqrt (T - s) < t := hb'.1.trans_lt ht.1
      have htr : t < Real.sqrt (T - b) := ht.2.trans_le hb'.2.2
      have ht0 : 0 ≤ t := (Real.sqrt_nonneg _).trans htl.le
      have hlo : (Real.sqrt (T - s)) ^ 2 < t ^ 2 :=
        (sq_lt_sq₀ (Real.sqrt_nonneg _) ht0).mpr htl
      have hhi : t ^ 2 < (Real.sqrt (T - b)) ^ 2 :=
        (sq_lt_sq₀ ht0 (Real.sqrt_nonneg _)).mpr htr
      exact hmetric j (T - t ^ 2) ⟨by linarith, by linarith⟩
        (H.mapsTo_regularizedStage_Ioo T (Real.sqrt (T - s)) (Real.sqrt (T - b)) j.val ht)
    · intro j t ht
      obtain ⟨x, _, hx⟩ := hfull j ht
      exact ⟨x, hx⟩

theorem ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_on_birth_prefix_of_leaves_cap_ball
    (Lambda : ℝ) (hLambda : 0 < Lambda) :
    ∃ theta r eta : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
        (hle : first ≤ last) (D Rbirth Rball : ℝ), Rbirth + r ≤ Rball → Rball < D + 1 →
      ∀ (f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ x : standardCapWindow D, (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) →
      ∀ (Q : StandardSolution) (T b s q : ℝ) (hbs : b < s), s ≤ T → ∀ (hq : 0 < q)
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed b s hbs.le)),
      IsSolutionOn S → s ∈ Icc (H.time last) (H.stageEndTime last) →
      b ∈ H.stageDomain first → q * (s - b) ≤ theta →
      (∀ j : H.StageInterval first last, ∀ t ∈ Ico b s, t ∈ H.stageDomain j.val →
        S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) →
      (∀ t ∈ Icc 0 (q * (s - b)), ∀ x : standardCapWindow D, ∀ j : ℕ, j ≤ 2 →
        metricDerivNorm j (scaleMetric q hq (S.base.metric (b + t / q)))
          ((Q.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ eta) →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast : standardCapWindow D, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨first, le_rfl, hle⟩ (Real.sqrt (T - b)) = f ⟨first, le_rfl, hle⟩ xPast →
      (∃ j, ¬ MapsTo (alpha j)
        (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
          (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
        (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) →
      ∃ (last' : Fin (H.eventCount + 1)) (hfirst : first ≤ last') (hlast : last' ≤ last)
          (τ : ℝ) (xRecent : standardCapWindow D),
        τ ∈ Ioo (Real.sqrt (T - s)) (Real.sqrt (T - b)) ∧
        xRecent ∈ frontier {x : standardCapWindow D | ‖x.val‖ ≤ Rball} ∧
        ‖xRecent.val‖ = Rball ∧ T - τ ^ 2 ∈ H.stageDomain last' ∧
        (∀ j : H.StageInterval first last',
          MapsTo (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (Icc (H.regularizedStageStart T τ j.val)
              (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
            (f ⟨j.val, j.property.1, j.property.2.trans hlast⟩ ''
              {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) ∧
        f ⟨last', hfirst, hlast⟩ xRecent = alpha ⟨last', hfirst, hlast⟩ τ ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last'),
          ∃ z : (H.event i).old,
            z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans (hl.trans hlast)⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl.trans hlast⟩
              (Real.sqrt (T - H.time i.succ))) ∧
        τ * Lambda < ∑ j : H.StageInterval first last',
          H.stageRegularizedAction j.val T
            (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (H.regularizedStageStart T τ j.val)
            (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hmodel⟩ :=
    ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_on_cap_prefix Lambda hLambda
  refine ⟨theta, r, eta, htheta, hr, heta, ?_⟩
  intro H first last hle D Rbirth Rball hgap hfit f hf hinj hcross Q T b s q hbs hsT hq S hS
    hs hb hage hmetric hclose alpha halpha hnode xPast hnormPast hpast hexit
  obtain ⟨last', hfirst, hlast, τ, xRecent, hτ, _, hstay, hrecent, hnode', halt, hbound⟩ :=
    hmodel H first last hle D Rbirth Rball hgap hfit f hf hinj hcross Q T b s q hbs hsT hq S hS
      hs hb hage hmetric hclose alpha halpha hnode xPast hnormPast hpast (Or.inr (Or.inr hexit))
  rcases halt with hfull | ⟨huτ, hfrontier, hnorm, hphysical⟩
  · obtain ⟨j, hj⟩ := hexit
    exact False.elim (hj (hfull.2.2.2 j))
  · exact ⟨last', hfirst, hlast, τ, xRecent, ⟨huτ, hτ.2⟩, hfrontier, hnorm, hphysical,
      hstay, hrecent, hnode', hbound ((Real.sqrt_nonneg _).trans_lt huτ)⟩

private theorem ObservedHistory.exists_confined_point_before_terminal_face
    (H : ObservedHistory.{u}) {X : Type v}
    (first last : Fin (H.eventCount + 1))
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier) (K : Set X)
    {T u v w : ℝ} (hu : 0 ≤ u) (huv : u < v) (huw : u < w)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hstay : ∀ j, MapsTo (alpha j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) (f j '' K)) :
    ∃ (τ : ℝ) (j : H.StageInterval first last),
      τ ∈ Ioo u (min w v) ∧ T - τ ^ 2 ∈ H.stageDomain j.val ∧ alpha j τ ∈ f j '' K := by
  obtain ⟨τ, huτ, hτwv⟩ := exists_between (lt_min huw huv)
  have hτv : τ < v := hτwv.trans_le (min_le_right w v)
  have hτ0 : 0 ≤ τ := hu.trans huτ.le
  have hv0 : 0 ≤ v := hu.trans huv.le
  have huτsq : u ^ 2 < τ ^ 2 := (sq_lt_sq₀ hu hτ0).mpr huτ
  have hτvsq : τ ^ 2 < v ^ 2 := (sq_lt_sq₀ hτ0 hv0).mpr hτv
  have hphysicalPast : T - v ^ 2 < T - τ ^ 2 := by linarith
  have hphysicalRecent : T - τ ^ 2 < T - u ^ 2 := by linarith
  let tH : Icc (0 : ℝ) H.horizon :=
    ⟨T - τ ^ 2, (H.stageDomain_subset first hlower).1.trans hphysicalPast.le,
      hphysicalRecent.le.trans (hupper.2.trans (H.stageEndTime_le_horizon last))⟩
  have hfirst : first ≤ H.activeStage tH :=
    H.le_activeStage tH first ((H.time_le_of_mem_stageDomain hlower).trans hphysicalPast.le)
  have hlast : H.activeStage tH ≤ last := by
    cases last using Fin.lastCases with
    | last => exact Fin.le_last _
    | cast i =>
      by_contra hn
      have hi : i.succ ≤ H.activeStage tH := by
        have hh := lt_of_not_ge hn
        change i.val + 1 ≤ (H.activeStage tH).val
        exact hh
      have hh := (H.time_strictMono.monotone hi).trans (H.activeStage_time_le tH)
      rw [H.stageEndTime_castSucc] at hupper
      change H.time i.succ ≤ T - τ ^ 2 at hh
      linarith [hupper.2]
  let j : H.StageInterval first last := ⟨H.activeStage tH, hfirst, hlast⟩
  have hphysical : T - τ ^ 2 ∈ H.stageDomain j.val := H.activeStage_mem tH
  refine ⟨τ, j, ⟨huτ, hτwv⟩, hphysical, hstay j ?_⟩
  have hmin : T - τ ^ 2 ≤ min (T - u ^ 2) (H.stageEndTime j.val) :=
    le_min hphysicalRecent.le (H.le_stageEndTime_of_mem_stageDomain hphysical)
  have hmax : max (T - v ^ 2) (H.time j.val) ≤ T - τ ^ 2 :=
    max_le hphysicalPast.le (H.time_le_of_mem_stageDomain hphysical)
  constructor
  · change Real.sqrt (T - min (T - u ^ 2) (H.stageEndTime j.val)) ≤ τ
    exact (Real.sqrt_le_sqrt (by linarith : T - min (T - u ^ 2) (H.stageEndTime j.val) ≤ τ ^ 2)).trans_eq
      (Real.sqrt_sq hτ0)
  · change τ ≤ Real.sqrt (T - max (T - v ^ 2) (H.time j.val))
    rw [← Real.sqrt_sq hτ0]
    exact Real.sqrt_le_sqrt (by linarith)

open DifferentialGeometry.Tensor0SBundle in
theorem ObservedHistory.exists_uniform_sum_stageRegularizedAction_gt_of_cap_prefix_near_controlled_terminal_region
    (A B E C rho R : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ theta r eta q₀ : ℝ,
      theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < eta ∧ 0 < q₀ ∧
      ∀ (X : Type v) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X]
        (H : ObservedHistory.{u}) (first capFirst capLast control last : Fin (H.eventCount + 1))
        (hfirst : first ≤ capFirst) (hcap : capFirst ≤ capLast) (hlast : capLast ≤ last)
        (hcontrol : control ≤ last)
        (f : (j : H.StageInterval control last) → X → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : control ≤ i.castSucc) (hl : i.succ ≤ last), ∀ x : X,
        (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) →
      ∀ (T v : ℝ), 0 ≤ v → v ≤ E →
      ∀ (S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed (T - R ^ 2) T (sub_le_self _ (sq_nonneg R)))),
      IsSolutionOn S → T ∈ Icc (H.time last) (H.stageEndTime last) →
      T - v ^ 2 ∈ H.stageDomain first → T - R ^ 2 ∈ H.stageDomain control →
      (∀ j : H.StageInterval control last, ∀ t ∈ Ico (T - R ^ 2) T,
        t ∈ H.stageDomain j.val →
          S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) →
      (∀ t ∈ Icc (T - R ^ 2) T, ∀ x : X,
        normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C) →
      ∀ (K : Set X), IsCompact K → ∀ (xRecent : X), xRecent ∈ interior K →
      (∀ x ∈ frontier K,
        ENNReal.ofReal rho ≤ riemannianEDistOf (S.base.metric T) xRecent x) →
      ∀ (D Rbirth Rball : ℝ), Rbirth + r ≤ Rball → Rball < D + 1 →
      ∀ (g : (j : H.StageInterval capFirst capLast) → standardCapWindow D → (H.stage j.val).Carrier)
        (hg : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (g j)),
      (∀ j, Function.Injective (g j)) →
      (∀ (i : Fin H.eventCount) (hi : capFirst ≤ i.castSucc) (hl : i.succ ≤ capLast),
        ∀ x : standardCapWindow D, (H.event i).RegularCrossing
          (g ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
          (g ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) →
      ∀ (Q : StandardSolution) (b s q : ℝ) (hbs : b < s), s ≤ T → T - v ^ 2 ≤ b →
      ∀ (hq : 0 < q), q₀ ≤ q →
      ∀ (Scap : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed b s hbs.le)),
      IsSolutionOn Scap → s ∈ Icc (H.time capLast) (H.stageEndTime capLast) →
      b ∈ H.stageDomain capFirst → q * (s - b) ≤ theta →
      (∀ j : H.StageInterval capFirst capLast, ∀ t ∈ Ico b s, t ∈ H.stageDomain j.val →
        Scap.base.metric t = localPullMetric (H.stageMetric j.val t) (g j) (hg j)) →
      (∀ t ∈ Icc 0 (q * (s - b)), ∀ x : standardCapWindow D, ∀ k : ℕ, k ≤ 2 →
        metricDerivNorm k (scaleMetric q hq (Scap.base.metric (b + t / q)))
          ((Q.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ eta) →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      (∀ j, ∀ t ∈ Ioo
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (alpha j t)) →
      alpha ⟨last, hfirst.trans (hcap.trans hlast), le_rfl⟩ 0 =
        f ⟨last, hcontrol, le_rfl⟩ xRecent →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast : standardCapWindow D, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨capFirst, hfirst, hcap.trans hlast⟩ (Real.sqrt (T - b)) =
        g ⟨capFirst, le_rfl, hcap⟩ xPast →
      (q * (s - b) = theta ∨ s = T ∨ ∃ j : H.StageInterval capFirst capLast,
        ¬ MapsTo (alpha ⟨j.val, hfirst.trans j.property.1, j.property.2.trans hlast⟩)
          (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
            (H.regularizedStageEnd T (Real.sqrt (T - b)) j.val))
          (g j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) →
      A < ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (alpha j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
  obtain ⟨wFast, hwFast, hpoint⟩ :=
    ObservedHistory.exists_uniform_time_sum_stageRegularizedAction_gt_of_point_in_standard_cap_chart A B E C rho hB hE hrho
  let w := min wFast R
  have hw : 0 < w := lt_min hwFast hR
  let F := (2 * B / 3) * E ^ 3
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let L := (max A 0 + F + 1) / w
  have hL : 0 < L := div_pos (by positivity) hw
  obtain ⟨theta, r, etaCap, htheta, hr, hetaCap, hcapAction⟩ :=
    ObservedHistory.exists_uniform_lRegularizedAction_lower_bound_on_cap_prefix L hL
  obtain ⟨etaPoint, q₀, hetaPoint, hq₀, hfast⟩ := hpoint theta htheta.1.le htheta.2
  refine ⟨theta, r, min etaCap etaPoint, q₀, htheta, hr, lt_min hetaCap hetaPoint, hq₀, ?_⟩
  intro X _ _ _ _ H first capFirst capLast control last hfirst hcap hlast hcontrol f hf hinj hcross
    T v hv hvE S hS hupper hlower hcontrolled hmetric hRm K hK xRecent hxRecent hseparation
    D Rbirth Rball hgap hfit g hg ginj gcross Q b s q hbs hsT hstart hq hqmin Scap hScap
    hs hb hage hcapMetric hclose alpha halpha hint hscalar hrecent hnode xPast hnormPast hpast hstop
  let beta (j : H.StageInterval capFirst capLast) :=
    alpha ⟨j.val, hfirst.trans j.property.1, j.property.2.trans hlast⟩
  have hcloseCap : ∀ t ∈ Icc 0 (q * (s - b)), ∀ x : standardCapWindow D, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (scaleMetric q hq (Scap.base.metric (b + t / q)))
        ((Q.val.metric t).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ etaCap :=
    fun t ht x k hk => (hclose t ht x k hk).trans (min_le_left _ _)
  obtain ⟨j, hjfirst, hjlast, τ, _, hτ, hphysical, hstay, _, _, _, haction⟩ :=
    hcapAction H capFirst capLast hcap D Rbirth Rball hgap hfit g hg ginj gcross Q T b s q hbs hsT
      hq Scap hScap hs hb hage hcapMetric hcloseCap beta
      (fun j => halpha ⟨j.val, hfirst.trans j.property.1, j.property.2.trans hlast⟩)
      (fun i hi hl => hnode i (hfirst.trans hi) (hl.trans hlast)) xPast hnormPast hpast hstop
  have hτ0 : 0 ≤ τ := (Real.sqrt_nonneg _).trans hτ.1
  have hbclock : T - Real.sqrt (T - b) ^ 2 = b := by
    rw [Real.sq_sqrt (sub_nonneg.mpr (hbs.le.trans hsT))]; ring
  have hsclock : T - Real.sqrt (T - s) ^ 2 = s := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hsT)]; ring
  have hvCap : Real.sqrt (T - b) ≤ v := by
    calc
      Real.sqrt (T - b) ≤ Real.sqrt (v ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = v := Real.sqrt_sq hv
  by_cases hτw : τ < w
  · let g' (k : H.StageInterval capFirst j) :=
      g ⟨k.val, k.property.1, k.property.2.trans hjlast⟩
    let beta' (k : H.StageInterval capFirst j) :=
      beta ⟨k.val, k.property.1, k.property.2.trans hjlast⟩
    obtain ⟨σ, k, hσ, hσphysical, hσin⟩ :=
      H.exists_confined_point_before_terminal_face capFirst j g'
        {x : standardCapWindow D | ‖x.val‖ ≤ Rball} hτ0 hτ.2 hτw hphysical
        (by rwa [hbclock]) beta' hstay
    have hσpos : 0 < σ := hτ0.trans_lt hσ.1
    have hσw : σ < w := hσ.2.trans_le (min_le_left _ _)
    have hσR : σ ≤ R := hσw.le.trans (min_le_right _ _)
    have hσCap : σ < Real.sqrt (T - b) := hσ.2.trans_le (min_le_right _ _)
    have huσ : Real.sqrt (T - s) < σ := hτ.1.trans_lt hσ.1
    have hσsq := (sq_lt_sq₀ hσpos.le (Real.sqrt_nonneg (T - b))).mpr hσCap
    have hsqσ := (sq_lt_sq₀ (Real.sqrt_nonneg (T - s)) hσpos.le).mpr huσ
    have htcap : T - σ ^ 2 ∈ Ico b s := ⟨by linarith, by linarith⟩
    have htR : T - R ^ 2 ≤ T - σ ^ 2 :=
      sub_le_sub_left (pow_le_pow_left₀ hσpos.le hσR 2) T
    let tH : Icc (0 : ℝ) H.horizon := ⟨T - σ ^ 2, H.stageDomain_subset k.val hσphysical⟩
    have hkcontrol : control ≤ k.val := by
      have h := H.le_activeStage tH control ((H.time_le_of_mem_stageDomain hcontrolled).trans htR)
      rwa [(H.mem_stageDomain_iff tH k.val).mp hσphysical] at h
    let kTerminal : H.StageInterval control last :=
      ⟨k.val, hkcontrol, k.property.2.trans (hjlast.trans hlast)⟩
    let kCap : H.StageInterval capFirst capLast := ⟨k.val, k.property.1, k.property.2.trans hjlast⟩
    let z := q * (T - σ ^ 2 - b)
    have hz : z ∈ Icc 0 (q * (s - b)) :=
      ⟨mul_nonneg hq.le (sub_nonneg.mpr htcap.1),
        mul_le_mul_of_nonneg_left (sub_le_sub_right htcap.2.le b) hq.le⟩
    have htime : b + z / q = T - σ ^ 2 := by dsimp [z]; field_simp; ring
    apply hfast X H first control last hcontrol f hf hinj hcross T R v σ hσpos
      (hσw.le.trans (min_le_left _ _)) hσR (hσCap.le.trans hvCap) hvE kTerminal
      (hfirst.trans k.property.1) S hS hupper hlower hσphysical hmetric hRm K hK
      xRecent hxRecent hseparation alpha halpha hint hscalar hrecent hnode
      Q (standardCapWindow D) (g kCap) (hg kCap) q z hq hqmin ⟨hz.1, hz.2.trans hage⟩
    · intro x m hm
      have h := (hclose z hz x m hm).trans (min_le_right _ _)
      rwa [htime, hcapMetric kCap _ htcap hσphysical, ← localPullMetric_scaleMetric] at h
    · obtain ⟨x, _, hx⟩ := hσin
      exact ⟨x, hx⟩
  · have hwτ : w ≤ τ := le_of_not_gt hτw
    have hτpos : 0 < τ := hw.trans_le hwτ
    have haction := haction hτpos
    have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupper
    have haccount := H.sum_stageRegularizedAction_subinterval_le_of_scalar_lower_bound
      hfirst hjfirst (hjlast.trans hlast) le_rfl hτpos.le hτ.2.le hvCap hupper0 hlower
      hphysical
      (by rwa [hbclock]) alpha hint hscalar
    have hτ3 : τ ^ 3 ≤ (Real.sqrt (T - b)) ^ 3 := pow_le_pow_left₀ hτpos.le hτ.2.le 3
    have hv3 : v ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hv hvE 3
    have hcost : (2 * B / 3) * ((v ^ 3 - (0 : ℝ) ^ 3) -
        ((Real.sqrt (T - b)) ^ 3 - τ ^ 3)) ≤ F := by
      apply (mul_le_mul_of_nonneg_left (show (v ^ 3 - (0 : ℝ) ^ 3) -
          ((Real.sqrt (T - b)) ^ 3 - τ ^ 3) ≤ E ^ 3 from by linarith) (by positivity)).trans_eq
      rfl
    have hLbound : max A 0 + F + 1 ≤ τ * L := by
      calc
        max A 0 + F + 1 = w * L := by dsimp [L]; field_simp
        _ ≤ τ * L := mul_le_mul_of_nonneg_right hwτ hL.le
    change τ * L < _ at haction
    dsimp only [beta] at haction
    linarith [le_max_left A 0]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

theorem exists_uniform_prepared_cap_prefix_alternative_of_backward_trace
    (Lambda : ℝ) (C : ℝ≥0) (hLambda : 0 < Lambda) :
    ∃ theta r Cbirth : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < Cbirth ∧
      ∀ {E : Type uE} {H₀ : Type uH} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H₀] {I : ModelWithCorners ℝ E H₀} [I.Boundaryless],
      ∀ (D : ℝ) (hD : 0 < D),
      ∃ R : ℝ, ∃ hDR : D + 1 < R, ∃ m₀ : ℕ, 4 ≤ m₀ ∧
      ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {M : Type uM} [TopologicalSpace M] [ChartedSpace H₀ M]
        [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A}
        {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hR : R ≤ Dbig), m₀ ≤ m → ζ ≤ ζ₀ →
      let hDD : D ≤ Dbig := by linarith;
      let inc : standardCapWindow D → standardCapWindow Dbig :=
        TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)));
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      (∀ t ∈ Ico (H.time last) s, G.flow.base.metric t = H.stageMetric last t) →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ theta →
      ∀ (z : standardCapWindow D) (x : (H.stage last).Carrier)
        (Atrace : BackwardPointTrace H first last hle x),
        Atrace.point first le_rfl hle = Jbig (inc z) →
    ∃ f : (j : H.StageInterval first last) → standardCapWindow D → (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ j, Function.Injective (f j)) ∧
        f ⟨first, le_rfl, hle⟩ = Jbig ∘ inc ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∀ y : standardCapWindow D,
            (H.event i).RegularCrossing
              (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ y)
              (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ y)) ∧
        f ⟨last, hle, le_rfl⟩ z = x ∧
      ∀ (T Rbirth Rball : ℝ), s ≤ T → s ≤ H.stageEndTime last →
        Rbirth + r ≤ Rball → Rball < D + 1 →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ w : (H.event i).old,
            w.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput w = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast : standardCapWindow D, ‖xPast.val‖ ≤ Rbirth →
        alpha ⟨first, le_rfl, hle⟩ (Real.sqrt (T - H.time first)) = Jbig (inc xPast) →
        (q * (s - H.time first) < theta ∧ s < T ∧
          ∀ j, MapsTo (alpha j)
            (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
              (H.regularizedStageEnd T (Real.sqrt (T - H.time first)) j.val))
            (f j '' {y : standardCapWindow D | ‖y.val‖ ≤ Rball})) ∨
      ∃ (last' : Fin (H.eventCount + 1)) (hfirst : first ≤ last') (hlast : last' ≤ last)
          (τ : ℝ) (xRecent : standardCapWindow D),
        τ ∈ Ico (Real.sqrt (T - s)) (Real.sqrt (T - H.time first)) ∧
        T - τ ^ 2 ∈ Icc (H.time last') (H.stageEndTime last') ∧
        (∀ j : H.StageInterval first last',
          MapsTo (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (Icc (H.regularizedStageStart T τ j.val)
              (H.regularizedStageEnd T (Real.sqrt (T - H.time first)) j.val))
            (f ⟨j.val, j.property.1, j.property.2.trans hlast⟩ ''
              {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) ∧
        f ⟨last', hfirst, hlast⟩ xRecent = alpha ⟨last', hfirst, hlast⟩ τ ∧
        (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last'),
          ∃ z : (H.event i).old,
            z.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans (hl.trans hlast)⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl.trans hlast⟩
              (Real.sqrt (T - H.time i.succ))) ∧
        ((τ = Real.sqrt (T - s) ∧ last' = last ∧ (q * (s - H.time first) = theta ∨ s = T) ∧
            ∀ j, MapsTo (alpha j)
              (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
                (H.regularizedStageEnd T (Real.sqrt (T - H.time first)) j.val))
              (f j '' {x : standardCapWindow D | ‖x.val‖ ≤ Rball})) ∨
          (Real.sqrt (T - s) < τ ∧
            xRecent ∈ frontier {x : standardCapWindow D | ‖x.val‖ ≤ Rball} ∧
            ‖xRecent.val‖ = Rball ∧ T - τ ^ 2 ∈ H.stageDomain last')) ∧
        (0 < τ → τ * Lambda < ∑ j : H.StageInterval first last',
          H.stageRegularizedAction j.val T
            (alpha ⟨j.val, j.property.1, j.property.2.trans hlast⟩)
            (H.regularizedStageStart T τ j.val)
            (H.regularizedStageEnd T (Real.sqrt (T - H.time first)) j.val)) := by
  obtain ⟨theta, r, eta, htheta, hr, heta, hprefix⟩ :=
    exists_uniform_lRegularizedAction_lower_bound_on_cap_prefix Lambda hLambda
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindow⟩ :=
    exists_uniform_prepared_cap_common_flow_of_backward_trace.{u, uE, uH, uM}
      theta C htheta.1 htheta.2
  refine ⟨theta, r, Cbirth, htheta, hr, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ D hD
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ :=
    hwindow (I := I) D 1 eta hD zero_lt_one heta 2
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hR hm hζ hDD inc
    H first last hle s G L hG Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  obtain ⟨f, hf, hinj, hbirth, hcross, S, hS, hstage, hcurv, Φ, hΦ, hΦval, hmarked,
      hterminal, Q, hQ, hclose⟩ :=
    hwindow w hR hm hζ H first last hle s G L hG Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q
      haq hzero parameters records hfixed hlower hdelta hderiv hfinal htime z x Atrace hanchor
  refine ⟨f, hf, hinj, hbirth, hcross, ?_, ?_⟩
  · exact (congrFun hΦval z).symm.trans hmarked
  intro T Rbirth Rball hsT hsEnd hgap hfit alpha halpha hnode xPast hnormPast hpast
  by_cases hstop : q * (s - H.time first) = theta ∨ s = T ∨ ∃ j, ¬ MapsTo (alpha j)
      (Icc (H.regularizedStageStart T (Real.sqrt (T - s)) j.val)
        (H.regularizedStageEnd T (Real.sqrt (T - H.time first)) j.val))
      (f j '' {y : standardCapWindow D | ‖y.val‖ ≤ Rball})
  · right
    have hbs : H.time first < s := (H.time_strictMono.monotone hle).trans_lt G.lt
    exact hprefix H first last hle D Rbirth Rball hgap hfit f hf hinj hcross Q T
      (H.time first) s q hbs hsT hq S hS ⟨G.lt.le, hsEnd⟩ (H.time_mem_stageDomain first)
      htime (fun j t ht hdomain => hstage j t hdomain ht.2)
      (fun t ht y j hj => ((hclose t ht).2 j hj y).le) alpha halpha hnode xPast hnormPast
      (by rw [hbirth]; exact hpast) hstop
  · left
    refine ⟨lt_of_le_of_ne htime (fun h => hstop (Or.inl h)),
      lt_of_le_of_ne hsT (fun h => hstop (Or.inr (Or.inl h))), ?_⟩
    intro j
    by_contra hbad
    exact hstop (Or.inr (Or.inr ⟨j, hbad⟩))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM v

open DifferentialGeometry.Tensor0SBundle in
theorem exists_uniform_prepared_discard_action_lower_bound
    (A B Ebound Ccurv rho Rcontrol : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrho : 0 < rho) (hRcontrol : 0 < Rcontrol) :
    ∃ theta r qmin Cbirth : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < qmin ∧ 0 < Cbirth ∧
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
        (w : StandardCap.CanonicalStaticInsertionWitness d A₀ hA Dbig m ζ),
        R ≤ Dbig → m₀ ≤ m → ζ ≤ ζ₀ →
      ∀ (H : ObservedHistory.{u}) (capFirst lossLast : Fin (H.eventCount + 1)) (hcapLoss : capFirst ≤ lossLast),
      ∀ (Jbig : standardCapWindow Dbig → (H.stage capFirst).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric capFirst).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ lossLast → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ lossLast →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            Cderiv * (H.event j).incoming.flow.scalar t x ^ 2) →
      q * (H.time lossLast - H.time capFirst) ≤ theta →
      (¬ Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
        range (H.backwardSurvivorMap capFirst lossLast hcapLoss capFirst le_rfl hcapLoss)) →
      qmin ≤ q →
      ∀ (X : Type v) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X]
        (first control last : Fin (H.eventCount + 1))
        (hfirst : first ≤ capFirst) (hlast : lossLast ≤ last) (hcontrol : control ≤ last)
        (f : (j : H.StageInterval control last) → X → (H.stage j.val).Carrier)
        (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Function.Injective (f j)) →
      (∀ (i : Fin H.eventCount) (hi : control ≤ i.castSucc) (hl : i.succ ≤ last), ∀ y : X,
        (H.event i).RegularCrossing
          (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ y)
          (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ y)) →
      ∀ (T v : ℝ), 0 ≤ v → v ≤ Ebound →
      ∀ (S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed (T - Rcontrol ^ 2) T (sub_le_self _ (sq_nonneg Rcontrol)))),
      IsSolutionOn S → T ∈ Icc (H.time last) (H.stageEndTime last) →
      T - v ^ 2 ∈ H.stageDomain first → T - Rcontrol ^ 2 ∈ H.stageDomain control →
      (∀ j : H.StageInterval control last, ∀ t ∈ Ico (T - Rcontrol ^ 2) T,
        t ∈ H.stageDomain j.val →
          S.base.metric t = localPullMetric (H.stageMetric j.val t) (f j) (hf j)) →
      (∀ t ∈ Icc (T - Rcontrol ^ 2) T, ∀ y : X,
        normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ Ccurv) →
      ∀ (K : Set X), IsCompact K → ∀ (xRecent : X), xRecent ∈ interior K →
      (∀ y ∈ frontier K,
        ENNReal.ofReal rho ≤ riemannianEDistOf (S.base.metric T) xRecent y) →
      T - v ^ 2 ≤ H.time capFirst →
      ∀ alpha : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      (∀ j, ∀ t ∈ Ioo
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) (alpha j t)) →
      alpha ⟨last, hfirst.trans (hcapLoss.trans hlast), le_rfl⟩ 0 =
        f ⟨last, hcontrol, le_rfl⟩ xRecent →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) →
      ∀ xPast : standardCapWindow Dbig, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨capFirst, hfirst, hcapLoss.trans hlast⟩ (Real.sqrt (T - H.time capFirst)) = Jbig xPast →
      A < ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (alpha j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
  obtain ⟨theta, r, eta, qmin, htheta, hr, heta, hqmin, haction⟩ :=
    exists_uniform_sum_stageRegularizedAction_gt_of_cap_prefix_near_controlled_terminal_region
      A B Ebound Ccurv rho Rcontrol hB hEbound hrho hRcontrol
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hdiscard⟩ :=
    exists_uniform_first_cap_discarding_event_of_not_surviving.{u, uE, uH, uM}
      theta Cderiv htheta.1 htheta.2
  refine ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ Rbirth a
  have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
  have hgap : Rbirth + r ≤ a := le_max_right _ _
  obtain ⟨D, hD, haD, _, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hdiscard⟩ :=
    hdiscard (I := I) a 0 eta ha heta 2
  refine ⟨D, hD, haD, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A₀ hA₀ Dbig m ζ w hR hm hζ
    H capFirst lossLast hcapLoss Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv htime hnot hqscale
  have hDD : D ≤ Dbig := by linarith
  let inc : standardCapWindow D → standardCapWindow Dbig :=
    TopologicalSpace.Opens.inclusion (fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)))
  obtain ⟨i, hfi, hiloss, hpast, Ξ, hΞs, hbirth, hΞ, gflow, F, hslabs, hlastFlow,
    hF, hFzero, hFmetric, hgram, hcurv, hdiscarded, Q, hQ, hclose⟩ :=
    hdiscard w hR hm hζ H capFirst lossLast hcapLoss Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq
      hzero parameters records hfixed hlower hdelta hderiv htime hnot
  have hG : ∀ t ∈ Ico (H.time i.castSucc) (H.time i.succ),
      (H.event i).incoming.flow.base.metric t = H.stageMetric i.castSucc t := by
    intro t _
    simp only [stageMetric, Fin.lastCases_castSucc]
  obtain ⟨gcap, hgcap, hcapinj, hcapbirth, hcapcross, Scap, hScap, hcapmetric,
      hnormalized, Φ, hΦ, hΦval, hΦeq, hterminal⟩ :=
    exists_common_flow_of_normalized_incoming_window H capFirst i.castSucc hfi
      (H.time i.succ) (H.event i).incoming (H.event i).terminal hG hq (Jbig ∘ inc)
      Ξ hΞs hΞ hbirth gflow hslabs hlastFlow F hFmetric
  have hdisjoint : Disjoint (gcap ⟨i.castSucc, hfi, le_rfl⟩ ''
      {y : standardCapWindow D | ‖y.val‖ ≤ a})
      (range (fun y : (H.event i).old => y.val.val)) := by
    apply (H.event i).disjoint_old_image_of_discarded_core
    intro y hy
    obtain ⟨z, hz, dd, hdd⟩ := hdiscarded y hy
    refine ⟨z, ?_, dd, hdd⟩
    have hp := congrFun hΦval y
    rw [hΦeq] at hp
    exact hz.trans hp
  intro X _ _ _ _ first control last hfirst hlast hcontrol f hf hinj hcross
    T v hv hvE S hS hupper hlowerPath hcontrolled hmetric hRm K hK xRecent hxRecent hseparation
    hstart alpha halpha hint hscalar hrecent hnode xPast hnormPast hbirthPath
  have hilast : i.succ ≤ last := hiloss.trans hlast
  have hcaplast : i.castSucc ≤ last := i.castSucc_lt_succ.le.trans hilast
  have heventT : H.time i.succ ≤ T := (H.time_strictMono.monotone hilast).trans hupper.1
  have hbs : H.time capFirst < H.time i.succ := H.time_strictMono (hfi.trans_lt i.castSucc_lt_succ)
  let xPastD : standardCapWindow D := ⟨xPast.val, by
    change ‖xPast.val‖ < D + 1
    linarith⟩
  have hincPast : inc xPastD = xPast := Subtype.ext rfl
  apply haction X H first capFirst i.castSucc control last hfirst hfi hcaplast hcontrol
    f hf hinj hcross T v hv hvE S hS hupper hlowerPath hcontrolled hmetric hRm K hK xRecent hxRecent
    hseparation D Rbirth a hgap (by linarith) gcap hgcap hcapinj hcapcross Q
    (H.time capFirst) (H.time i.succ) q hbs heventT hstart hq hqscale Scap hScap
    (by rw [H.stageEndTime_castSucc]; exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
    (H.time_mem_stageDomain capFirst)
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hiloss) _) hq.le).trans htime)
    (fun j t ht hdomain => hcapmetric j t hdomain ht.2)
    (fun t ht y j hj => by rw [hnormalized t ht]; exact ((hclose t ht).2 j hj y).le)
    alpha halpha hint hscalar hrecent hnode xPastD hnormPast ?_ ?_
  · rw [hcapbirth, Function.comp_apply, hincPast]
    exact hbirthPath
  · right
    right
    refine ⟨⟨i.castSucc, hfi, le_rfl⟩, ?_⟩
    intro hstay
    have hclock : H.regularizedStageStart T (Real.sqrt (T - H.time i.succ)) i.castSucc =
        Real.sqrt (T - H.time i.succ) := by
      apply H.regularizedStageStart_eq_of_mem_Icc (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt (sub_nonneg.mpr heventT), sub_sub_cancel, H.stageEndTime_castSucc]
      exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
    have hbounds := H.regularizedStage_bounds (Real.sqrt_nonneg (T - H.time i.succ))
      (Real.sqrt_le_sqrt (sub_le_sub_left hbs.le T))
      (show T - Real.sqrt (T - H.time i.succ) ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) by
        rw [Real.sq_sqrt (sub_nonneg.mpr heventT), sub_sub_cancel, H.stageEndTime_castSucc]
        exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩)
      (show T - Real.sqrt (T - H.time capFirst) ^ 2 ∈ H.stageDomain capFirst by
        rw [Real.sq_sqrt (sub_nonneg.mpr (hbs.le.trans heventT)), sub_sub_cancel]
        exact H.time_mem_stageDomain capFirst)
      (⟨i.castSucc, hfi, le_rfl⟩ : H.StageInterval capFirst i.castSucc)
    have hinside := hstay (show Real.sqrt (T - H.time i.succ) ∈ Icc
        (H.regularizedStageStart T (Real.sqrt (T - H.time i.succ)) i.castSucc)
        (H.regularizedStageEnd T (Real.sqrt (T - H.time capFirst)) i.castSucc) by
      rw [hclock] at hbounds ⊢
      exact ⟨le_rfl, hbounds.2.1⟩)
    obtain ⟨old, hold, _⟩ := hnode i (hfirst.trans hfi) hilast
    exact Set.disjoint_left.mp hdisjoint hinside ⟨old, hold⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uE uH uM

open DifferentialGeometry.Tensor0SBundle in
theorem exists_uniform_prepared_discard_action_lower_bound_of_parabolicallyRmControlledBall
    (A B Ebound rTest : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hEbound : 0 ≤ Ebound) (hrTest : 0 < rTest) :
    ∃ theta r qmin Cbirth : ℝ, theta ∈ Ioo (0 : ℝ) 1 ∧ 0 < r ∧ 0 < qmin ∧ 0 < Cbirth ∧
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
        (w : StandardCap.CanonicalStaticInsertionWitness d A₀ hA Dbig m ζ),
        R ≤ Dbig → m₀ ≤ m → ζ ≤ ζ₀ →
      ∀ (H : ObservedHistory.{u}) (capFirst lossLast : Fin (H.eventCount + 1)) (hcapLoss : capFirst ≤ lossLast),
      ∀ (Jbig : standardCapWindow Dbig → (H.stage capFirst).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ Cbirth * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric capFirst).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ lossLast → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, capFirst ≤ j.castSucc → j.succ ≤ lossLast →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            Cderiv * (H.event j).incoming.flow.scalar t x ^ 2) →
      q * (H.time lossLast - H.time capFirst) ≤ theta →
      (¬ Jbig '' {x : standardCapWindow Dbig | ‖x.val‖ ≤ a} ⊆
        range (H.backwardSurvivorMap capFirst lossLast hcapLoss capFirst le_rfl hcapLoss)) →
      qmin ≤ q →
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTest →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ capFirst)
        (hlast : lossLast ≤ H.activeStage t) (v : ℝ), 0 ≤ v → v ≤ Ebound →
      t.val - v ^ 2 ∈ H.stageDomain first → t.val - v ^ 2 ≤ H.time capFirst →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (alpha j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (hcapLoss.trans hlast), le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ y : (H.event i).old,
          y.val.val = alpha ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput y = alpha ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      ∀ xPast : standardCapWindow Dbig, ‖xPast.val‖ ≤ Rbirth →
      alpha ⟨capFirst, hfirst, hcapLoss.trans hlast⟩ (Real.sqrt (t.val - H.time capFirst)) = Jbig xPast →
      A < ∑ j : H.StageInterval first (H.activeStage t), H.stageRegularizedAction j.val t.val (alpha j)
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val) := by
  obtain ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, haction⟩ :=
    exists_uniform_prepared_discard_action_lower_bound.{u, uE, uH, uM, u}
      A B Ebound (1 / rTest ^ 4) (rTest / 2) rTest Cderiv hB hEbound (half_pos hrTest) hrTest
  refine ⟨theta, r, qmin, Cbirth, htheta, hr, hqmin, hCbirth, ?_⟩
  intro E H₀ _ _ _ _ _ I _ Rbirth a
  obtain ⟨D, hD, haD, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, haction⟩ :=
    haction (I := I) Rbirth
  refine ⟨D, hD, haD, R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro M _ _ _ _ g x₀ δ k d A₀ hA Dbig m ζ w hR hm hζ
    H capFirst lossLast hcapLoss Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hdelta hderiv htime hnot hqscale
    t p hball first hfirst hlast v hv hvE hlowerPath hstart alpha halpha hint hscalar hrecent hnode
    xPast hnormPast hbirthPath
  obtain ⟨ta, hat, hta, U, hU, f, hf, hinj, hcross, hflast, S, hS, hmetric, hRm,
      hterminal, pU, K, hpU, himage, hK, hpinterior, hseparation⟩ :=
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
  have hRm' : ∀ s ∈ Icc (t.val - rTest ^ 2) t.val, ∀ x : U,
      normSq0S (S'.base.metric s) x 4 (S'.base.rm04 s x) ≤ 1 / rTest ^ 4 := by
    intro s hs x
    change normSq0S (S.base.metric s) x 4 (S.base.rm04 s x) ≤ 1 / rTest ^ 4
    apply (le_div_iff₀ (pow_pos hrTest 4)).mpr
    simpa only [mul_comm] using hRm s ⟨hta.le.trans hs.1, hs.2⟩ x
  apply haction w hR hm hζ H capFirst lossLast hcapLoss Jbig hJbig q q₀ a₀ hq hq₀ hq₀Q haq
    hzero parameters records hfixed hlower hdelta hderiv htime hnot hqscale
    U first (H.activeStage ta) (H.activeStage t) hfirst hlast (H.activeStage_mono hat)
    f hf hinj hcross t.val v hv hvE S' hS' hupper hlowerPath hcontrolled
    (fun j s hs hstage => hmetric j s ⟨hta.le.trans hs.1, hs.2.le⟩ hstage)
    hRm' K hK pU hpinterior hseparation hstart alpha halpha hint hscalar ?_ hnode
    xPast hnormPast hbirthPath
  rw [hflast, hpU]
  exact hrecent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
