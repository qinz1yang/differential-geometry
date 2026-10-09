import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.EventContinuation
import Mathlib.Topology.Order.LeftRight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowDiscarding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability
import Mathlib.Topology.UniformSpace.OfCompactT2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
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
      exact (ite_eq_left (show w ≤ v from le_of_lt hw)).symm)
  · change Tendsto _ (𝓝[>] v) (𝓝 _)
    simpa only [le_refl, ite_true] using hright.congr' (by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (ite_eq_right (show ¬ w ≤ v from not_le_of_gt hw)).symm)

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
        simpa only [ite_eq_left hwv] using hh
      · apply H.regularizedSpatialCost_eq_of_mem_stageDomain
        apply (H.mem_stageDomain_iff ⟨t.val - w.val ^ 2, hphysical w⟩ i.castSucc).mpr
        simpa only [ite_eq_right hwv] using hh
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
