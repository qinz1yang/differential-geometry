import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension
import DifferentialGeometry.Topology.Manifold.SmoothInterval

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v z uSmoothJoin uPositiveStages uStageSmooth

private theorem exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uStageSmooth})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (j : H.StageInterval first last) {a b : ℝ} (hab : a ≤ b)
    (hleft : H.regularizedStageStart T u j.val < a)
    (hright : b < H.regularizedStageEnd T v j.val) :
    ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric j.val t) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian j.val T eta r = lRegularizedLagrangian S T eta r) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (c d : ℝ),
        H.stageRegularizedAction j.val T eta c d = lRegularizedAction S T eta c d) ∧
      (∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
        T - r ^ 2 ∈ D.regular) ∧
      ∃ beta : ℝ → (H.stage j.val).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
        (∀ r ∈ Icc a b, beta =ᶠ[𝓝 r] gamma j) ∧
        IsLRegularizedGeodesicOn S T beta (Icc a b) ∧
        lRegularizedAction S T beta a b = H.stageRegularizedAction j.val T (gamma j) a b := by
  have hsub : Icc a b ⊆ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val) :=
    fun _ hr => ⟨hleft.trans_le hr.1, hr.2.trans_lt hright⟩
  have hflow : ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric j.val t) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian j.val T eta r = lRegularizedLagrangian S T eta r) ∧
      IsLRegularizedGeodesicOn S T (gamma j)
        (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
    rcases j with ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
      have hp := H.mapsTo_regularizedStage_Ioo_Ioo T u v (Fin.last H.eventCount)
        (hsub ⟨le_rfl, hab⟩)
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hp.1.trans hp.2
      have hlast : last = Fin.last H.eventCount :=
        le_antisymm (Fin.le_last last) hk.2
      subst last
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation, ?_,
        H.stageRegularizedLagrangian_last hfinal T, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      · exact H.regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
          first hfinal hu huv (by simpa only [H.stageEndTime_last] using hupper)
          hpast hscalar gamma hgammaAC hgammaInt (fun i hf => hgammaNodes i hf (Fin.le_last _)) hmin
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, ?_,
        H.stageRegularizedLagrangian_castSucc i T, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_castSucc]
      · exact H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
          first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
          i hk.1 hk.2
  obtain ⟨D, S, hS, hmetric, hlag, hgeo⟩ := hflow
  have haction (eta : ℝ → (H.stage j.val).Carrier) (c d : ℝ) :
      H.stageRegularizedAction j.val T eta c d = lRegularizedAction S T eta c d := by
    unfold stageRegularizedAction lRegularizedAction
    exact intervalIntegral.integral_congr (fun r _ => hlag eta r)
  have hclock (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      T - r ^ 2 ∈ D.regular := (hgeo r hr).1
  have hsmooth := hgeo.contMDiffOn hS isOpen_Ioo
  let U := (fun t : ℝ => a + t) ⁻¹'
    Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_const.add continuous_id)
  have hLU : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun t => gamma j (a + t)) U :=
    hsmooth.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ ht => ht)
  have hseg : Icc (0 : ℝ) (b - a) ⊆ U := by
    intro t ht
    exact hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨eta, heta, hgerm⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (sub_nonneg.mpr hab) hU hseg hLU
  let beta : ℝ → (H.stage j.val).Carrier := fun t => eta (t - a)
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    heta.comp (contMDiff_id.sub contMDiff_const)
  have hbetaEq (r : ℝ) (hr : r ∈ Icc a b) : beta =ᶠ[𝓝 r] gamma j := by
    have heq := (hgerm (r - a) ⟨by linarith [hr.1], by linarith [hr.2]⟩).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt.tendsto
    filter_upwards [heq] with t ht
    have hsum : a + (t - a) = t := by ring
    simpa only [beta, Function.comp_apply, Pi.sub_apply, id_eq, hsum] using ht
  have hgeoAB : IsLRegularizedGeodesicOn S T (gamma j) (Icc a b) :=
    fun r hr => hgeo r (hsub hr)
  refine ⟨D, S, hS, hmetric, hlag, haction, hclock, beta, hbeta, hbetaEq,
    hgeoAB.congr_of_eventuallyEq hbetaEq, ?_⟩
  rw [haction]
  apply lRegularizedAction_congr
  intro r hr
  rw [uIoo_of_le hab] at hr
  exact (hbetaEq r ⟨hr.1.le, hr.2.le⟩).eq_of_nhds

theorem exists_smooth_prefix_stage_representatives
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last) :
    let J := H.StageInterval first cut;
    let gammaCut : (x : J) → ℝ → (H.stage x.val).Carrier :=
      fun x => gamma ⟨x.val, x.property.1, x.property.2.trans hcl⟩;
    ∀ lo hi : J → ℝ,
      (∀ x, H.regularizedStageStart T 0 x.val < lo x ∧ lo x ≤ hi x ∧
        hi x < H.regularizedStageEnd T v x.val) →
    ∃ (DO : J → RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (alpha : (x : J) → ℝ → (H.stage x.val).Carrier) (low high : J → ℝ),
      (∀ x, IsSolutionOn (SO x)) ∧
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) ∧
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha x)) ∧
      (∀ x, ∀ r ∈ Icc (lo x) (hi x), alpha x =ᶠ[𝓝 r] gammaCut x) ∧
      (∀ x, EqOn (alpha x) (gammaCut x) (Icc (lo x) (hi x))) ∧
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alpha x) (Icc (lo x) (hi x))) ∧
      (∀ x, low x < lo x ∧ hi x < high x) ∧
      (∀ x, ∀ r ∈ Ioo (low x) (high x), T - r ^ 2 ∈ (DO x).regular) ∧
      (∀ x, EqOn (lRegularizedLagrangian (SO x) T (alpha x))
        (H.stageRegularizedLagrangian x.val T (gammaCut x)) (Icc (lo x) (hi x))) ∧
      (∀ x, lRegularizedAction (SO x) T (alpha x) (lo x) (hi x) =
        H.stageRegularizedAction x.val T (gammaCut x) (lo x) (hi x)) ∧
      (∀ x (weight : ℝ → ℝ),
        (∫ r in (lo x)..(hi x), weight r * lRegularizedLagrangian (SO x) T (alpha x) r) =
          ∫ r in (lo x)..(hi x), weight r * H.stageRegularizedLagrangian x.val T (gammaCut x) r) := by
  classical
  intro J gammaCut lo hi hgap
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hproducer (x : J) :=
    H.exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hv.le hupper0 hpastD hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      ⟨x.val, x.property.1, x.property.2.trans hcl⟩ (hgap x).2.1 (hgap x).1 (hgap x).2.2
  choose DO SO hSO hmetric hlag haction hclock alpha hsmooth hgerm hgeo hact using hproducer
  let low (x : J) := (H.regularizedStageStart T 0 x.val + lo x) / 2
  let high (x : J) := (hi x + H.regularizedStageEnd T v x.val) / 2
  have hmargin (x : J) : low x < lo x ∧ hi x < high x := by
    dsimp only [low, high]
    constructor <;> linarith [(hgap x).1, (hgap x).2.2]
  have hreg (x : J) (r : ℝ) (hr : r ∈ Ioo (low x) (high x)) :
      T - r ^ 2 ∈ (DO x).regular := by
    apply hclock x r
    dsimp only [low, high] at hr
    constructor <;> linarith [(hgap x).1, (hgap x).2.2, hr.1, hr.2]
  have hdensity (x : J) : EqOn (lRegularizedLagrangian (SO x) T (alpha x))
      (H.stageRegularizedLagrangian x.val T (gammaCut x)) (Icc (lo x) (hi x)) := by
    intro r hr
    rw [hlag x]
    have heq := hgerm x r hr
    have hvel : lVelocity (I := ThreeModel) (alpha x) r = lVelocity (I := ThreeModel) (gammaCut x) r := by
      unfold lVelocity
      rw [heq.mfderiv_eq]
      rfl
    unfold lRegularizedLagrangian
    rw [hvel, heq.self_of_nhds]
  refine ⟨DO, SO, alpha, low, high, hSO, hmetric, hsmooth, hgerm,
    fun x r hr => (hgerm x r hr).self_of_nhds, hgeo, hmargin, hreg, hdensity, hact, ?_⟩
  intro x weight
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (hgap x).2.1] at hr
  exact congrArg (fun z : ℝ => weight r * z) (hdensity x hr)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
