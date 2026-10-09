import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v z uSmoothJoin uPositiveStages uStageSmooth

private theorem survivor_lift_weighted_action_on_shrunk_collar
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {C D T c0 d0 c d : ℝ} (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
    (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hmetricOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld)
    (hmetricNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew)
    (eta : ℝ → W) (hAC : Manifold.absolutelyContinuousOnInterval ThreeModel eta c0 d0)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c0 d0)
    (hnew : EqOn ((fun z : W => F z.val) ∘ eta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c0 (Real.sqrt (T - H.time i.succ))))
    (hold : EqOn ((fun z : W => z.val.val) ∘ eta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d0))
    (hc : 0 ≤ c) (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (hsub : Icc c d ⊆ Ioo c0 d0)
    (hclock : ∀ r ∈ Icc c0 d0, T - r ^ 2 ∈ Ioo C D)
    (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :
    IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T eta r) volume c d ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
        c (Real.sqrt (T - H.time i.succ)) ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
        (Real.sqrt (T - H.time i.succ)) d ∧
      (∫ r in c..d, weight r * lRegularizedLagrangian S T eta r) =
        (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
          H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
        ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
          H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
  let w := Real.sqrt (T - H.time i.succ)
  have hw : 0 < w := hc.trans_lt hcw
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt (Real.sqrt_pos.mp hw).le]
    ring
  have hcd : c ≤ d := (hcw.trans hwd).le
  have hc0 : c0 < c := (hsub (left_mem_Icc.mpr hcd)).1
  have hd0 : d < d0 := (hsub (right_mem_Icc.mpr hcd)).2
  have h0 : c0 ≤ d0 := (hc0.trans_le (hcd.trans_lt hd0).le).le
  have hintSub {l r : ℝ} (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume l r :=
    hint.mono_set (by
      simpa only [uIcc_of_le hlr, uIcc_of_le h0] using
        Icc_subset_Icc (hc0.le.trans hcl) (hrd.trans hd0.le))
  have htransfer (j : Fin (H.eventCount + 1))
      (f : W → (H.stage j).Carrier) (hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
      (alpha : ℝ → (H.stage j).Carrier) {l r : ℝ}
      (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d)
      (hproj : EqOn (f ∘ eta) alpha (Ioo l r))
      (hmet : ∀ q ∈ Ioo l r, S.base.metric (T - q ^ 2) =
        localPullMetric (H.stageMetric j (T - q ^ 2)) f hlocal) :
      lRegularizedLagrangian S T eta =ᵐ[volume.restrict (Ι l r)]
        H.stageRegularizedLagrangian j T alpha := by
    have hACSub := Manifold.absolutelyContinuousOnInterval_mono hAC (show uIcc l r ⊆ uIcc c0 d0 by
      simpa only [uIcc_of_le hlr, uIcc_of_le h0] using
        Icc_subset_Icc (hc0.le.trans hcl) (hrd.trans hd0.le))
    have hdiff := Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hACSub
    rw [uIcc_of_le hlr, ← restrict_Ioo_eq_restrict_Icc] at hdiff
    rw [uIoc_of_le hlr, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with q hqdiff hq
    have heq : f ∘ eta =ᶠ[𝓝 q] alpha := by
      filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
      exact hproj ht
    have hlag := H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hlocal T
      hqdiff (hmet q hq)
    rw [← hlag]
    have hv := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold stageRegularizedLagrangian lVelocity
    rw [hv, heq.self_of_nhds]
    rfl
  have hleft := htransfer i.succ (fun z : W => F z.val) hlocalNew
    (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) hcw.le le_rfl hwd.le
    (fun q hq => hnew ⟨hc0.le.trans hq.1.le, hq.2.le⟩) (fun q hq => by
      apply hmetricNew
      have htime := hclock q (Ioo_subset_Icc_self (hsub
        ⟨hq.1.le, hq.2.le.trans hwd.le⟩))
      have hsq : q ^ 2 < w ^ 2 := (sq_lt_sq₀ (hc.trans hq.1.le) hw.le).mpr hq.2
      exact ⟨by linarith [hwclock], htime.2.le⟩)
  have hright := htransfer i.castSucc (fun z : W => z.val.val) hlocalOld
    (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) hwd.le hcw.le le_rfl
    (fun q hq => hold ⟨hq.1.le, hq.2.le.trans hd0.le⟩) (fun q hq => by
      apply hmetricOld
      have htime := hclock q (Ioo_subset_Icc_self (hsub
        ⟨hcw.le.trans hq.1.le, hq.2.le⟩))
      have hsq : w ^ 2 < q ^ 2 := (sq_lt_sq₀ hw.le (hw.le.trans hq.1.le)).mpr hq.1
      exact ⟨htime.1.le, by linarith [hwclock]⟩)
  have hintWeighted {l r : ℝ} (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d) :
      IntervalIntegrable (fun q => weight q * lRegularizedLagrangian S T eta q) volume l r :=
    (hintSub hlr hcl hrd).continuousOn_mul (by
      rw [uIcc_of_le hlr]
      exact hweight.mono (Icc_subset_Icc hcl hrd))
  have hleftWeighted := hleft.mono (fun r hr => congrArg (fun x : ℝ => weight r * x) hr)
  have hrightWeighted := hright.mono (fun r hr => congrArg (fun x : ℝ => weight r * x) hr)
  have hintLeft := hintWeighted hcw.le le_rfl hwd.le
  have hintRight := hintWeighted hwd.le hcw.le le_rfl
  refine ⟨hintWeighted hcd le_rfl le_rfl,
    (intervalIntegrable_congr_ae hleftWeighted).mp hintLeft,
    (intervalIntegrable_congr_ae hrightWeighted).mp hintRight, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (intervalIntegral.integral_congr_ae_restrict hleftWeighted)
    (intervalIntegral.integral_congr_ae_restrict hrightWeighted)

private theorem exists_smooth_survivor_piece
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {C D T c0 d0 c d : ℝ} (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
    (hS : IsSolutionOn S)
    (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hmetricOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld)
    (hmetricNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew)
    (eta : ℝ → W) (hAC : Manifold.absolutelyContinuousOnInterval ThreeModel eta c0 d0)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c0 d0)
    (hgeo : IsLRegularizedGeodesicOn S T eta (Ioo c0 d0))
    (hnew : EqOn ((fun z : W => F z.val) ∘ eta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c0 (Real.sqrt (T - H.time i.succ))))
    (hold : EqOn ((fun z : W => z.val.val) ∘ eta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d0))
    (hc : 0 ≤ c) (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (hsub : Icc c d ⊆ Ioo c0 d0)
    (hclock : ∀ r ∈ Icc c0 d0, T - r ^ 2 ∈ Ioo C D)
    : ∃ lo hi : ℝ, lo < c ∧ d < hi ∧
      (∀ r ∈ Ioo lo hi,
        T - r ^ 2 ∈ (RealTimeInterval.closed C D (hCs.trans hsD).le).regular) ∧
      ∃ beta : ℝ → W,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
        (∀ r ∈ Icc c d, beta =ᶠ[𝓝 r] eta) ∧
        IsLRegularizedGeodesicOn S T beta (Icc c d) ∧
        EqOn ((fun z : W => F z.val) ∘ beta)
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (Icc c (Real.sqrt (T - H.time i.succ))) ∧
        EqOn ((fun z : W => z.val.val) ∘ beta)
          (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
          (Icc (Real.sqrt (T - H.time i.succ)) d) ∧
        ((fun z : W => F z.val) ∘ beta) =ᶠ[𝓝 c]
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) ∧
        ((fun z : W => z.val.val) ∘ beta) =ᶠ[𝓝 d]
          (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) ∧
        EqOn (lRegularizedLagrangian S T beta) (lRegularizedLagrangian S T eta) (Icc c d) ∧
        IntervalIntegrable (lRegularizedLagrangian S T beta) volume c d ∧
        lRegularizedAction S T beta c d =
          H.stageRegularizedAction i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
            c (Real.sqrt (T - H.time i.succ)) +
          H.stageRegularizedAction i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (Real.sqrt (T - H.time i.succ)) d ∧
        ∀ (weight : ℝ → ℝ), ContinuousOn weight (Icc c d) →
          IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T beta r)
            volume c d ∧
          IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
            c (Real.sqrt (T - H.time i.succ)) ∧
          IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
            (Real.sqrt (T - H.time i.succ)) d ∧
          (∫ r in c..d, weight r * lRegularizedLagrangian S T beta r) =
            (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
              H.stageRegularizedLagrangian i.succ T
                (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
            ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
              H.stageRegularizedLagrangian i.castSucc T
                (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
  have hcd : c < d := hcw.trans hwd
  have hc0 : c0 < c := (hsub (left_mem_Icc.mpr hcd.le)).1
  have hd0 : d < d0 := (hsub (right_mem_Icc.mpr hcd.le)).2
  have hsmooth := hgeo.contMDiffOn hS isOpen_Ioo
  obtain ⟨rho, lo, hi, hlo, hhi, hrho, hrhoId, _, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset isOpen_Ioo hcd hsub
  let beta : ℝ → W := eta ∘ rho
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    hsmooth.comp_contMDiff hrho.contMDiff hrange
  have hgerm (r : ℝ) (hr : r ∈ Icc c d) : beta =ᶠ[𝓝 r] eta := by
    filter_upwards [Icc_mem_nhds (hlo.trans_le hr.1) (hr.2.trans_lt hhi)] with t ht
    change eta (rho t) = eta t
    rw [hrhoId ht]
    rfl
  have hclockMargin (r : ℝ) (hr : r ∈ Ioo lo hi) :
      T - r ^ 2 ∈ (RealTimeInterval.closed C D (hCs.trans hsD).le).regular := by
    have hrr := hrange r
    rw [hrhoId (Ioo_subset_Icc_self hr)] at hrr
    exact hclock r (Ioo_subset_Icc_self hrr)
  have hbetaGeo : IsLRegularizedGeodesicOn S T beta (Icc c d) :=
    (show IsLRegularizedGeodesicOn S T eta (Icc c d) from
      fun r hr => hgeo r (hsub hr)).congr_of_eventuallyEq hgerm
  have hnewBeta : EqOn ((fun z : W => F z.val) ∘ beta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c (Real.sqrt (T - H.time i.succ))) := by
    intro r hr
    change F (beta r).val = _
    rw [(hgerm r ⟨hr.1, hr.2.trans hwd.le⟩).self_of_nhds]
    exact hnew ⟨hc0.le.trans hr.1, hr.2⟩
  have holdBeta : EqOn ((fun z : W => z.val.val) ∘ beta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d) := by
    intro r hr
    change (beta r).val.val = _
    rw [(hgerm r ⟨hcw.le.trans hr.1, hr.2⟩).self_of_nhds]
    exact hold ⟨hr.1, hr.2.trans hd0.le⟩
  have hnewGerm : ((fun z : W => F z.val) ∘ beta) =ᶠ[𝓝 c]
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) := by
    filter_upwards [hgerm c (left_mem_Icc.mpr hcd.le), Ioo_mem_nhds hc0 hcw] with r heq hr
    change F (beta r).val = _
    rw [heq]
    exact hnew (Ioo_subset_Icc_self hr)
  have holdGerm : ((fun z : W => z.val.val) ∘ beta) =ᶠ[𝓝 d]
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) := by
    filter_upwards [hgerm d (right_mem_Icc.mpr hcd.le), Ioo_mem_nhds hwd hd0] with r heq hr
    change (beta r).val.val = _
    rw [heq]
    exact hold (Ioo_subset_Icc_self hr)
  have hdensity : EqOn (lRegularizedLagrangian S T beta)
      (lRegularizedLagrangian S T eta) (Icc c d) := by
    intro r hr
    have heq := hgerm r hr
    have hvel : lVelocity (I := ThreeModel) beta r = lVelocity (I := ThreeModel) eta r := by
      unfold lVelocity
      rw [heq.mfderiv_eq]
      rfl
    unfold lRegularizedLagrangian
    rw [hvel, heq.self_of_nhds]
  have hweighted (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :=
    H.survivor_lift_weighted_action_on_shrunk_collar first last gamma i hf hl hCs hsD W F S
      hlocalOld hlocalNew hmetricOld hmetricNew eta hAC hint hnew hold hc hcw hwd hsub hclock
      weight hweight
  have hweightedBeta (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :
      IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T beta r) volume c d ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
        c (Real.sqrt (T - H.time i.succ)) ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
        (Real.sqrt (T - H.time i.succ)) d ∧
      (∫ r in c..d, weight r * lRegularizedLagrangian S T beta r) =
        (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
          H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
        ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
          H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
    obtain ⟨hInt, hNew, hOld, hEq⟩ := hweighted weight hweight
    have hEqWeighted : EqOn (fun r => weight r * lRegularizedLagrangian S T eta r)
        (fun r => weight r * lRegularizedLagrangian S T beta r) (Icc c d) :=
      fun r hr => congrArg (fun x : ℝ => weight r * x) (hdensity hr).symm
    refine ⟨hInt.congr (fun r hr => hEqWeighted (Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le hcd.le] using hr))), hNew, hOld, ?_⟩
    rw [← hEq]
    exact intervalIntegral.integral_congr (by
      simpa only [uIcc_of_le hcd.le] using hEqWeighted.symm)
  have hunit := hweightedBeta (fun _ => 1) continuousOn_const
  have hbetaInt : IntervalIntegrable (lRegularizedLagrangian S T beta) volume c d := by
    simpa only [one_mul] using hunit.1
  have hbetaAction : lRegularizedAction S T beta c d =
      H.stageRegularizedAction i.succ T (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        c (Real.sqrt (T - H.time i.succ)) +
      H.stageRegularizedAction i.castSucc T (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (Real.sqrt (T - H.time i.succ)) d := by
    simpa only [one_mul, lRegularizedAction, stageRegularizedAction] using hunit.2.2.2
  exact ⟨lo, hi, hlo, hhi, hclockMargin, beta, hbeta, hgerm, hbetaGeo,
    hnewBeta, holdBeta, hnewGerm, holdGerm, hdensity, hbetaInt, hbetaAction, hweightedBeta⟩

theorem exists_smooth_prefix_survivor_representatives
    (H : ObservedHistory.{u}) (first last cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last)
    (gamma : (x : H.StageInterval first last) → ℝ → (H.stage x.val).Carrier) (T : ℝ) :
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : H.StageInterval first last :=
      ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans (i.property.2.trans hcl)⟩;
    let jn (i : E) : H.StageInterval first last :=
      ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2.trans hcl⟩;
    ∀ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
      (hsD : ∀ i, H.time i.val.succ < D i)
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
        (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
      (hlocalOld : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hlocalNew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (c0 d0 c d : E → ℝ) (eta : (i : E) → ℝ → W i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, ∀ t ∈ Ico (C i) (H.time i.val.succ), (S i).base.metric t =
        localPullMetric (H.stageMetric i.val.castSucc t) (fun z : W i => z.val.val) (hlocalOld i)) →
      (∀ i, ∀ t ∈ Icc (H.time i.val.succ) (D i), (S i).base.metric t =
        localPullMetric (H.stageMetric i.val.succ t) (fun z : W i => F i z.val) (hlocalNew i)) →
      (∀ i, Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i)) →
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (S i) T (eta i)) volume (c0 i) (d0 i)) →
      (∀ i, IsLRegularizedGeodesicOn (S i) T (eta i) (Ioo (c0 i) (d0 i))) →
      (∀ i, EqOn ((fun z : W i => F i z.val) ∘ eta i) (gamma (jn i))
        (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ)))) →
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i))) →
      (∀ i, 0 ≤ c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d i ∧ Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) →
      (∀ i, ∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) →
    ∃ (low high : E → ℝ) (alpha : (i : E) → ℝ → W i),
      (∀ i, low i < c i ∧ d i < high i) ∧
      (∀ i, ∀ r ∈ Ioo (low i) (high i),
        T - r ^ 2 ∈ (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le).regular) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha i)) ∧
      (∀ i, ∀ r ∈ Icc (c i) (d i), alpha i =ᶠ[𝓝 r] eta i) ∧
      (∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (c i) (d i))) ∧
      (∀ i, EqOn ((fun z : W i => F i z.val) ∘ alpha i) (gamma (jn i))
        (Icc (c i) (Real.sqrt (T - H.time i.val.succ)))) ∧
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ alpha i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d i))) ∧
      (∀ i, ((fun z : W i => F i z.val) ∘ alpha i) =ᶠ[𝓝 (c i)] gamma (jn i)) ∧
      (∀ i, ((fun z : W i => z.val.val) ∘ alpha i) =ᶠ[𝓝 (d i)] gamma (jo i)) ∧
      (∀ i, EqOn (lRegularizedLagrangian (S i) T (alpha i))
        (lRegularizedLagrangian (S i) T (eta i)) (Icc (c i) (d i))) ∧
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (S i) T (alpha i)) volume (c i) (d i)) ∧
      (∀ i, lRegularizedAction (S i) T (alpha i) (c i) (d i) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c i)
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (d i)) ∧
      (∀ i (weight : ℝ → ℝ), ContinuousOn weight (Icc (c i) (d i)) →
        IntervalIntegrable (fun r => weight r * lRegularizedLagrangian (S i) T (alpha i) r)
          volume (c i) (d i) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.succ T
          (gamma (jn i)) r) volume (c i) (Real.sqrt (T - H.time i.val.succ)) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.castSucc T
          (gamma (jo i)) r) volume (Real.sqrt (T - H.time i.val.succ)) (d i) ∧
        (∫ r in (c i)..(d i), weight r * lRegularizedLagrangian (S i) T (alpha i) r) =
          (∫ r in (c i)..Real.sqrt (T - H.time i.val.succ), weight r *
            H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          ∫ r in Real.sqrt (T - H.time i.val.succ)..(d i), weight r *
            H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r) := by
  classical
  intro E jo jn C D hCs hsD W F S hlocalOld hlocalNew c0 d0 c d eta
    hS hmetricOld hmetricNew hAC hint hgeo hnew hold hcollar hclock
  have hproducer (i : E) :=
    H.exists_smooth_survivor_piece first last gamma i.val i.property.1 (i.property.2.trans hcl)
      (hCs i) (hsD i) (W i) (F i) (S i) (hS i) (hlocalOld i) (hlocalNew i)
      (hmetricOld i) (hmetricNew i) (eta i) (hAC i) (hint i) (hgeo i) (hnew i) (hold i)
      (hcollar i).1 (hcollar i).2.1 (hcollar i).2.2.1 (hcollar i).2.2.2 (hclock i)
  choose low high hlo hhi hreg alpha hsmooth hgerm hclosed hnewBeta holdBeta hnewGerm holdGerm
    hdensity hInt haction hweighted using hproducer
  exact ⟨low, high, alpha, fun i => ⟨hlo i, hhi i⟩, hreg, hsmooth, hgerm, hclosed,
    hnewBeta, holdBeta, hnewGerm, holdGerm, hdensity, hInt, haction, hweighted⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
