import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorMetricSeam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Measurable
import DifferentialGeometry.Analysis.Integration.Integral.LowerBounded
import DifferentialGeometry.Topology.Order.InfimumAddition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.WithTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1RegularityJointMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalActionCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalActionRegularity
set_option autoImplicit false
section

open Set Filter
open scoped Topology

private theorem exists_finite_action_vector_limit
    {ι : Type*} [Fintype ι] (f : ℕ → ι → ℝ) (lower upper : ι → ℝ) (ell : ℝ)
    (hbound : ∀ n i, lower i ≤ f n i ∧ f n i ≤ upper i)
    (hsum : Tendsto (fun n => ∑ i, f n i) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (values : ι → ℝ), StrictMono phi ∧
      (∀ i, Tendsto (fun n => f (phi n) i) atTop (𝓝 (values i))) ∧
      ∑ i, values i = ell := by
  have hmem (n : ℕ) : f n ∈ Icc lower upper :=
    ⟨fun i => (hbound n i).1, fun i => (hbound n i).2⟩
  obtain ⟨values, _, phi, hphi, hconv⟩ := isCompact_Icc.tendsto_subseq hmem
  have hpoint (i : ι) : Tendsto (fun n => f (phi n) i) atTop (𝓝 (values i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hconv
  have htotal : Tendsto (fun n => ∑ i, f (phi n) i) atTop (𝓝 (∑ i, values i)) :=
    tendsto_finsetSum _ (fun i _ => hpoint i)
  exact ⟨phi, values, hphi, hpoint, tendsto_nhds_unique htotal (hsum.comp hphi.tendsto_atTop)⟩

private theorem exists_finset_subsequence_limits
    {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (s : Finset ι) (f : (i : ι) → ℕ → X i) (R : (i : ι) → X i → Prop)
    (h : ∀ i ∈ s, ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ (psi : ℕ → ℕ) (x : X i), StrictMono psi ∧ R i x ∧
        Tendsto (f i ∘ phi ∘ psi) atTop (𝓝 x)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ i ∈ s,
      ∃ x : X i, R i x ∧ Tendsto (f i ∘ phi) atTop (𝓝 x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨phi, hphi, hlim⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨psi, x, hpsi, hx, hconv⟩ := h i (Finset.mem_insert_self _ _) phi hphi
    refine ⟨phi ∘ psi, hphi.comp hpsi, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨x, hx, hconv⟩
    · obtain ⟨y, hy, hconvj⟩ := hlim j hj
      exact ⟨y, hy, hconvj.comp hpsi.tendsto_atTop⟩

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

private theorem exists_old_of_tendsto
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {alpha : ι → P.Carrier} {beta : ι → Q.Carrier} {p : P.Carrier} {q : Q.Carrier}
    (halpha : Tendsto alpha l (𝓝 p)) (hbeta : Tendsto beta l (𝓝 q))
    (hnode : ∀ᶠ n in l, ∃ z : E.old, z.val.val = alpha n ∧ E.oldOutput z = beta n) :
    ∃ z : E.old, z.val.val = p ∧ E.oldOutput z = q := by
  let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
  let f : E.old → P.Carrier × Q.Carrier := fun z => (z.val.val, E.oldOutput z)
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).prodMk E.oldOutput.continuous
  have hmem : (p, q) ∈ range f := (isCompact_range hf).isClosed.mem_of_tendsto
    (halpha.prodMk_nhds hbeta) (by
      filter_upwards [hnode] with n hn
      obtain ⟨z, hz1, hz2⟩ := hn
      exact ⟨z, Prod.ext hz1 hz2⟩)
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uOldLimit
variable (H : ObservedHistory.{uOldLimit})

private theorem exists_subsequence_old_stage_action_le_of_tendsto_action
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (j : H.StageInterval first last) (hj : j.val < last)
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (halpha : ∀ n k, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n k)
      (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)))
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hint : ∀ n, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ n, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ A)
    (haction : Tendsto (fun n => H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      H.stageRegularizedAction j.val T gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ ell := by
  rcases j with ⟨k, hk⟩
  cases k using Fin.lastCases with
  | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hj)
  | cast i =>
    have hl : i.succ ≤ last := by
      change i.val + 1 ≤ last.val
      exact hj
    have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
      ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
    have hstart := H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl
    have hclocks := H.regularizedStage_endpoint_clocks hupperIcc huv hu
      (⟨i.castSucc, hk⟩ : H.StageInterval first last)
    have hterminal : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = H.time i.succ := by
      rw [hclocks.1, H.stageEndTime_castSucc]
      exact min_eq_right ((H.time_strictMono.monotone hl).trans hupperIcc.1)
    have hpastlt : T - v ^ 2 < H.time i.succ := by
      let tPast : Icc (0 : ℝ) H.horizon := ⟨T - v ^ 2, H.stageDomain_subset first hpast⟩
      have hactive : H.activeStage tPast = first := (H.mem_stageDomain_iff tPast first).mp hpast
      by_contra hn
      have hle : i.succ ≤ first := by
        simpa only [hactive] using H.le_activeStage tPast i.succ (not_lt.mp hn)
      exact (not_le_of_gt (hk.1.trans_lt i.castSucc_lt_succ)) hle
    have hmaxlt : max (T - v ^ 2) (H.time i.castSucc) < H.time i.succ :=
      max_lt hpastlt (H.time_strictMono i.castSucc_lt_succ)
    have hstart0 : 0 ≤ H.regularizedStageStart T u i.castSucc := Real.sqrt_nonneg _
    have hend0 : 0 ≤ H.regularizedStageEnd T v i.castSucc := Real.sqrt_nonneg _
    have hstrict : H.regularizedStageStart T u i.castSucc <
        H.regularizedStageEnd T v i.castSucc := by
      by_contra hn
      have hsq := (sq_le_sq₀ hend0 hstart0).mpr (not_lt.mp hn)
      nlinarith only [hterminal, hclocks.2, hmaxlt, hsq]
    have hphysicalPast : H.time i.castSucc ≤ T - (H.regularizedStageEnd T v i.castSucc) ^ 2 := by
      rw [hclocks.2]
      exact le_max_right _ _
    let E := H.event i
    let : CompactSpace E.old := isCompact_iff_compactSpace.mp E.old_compact
    let K : Set E.incoming.terminalRegularOpen := range E.oldTerminal
    have hK : IsCompact K := isCompact_range E.oldTerminal.continuous
    have hstartK (n : ℕ) : alpha n ⟨i.castSucc, hk⟩
        (H.regularizedStageStart T u i.castSucc) ∈ Subtype.val '' K := by
      obtain ⟨z, hz, _⟩ := hnodes n i hk.1 hl
      refine ⟨E.oldTerminal z, mem_range_self z, ?_⟩
      rw [E.oldTerminal_eq, hstart]
      exact hz
    have hlag (gamma : ℝ → (H.stage i.castSucc).Carrier) :
        H.stageRegularizedLagrangian i.castSucc T gamma =
          lRegularizedLagrangian E.incoming.flow T gamma :=
      funext (H.stageRegularizedLagrangian_castSucc i T gamma)
    obtain ⟨phi, gamma, hgamma, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      E.terminal.exists_subsequence_action_le_of_tendsto_action K hK hstart0 hstrict
        hterminal hphysicalPast A B ell hB (fun n => alpha n ⟨i.castSucc, hk⟩)
        (fun n => halpha n ⟨i.castSucc, hk⟩) hstartK
        (fun n => by simpa only [hlag] using hint n)
        (fun n r hr => by
          change -B ≤ metricScalarAt ((H.event i).incoming.flow.base.metric (T - r ^ 2))
            (alpha n ⟨i.castSucc, hk⟩ r)
          simpa only [stageMetric, Fin.lastCases_castSucc] using hscalar n r hr)
        (fun n => by simpa only [H.stageRegularizedAction_castSucc] using hact n)
        (by simpa only [H.stageRegularizedAction_castSucc] using haction)
    refine ⟨phi, gamma, hgamma, hphi, hconv, hAC, ?_, ?_⟩
    · simpa only [hlag] using hInt
    · simpa only [H.stageRegularizedAction_castSucc] using hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uFinal

private theorem exists_subsequence_stageAction_le_of_tendsto_at_observed_time
    (H : ObservedHistory.{uFinal}) (t : Icc (0 : ℝ) H.horizon)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hTu : T - u ^ 2 = t.val)
    (ha : H.time (H.activeStage t) ≤ T - v ^ 2)
    (p : (H.stageAt t).Carrier) (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → ℝ → (H.stageAt t).Carrier)
    (halpha : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n) (Icc u v))
    (hstart : ∀ n, alpha n u = p)
    (hscalar : ∀ n, ∀ r ∈ Ioo u v,
      -B ≤ metricScalarAt (H.stageMetric (H.activeStage t) (T - r ^ 2)) (alpha n r))
    (hact : ∀ n, H.stageRegularizedAction (H.activeStage t) T (alpha n) u v ≤ A)
    (haction : Tendsto
      (fun n => H.stageRegularizedAction (H.activeStage t) T (alpha n) u v)
      atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stageAt t).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) r.val,
        (halpha (phi n)).continuousOn.domRestrict⟩ : C(Icc u v, (H.stageAt t).Carrier)))
        atTop (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      gamma u = p ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      IntervalIntegrable (H.stageRegularizedLagrangian (H.activeStage t) T gamma)
        volume u v ∧
      H.stageRegularizedAction (H.activeStage t) T gamma u v ≤ ell := by
  let : TopologicalSpace.MetrizableSpace (H.stageAt t).Carrier :=
    Manifold.metrizableSpace ThreeModel (H.stageAt t).Carrier
  let : MetricSpace (H.stageAt t).Carrier := TopologicalSpace.metrizableSpaceMetric _
  have ht : H.time (H.activeStage t) < t.val := by
    have hsq : u ^ 2 < v ^ 2 := (sq_lt_sq₀ hu (hu.trans huv.le)).2 huv
    linarith only [ha, hTu, hsq]
  generalize hS : H.closedPrefixAt t ht = S
  let G : (H.stageAt t).IncomingSlab (H.time (H.activeStage t)) t.val :=
    S.restrictIncoming le_rfl S.lt le_rfl
  let L : G.TerminalLimitMetric := S.endpointTerminalLimitMetric (H.stageAt t)
  have hmetric (r : ℝ) : G.flow.base.metric r = H.stageMetric (H.activeStage t) r := by
    change S.flow.base.metric r = _
    rw [← hS]
    exact H.closedPrefixAt_metric t ht r
  have hlag (beta : ℝ → (H.stageAt t).Carrier) :
      lRegularizedLagrangian G.flow T beta =
        H.stageRegularizedLagrangian (H.activeStage t) T beta := by
    funext r
    simp only [lRegularizedLagrangian, stageRegularizedLagrangian,
      SolutionOn.scalar, SolutionFamily.scalar, hmetric]
  have hactionEq (beta : ℝ → (H.stageAt t).Carrier) :
      lRegularizedAction G.flow T beta u v =
        H.stageRegularizedAction (H.activeStage t) T beta u v := by
    unfold lRegularizedAction stageRegularizedAction
    rw [hlag]
  let pG : G.terminalRegularOpen := ⟨p, by
    change p ∈ G.terminalRegularRegion
    rw [S.terminalRegularRegion_eq_univ]
    exact mem_univ _⟩
  have hclock (r : ℝ) (hr : r ∈ Icc u v) :
      T - r ^ 2 ∈ Icc (H.time (H.activeStage t)) t.val := by
    have hl := pow_le_pow_left₀ hu hr.1 2
    have hr' := pow_le_pow_left₀ (hu.trans hr.1) hr.2 2
    constructor <;> linarith only [ha, hTu, hl, hr']
  have hint (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian G.flow T (alpha n)) volume u v := by
    change IntervalIntegrable (lRegularizedLagrangian S.flow T (alpha n)) volume u v
    have hMet : MetricFamilySmoothOn (I := ThreeModel)
        (RealTimeInterval.closed (H.time (H.activeStage t)) t.val ht.le) S.flow.family.metric :=
      S.equation.smoothMetric
    have hSc : ScalarSTContOn S.flow := ⟨S.equation.scalarCont⟩
    exact intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
      (I := ThreeModel) S.flow hMet hSc
      T u v huv.le (alpha n) (halpha n) hclock
  obtain ⟨phi, gamma, hgamma, hphi, hconv, hpoint, hAC, hInt, hle⟩ :=
    L.exists_subsequence_action_le_of_tendsto_action (P := H.stageAt t) (G := G) {pG} isCompact_singleton
      hu huv hTu ha A B ell hB alpha halpha
      (fun n => ⟨pG, mem_singleton pG, (hstart n).symm⟩) hint
      (fun n r hr => by
        change -B ≤ metricScalarAt (G.flow.base.metric (T - r ^ 2)) (alpha n r)
        rw [hmetric]
        exact hscalar n r hr)
      (fun n => by rw [hactionEq]; exact hact n)
      (by simpa only [hactionEq] using haction)
  refine ⟨phi, gamma, hgamma, hphi, hconv, ?_, hAC, ?_, ?_⟩
  · rcases hpoint with ⟨z, hz, heq⟩
    have hz' : z = pG := mem_singleton_iff.mp hz
    simpa only [hz'] using heq.symm
  · rwa [hlag] at hInt
  · rwa [hactionEq] at hle

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uStageZero
variable (H : ObservedHistory.{uStageZero})

private theorem exists_zero_final_stage_limit
    {last : Fin (H.eventCount + 1)} {T u v : ℝ} (hu : 0 ≤ u)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hcollapsed : H.regularizedStageStart T u last = H.regularizedStageEnd T v last)
    (p : (H.stage last).Carrier) (α : ℕ → ℝ → (H.stage last).Carrier)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (α n)
      (Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last)))
    (hstart : ∀ n, α n u = p) :
    H.regularizedStageStart T u last = u ∧ H.regularizedStageEnd T v last = u ∧
      (∀ n, H.stageRegularizedAction last T (α n)
        (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0) ∧
      ∃ (φ : ℕ → ℕ) (γ : ℝ → (H.stage last).Carrier) (hγ : Continuous γ),
        φ = id ∧ γ = (fun _ => p) ∧ StrictMono φ ∧
        Tendsto (fun n => (⟨fun r => α (φ n) r.val,
          (hα (φ n)).continuousOn.domRestrict⟩ :
            C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
              (H.stage last).Carrier))) atTop
          (𝓝 ⟨fun r => γ r.val, hγ.comp continuous_subtype_val⟩) ∧
        γ u = p ∧
        Manifold.absolutelyContinuousOnInterval ThreeModel γ
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) ∧
        IntervalIntegrable (H.stageRegularizedLagrangian last T γ) volume
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) ∧
        H.stageRegularizedAction last T γ
          (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0 := by
  have hs : H.regularizedStageStart T u last = u :=
    H.regularizedStageStart_eq_of_mem_Icc hu
      ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have he : H.regularizedStageEnd T v last = u := hcollapsed.symm.trans hs
  have hzero (α : ℝ → (H.stage last).Carrier) : H.stageRegularizedAction last T α
      (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last) = 0 := by
    simp only [hs, he, stageRegularizedAction, intervalIntegral.integral_same]
  refine ⟨hs, he, fun n => hzero (α n), id, (fun _ => p), continuous_const,
    rfl, rfl, strictMono_id, ?_, rfl, ?_, ?_, hzero _⟩
  · have heq (n : ℕ) :
        (⟨fun r => α (id n) r.val, (hα (id n)).continuousOn.domRestrict⟩ :
          C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
            (H.stage last).Carrier)) = ⟨fun _ => p, continuous_const⟩ := by
      ext r
      have hr : r.val = u :=
        le_antisymm (r.property.2.trans_eq he) (hs.symm.trans_le r.property.1)
      change α (id n) r.val = p
      simpa only [id_eq, hr] using hstart n
    simpa only [heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (⟨fun _ => p, continuous_const⟩ :
          C(Icc (H.regularizedStageStart T u last) (H.regularizedStageEnd T v last),
            (H.stage last).Carrier))) atTop (𝓝 _))
  · let : IsManifold ThreeModel 1 (H.stage last).Carrier := IsManifold.of_le (n := ∞) (by decide)
    exact Manifold.absolutelyContinuousOnInterval_of_contMDiffOn contMDiffOn_const
  · rw [hs, he]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uStageLimit
variable (H : ObservedHistory.{uStageLimit})

private theorem exists_subsequence_stage_action_le_of_tendsto_action
    {first last : Fin (H.eventCount + 1)} {T u v : ℝ}
    (hle : first ≤ last) (j : H.StageInterval first last)
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (A B ell : ℝ) (hB : 0 ≤ B)
    (alpha : ℕ → (k : H.StageInterval first last) → ℝ → (H.stage k.val).Carrier)
    (halpha : ∀ n k, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n k)
      (Icc (H.regularizedStageStart T u k.val) (H.regularizedStageEnd T v k.val)))
    (hstart : ∀ n, alpha n ⟨last, hle, le_rfl⟩ u = p)
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hint : ∀ n, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hscalar : ∀ n, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ A)
    (haction : Tendsto (fun n => H.stageRegularizedAction j.val T (alpha n j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      StrictMono phi ∧
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩) ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ∧
      H.stageRegularizedAction j.val T gamma
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤ ell := by
  rcases lt_or_eq_of_le j.property.2 with hj | hj
  · exact H.exists_subsequence_old_stage_action_le_of_tendsto_action j hj hu huv hupper hpast
      A B ell hB alpha halpha hnodes hint hscalar hact haction
  rcases j with ⟨k, hk⟩
  dsimp only at hj
  subst k
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hs : H.regularizedStageStart T u last = u :=
    H.regularizedStageStart_eq_of_mem_Icc hu hupperIcc
  have hbounds := H.regularizedStage_bounds hu huv hupperIcc hpast
    (⟨last, hle, le_rfl⟩ : H.StageInterval first last)
  rcases hbounds.2.1.eq_or_lt with hcollapsed | hstrict
  · obtain ⟨_, _, hzero, phi, gamma, hgamma, _, _, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      H.exists_zero_final_stage_limit hu hupper hcollapsed p
        (fun n => alpha n ⟨last, hle, le_rfl⟩)
        (fun n => halpha n ⟨last, hle, le_rfl⟩) hstart
    have hell : ell = 0 := tendsto_nhds_unique haction (by
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact ⟨phi, gamma, hgamma, hphi, hconv, hAC, hInt, hbound.le.trans_eq hell.symm⟩
  · generalize ht : (⟨T - u ^ 2, H.stageDomain_subset last hupper⟩ :
        Icc (0 : ℝ) H.horizon) = t
    have hTu : T - u ^ 2 = t.val := congrArg Subtype.val ht
    have hactive : H.activeStage t = last := (H.mem_stageDomain_iff t last).mp (by
      rw [← hTu]
      exact hupper)
    subst last
    have hclocks := H.regularizedStage_endpoint_clocks hupperIcc huv hu
      (⟨H.activeStage t, hle, le_rfl⟩ : H.StageInterval first (H.activeStage t))
    have hphysicalPast : H.time (H.activeStage t) ≤
        T - (H.regularizedStageEnd T v (H.activeStage t)) ^ 2 := by
      rw [hclocks.2]
      exact le_max_right _ _
    obtain ⟨phi, gamma, hgamma, hphi, hconv, _, hAC, hInt, hbound⟩ :=
      H.exists_subsequence_stageAction_le_of_tendsto_at_observed_time t
        hu (by simpa only [hs] using hstrict) hTu hphysicalPast p A B ell hB
        (fun n => alpha n ⟨H.activeStage t, hle, le_rfl⟩)
        (fun n => by simpa only [hs] using halpha n ⟨H.activeStage t, hle, le_rfl⟩) hstart
        (fun n r hr => hscalar n r (by simpa only [hs] using hr))
        (fun n => by simpa only [hs] using hact n)
        (by simpa only [hs] using haction)
    refine ⟨phi, gamma, hgamma, hphi, ?_, ?_, ?_, ?_⟩
    · let e : C(Icc (H.regularizedStageStart T u (H.activeStage t))
          (H.regularizedStageEnd T v (H.activeStage t)),
          Icc u (H.regularizedStageEnd T v (H.activeStage t))) :=
        ⟨fun r => ⟨r.val, by simpa only [hs] using r.property⟩,
          continuous_subtype_val.subtype_mk (fun r => by simpa only [hs] using r.property)⟩
      exact (ContinuousMap.continuous_precomp e).continuousAt.tendsto.comp hconv
    · simpa only [hs] using hAC
    · simpa only [hs] using hInt
    · simpa only [hs] using hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryLimit

theorem exists_subsequence_sum_stageRegularizedAction_le_of_tendsto_action_of_tendsto_endpoint
    (H : ObservedHistory.{uHistoryLimit})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (A B ell : ℝ)
    (alpha : ℕ → (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (halpha : ∀ n j, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (alpha n j)
      (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)))
    (hint : ∀ n j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (alpha n j))
      volume (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hstart : ∀ n, alpha n ⟨last, hle, le_rfl⟩ u = p)
    (hend : Tendsto (fun n => alpha n ⟨first, le_rfl, hle⟩ v) atTop (𝓝 q))
    (hnodes : ∀ n (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = alpha n ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = alpha n ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ n j, ∀ r ∈ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val),
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r))
    (hact : ∀ n, (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ A)
    (haction : Tendsto (fun n => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (alpha n j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
      atTop (𝓝 ell)) :
    ∃ (phi : ℕ → ℕ) (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
      (hgamma : ∀ j, Continuous (gamma j)),
      StrictMono phi ∧
      (∀ j, Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
          (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma j r.val, (hgamma j).comp continuous_subtype_val⟩)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
      gamma ⟨last, hle, le_rfl⟩ u = p ∧ gamma ⟨first, le_rfl, hle⟩ v = q ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤ ell := by
  classical
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hscalarC (n : ℕ) (j : H.StageInterval first last) (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      -C ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) (alpha n j r) :=
    (neg_le_neg (le_max_left B 0)).trans (hscalar n j r hr)
  have hupperIcc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let a (j : H.StageInterval first last) := H.regularizedStageStart T u j.val
  let b (j : H.StageInterval first last) := H.regularizedStageEnd T v j.val
  let action (n : ℕ) (j : H.StageInterval first last) :=
    H.stageRegularizedAction j.val T (alpha n j) (a j) (b j)
  let lower (j : H.StageInterval first last) := -(2 * C / 3) * ((b j) ^ 3 - (a j) ^ 3)
  let upper (j : H.StageInterval first last) :=
    A + (2 * C / 3) * ((v ^ 3 - u ^ 3) - ((b j) ^ 3 - (a j) ^ 3))
  have hbound (n : ℕ) (j : H.StageInterval first last) :
      lower j ≤ action n j ∧ action n j ≤ upper j :=
    ⟨H.stageRegularizedAction_ge_of_scalar_lower_bound j.val T (alpha n j)
      (H.regularizedStage_bounds hu huv hupperIcc hpast j).2.1 (hscalarC n j) (hint n j),
      H.stageRegularizedAction_le_of_sum_le hu huv hupperIcc hpast
        (alpha n) (hint n) (hscalarC n) (hact n) j⟩
  obtain ⟨psi, values, hpsi, hvalues, hvaluesSum⟩ :=
    exists_finite_action_vector_limit action lower upper ell hbound haction
  let F (j : H.StageInterval first last) (n : ℕ) :
      C(Icc (a j) (b j), (H.stage j.val).Carrier) :=
    ⟨fun r => alpha (psi n) j r.val, (halpha (psi n) j).continuousOn.domRestrict⟩
  let R (j : H.StageInterval first last)
      (f : C(Icc (a j) (b j), (H.stage j.val).Carrier)) : Prop :=
    ∃ (gamma : ℝ → (H.stage j.val).Carrier) (hgamma : Continuous gamma),
      (⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩ :
        C(Icc (a j) (b j), (H.stage j.val).Carrier)) = f ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma (a j) (b j) ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T gamma) volume (a j) (b j) ∧
      H.stageRegularizedAction j.val T gamma (a j) (b j) ≤ values j
  have hcoordinate (j : H.StageInterval first last) (_hj : j ∈ Finset.univ)
      (chi : ℕ → ℕ) (hchi : StrictMono chi) :
      ∃ (theta : ℕ → ℕ) (f : C(Icc (a j) (b j), (H.stage j.val).Carrier)),
        StrictMono theta ∧ R j f ∧ Tendsto (F j ∘ chi ∘ theta) atTop (𝓝 f) := by
    obtain ⟨theta, gamma, hgamma, htheta, hconv, hAC, hInt, hleAction⟩ :=
      H.exists_subsequence_stage_action_le_of_tendsto_action hle j hu huv hupper hpast
        p (upper j) C (values j) hC (fun n => alpha (psi (chi n)))
        (fun n => halpha (psi (chi n))) (fun n => hstart (psi (chi n)))
        (fun n => hnodes (psi (chi n))) (fun n => hint (psi (chi n)) j)
        (fun n => hscalarC (psi (chi n)) j) (fun n => (hbound (psi (chi n)) j).2)
        ((hvalues j).comp hchi.tendsto_atTop)
    exact ⟨theta, ⟨fun r => gamma r.val, hgamma.comp continuous_subtype_val⟩,
      htheta, ⟨gamma, hgamma, rfl, hAC, hInt, hleAction⟩, hconv⟩
  obtain ⟨chi, hchi, hlimits⟩ :=
    exists_finset_subsequence_limits Finset.univ F R hcoordinate
  choose maps hmapsR hmapsConv using fun j => hlimits j (Finset.mem_univ j)
  choose gamma hgamma hgammaEq hgammaAC hgammaInt hgammaAction using hmapsR
  let phi := psi ∘ chi
  have hconv (j : H.StageInterval first last) :
      Tendsto (fun n => (⟨fun r => alpha (phi n) j r.val,
        (halpha (phi n) j).continuousOn.domRestrict⟩ :
        C(Icc (a j) (b j), (H.stage j.val).Carrier))) atTop
        (𝓝 ⟨fun r => gamma j r.val, (hgamma j).comp continuous_subtype_val⟩) := by
    rw [hgammaEq j]
    exact hmapsConv j
  have heval (j : H.StageInterval first last) (r : ℝ) (hr : r ∈ Icc (a j) (b j)) :
      Tendsto (fun n => alpha (phi n) j r) atTop (𝓝 (gamma j r)) :=
    (continuous_eval_const (⟨r, hr⟩ : Icc (a j) (b j))).continuousAt.tendsto.comp (hconv j)
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  have haLast : a jlast = u := H.regularizedStageStart_eq_of_mem_Icc hu hupperIcc
  have hbFirst : b jfirst = v := H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hpast
  have huLast : u ∈ Icc (a jlast) (b jlast) :=
    ⟨haLast.le, haLast.symm.trans_le (H.regularizedStage_bounds hu huv hupperIcc hpast jlast).2.1⟩
  have hvFirst : v ∈ Icc (a jfirst) (b jfirst) :=
    ⟨(H.regularizedStage_bounds hu huv hupperIcc hpast jfirst).2.1.trans_eq hbFirst, hbFirst.ge⟩
  refine ⟨phi, gamma, hgamma, hpsi.comp hchi, hconv, hgammaAC, hgammaInt, ?_, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (heval jlast u huLast)
    simpa only [jlast, hstart] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p))
  · apply tendsto_nhds_unique (heval jfirst v hvFirst)
    exact hend.comp (hpsi.comp hchi).tendsto_atTop
  · intro i hf hl
    let jo : H.StageInterval first last := ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    let jn : H.StageInterval first last := ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    let w := Real.sqrt (T - H.time i.succ)
    have hao : a jo = w := H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl
    have hbn : b jn = w := H.regularizedStageEnd_succ_eq_event_clock hpast i hf
    have hwo : w ∈ Icc (a jo) (b jo) := by
      rw [← hao]
      exact ⟨le_rfl, (H.regularizedStage_bounds hu huv hupperIcc hpast jo).2.1⟩
    have hwn : w ∈ Icc (a jn) (b jn) := by
      rw [← hbn]
      exact ⟨(H.regularizedStage_bounds hu huv hupperIcc hpast jn).2.1, le_rfl⟩
    exact (H.event i).exists_old_of_tendsto (heval jo w hwo) (heval jn w hwn)
      (Eventually.of_forall fun n => hnodes (phi n) i hf hl)
  · calc
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ≤
          ∑ j, values j := Finset.sum_le_sum (fun j _ => hgammaAction j)
      _ = ell := hvaluesSum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uHistoryClosedC1

theorem contMDiffOn_stage_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uHistoryClosedC1})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
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
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v)) :
    ∀ j : H.StageInterval first last,
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)
        (Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
  have hupperClosed : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  intro j
  have hbounds := H.regularizedStage_bounds hu huv hupperClosed hpast j
  have hclocks := H.regularizedStage_endpoint_clocks hupperClosed huv hu j
  have hstart0 : 0 ≤ H.regularizedStageStart T u j.val := Real.sqrt_nonneg _
  have hend0 : 0 ≤ H.regularizedStageEnd T v j.val := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hbounds.2.1 with heq | hstrict
  · apply (contMDiffOn_const (c := gamma j (H.regularizedStageStart T u j.val))).congr
    intro r hr
    have hr' : r = H.regularizedStageStart T u j.val :=
      le_antisymm (hr.2.trans_eq heq.symm) hr.1
    rw [hr']
  have hclock (r : ℝ)
      (hr : r ∈ Icc (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      T - r ^ 2 ∈ Icc (H.time j.val) (H.stageEndTime j.val) := by
    have hr0 := hstart0.trans hr.1
    have hsqA := (sq_le_sq₀ hstart0 hr0).mpr hr.1
    have hsqB := (sq_le_sq₀ hr0 hend0).mpr hr.2
    have hA : T - (H.regularizedStageStart T u j.val) ^ 2 ≤ H.stageEndTime j.val := by
      rw [hclocks.1]
      exact min_le_right _ _
    have hB : H.time j.val ≤ T - (H.regularizedStageEnd T v j.val) ^ 2 := by
      rw [hclocks.2]
      exact le_max_right _ _
    constructor <;> linarith only [hsqA, hsqB, hA, hB]
  have hminimum {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D)
      (hlag : ∀ beta : ℝ → (H.stage j.val).Carrier,
        H.stageRegularizedLagrangian j.val T beta = lRegularizedLagrangian S T beta) :
      ∀ beta : ℝ → (H.stage j.val).Carrier,
        Manifold.absolutelyContinuousOnInterval ThreeModel beta
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) →
        IntervalIntegrable (lRegularizedLagrangian S T beta) volume
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) →
        beta (H.regularizedStageStart T u j.val) = gamma j (H.regularizedStageStart T u j.val) →
        beta (H.regularizedStageEnd T v j.val) = gamma j (H.regularizedStageEnd T v j.val) →
        lRegularizedAction S T (gamma j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) ≤
        lRegularizedAction S T beta
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    intro beta hbeta hbetaInt hbetaA hbetaB
    have hh := H.stageRegularizedAction_le_of_regularizedExtendedAction_eq_regularizedCost
      first last hle hu huv hupperClosed hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      j beta hbeta (by simpa only [hlag] using hbetaInt) hbetaA hbetaB
    simpa only [stageRegularizedAction, lRegularizedAction, hlag] using hh
  rcases j with ⟨k, hk⟩
  cases k using Fin.lastCases with
  | last =>
    have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
      by_contra hn
      have hcollapse : H.stageEndTime (Fin.last H.eventCount) ≤ H.time (Fin.last H.eventCount) := by
        simpa only [H.stageEndTime_last] using le_of_not_gt hn
      have hendstart : H.regularizedStageEnd T v (Fin.last H.eventCount) ≤
          H.regularizedStageStart T u (Fin.last H.eventCount) := by
        apply Real.sqrt_le_sqrt
        apply sub_le_sub_left
        exact (min_le_right _ _).trans (hcollapse.trans (le_max_right _ _))
      exact (not_le_of_gt hstrict) hendstart
    let S := (H.finalSlab hfinal).flow
    let : TopologicalSpace.MetrizableSpace (H.stage (Fin.last H.eventCount)).Carrier :=
      Manifold.metrizableSpace ThreeModel (H.stage (Fin.last H.eventCount)).Carrier
    let : PseudoMetricSpace (H.stage (Fin.last H.eventCount)).Carrier :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric (H.stage (Fin.last H.eventCount)).Carrier
    have hlag (beta : ℝ → (H.stage (Fin.last H.eventCount)).Carrier) :
        H.stageRegularizedLagrangian (Fin.last H.eventCount) T beta =
          lRegularizedLagrangian S T beta :=
      funext (H.stageRegularizedLagrangian_last hfinal T beta)
    have htime (r : ℝ)
        (hr : r ∈ Icc (H.regularizedStageStart T u (Fin.last H.eventCount))
          (H.regularizedStageEnd T v (Fin.last H.eventCount))) :
        T - r ^ 2 ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      simpa only [H.stageEndTime_last] using hclock r hr
    apply lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric
      S (H.finalSlab hfinal).equation T
      (H.regularizedStageStart T u (Fin.last H.eventCount))
      (H.regularizedStageEnd T v (Fin.last H.eventCount)) hstrict
      (gamma ⟨Fin.last H.eventCount, hk⟩) (hgammaAC _)
      (by simpa only [hlag] using hgammaInt ⟨Fin.last H.eventCount, hk⟩)
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) Subset.rfl htime
      (fun r hr => by
        change H.time (Fin.last H.eventCount) < T - r ^ 2 ∧ T - r ^ 2 < H.horizon
        simpa only [H.stageEndTime_last, mem_Ioo] using
          H.mapsTo_regularizedStage_Ioo_Ioo T u v (Fin.last H.eventCount) hr)
      (H.finalSlab hfinal).smoothUpTo.jointContMDiffOn
    intro beta hbeta hbetaA hbetaB
    have hbetaInt : IntervalIntegrable (lRegularizedLagrangian S T beta) volume
        (H.regularizedStageStart T u (Fin.last H.eventCount))
        (H.regularizedStageEnd T v (Fin.last H.eventCount)) := by
      have hc := lRegularizedLagrangian_continuousOn_carrier S (H.finalSlab hfinal).equation beta hbeta
      exact (hc.comp (f := fun r : ℝ => (T, r))
        (continuous_const.prodMk continuous_id).continuousOn htime).intervalIntegrable_of_Icc hstrict.le
    exact hminimum S hlag beta
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hbeta.contMDiffOn)
      hbetaInt hbetaA hbetaB
  | cast i =>
    let G := (H.event i).incoming
    have hlag (beta : ℝ → (H.stage i.castSucc).Carrier) :
        H.stageRegularizedLagrangian i.castSucc T beta = lRegularizedLagrangian G.flow T beta :=
      funext (H.stageRegularizedLagrangian_castSucc i T beta)
    have hint : IntervalIntegrable
        (lRegularizedLagrangian G.flow T (gamma ⟨i.castSucc, hk⟩)) volume
        (H.regularizedStageStart T u i.castSucc) (H.regularizedStageEnd T v i.castSucc) := by
      simpa only [hlag] using hgammaInt ⟨i.castSucc, hk⟩
    by_cases hreach : H.time i.succ ≤ T - u ^ 2
    · let tUpper : Icc (0 : ℝ) H.horizon := ⟨T - u ^ 2, H.stageDomain_subset last hupper⟩
      have hactive : H.activeStage tUpper = last := (H.mem_stageDomain_iff tUpper last).mp hupper
      have hsucc : i.succ ≤ last := by
        simpa only [hactive] using H.le_activeStage tUpper i.succ hreach
      have hstart : H.regularizedStageStart T u i.castSucc = Real.sqrt (T - H.time i.succ) :=
        H.regularizedStageStart_castSucc_eq_event_clock hupperClosed i hsucc
      have hTu : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = H.time i.succ := by
        rw [hclocks.1, H.stageEndTime_castSucc, min_eq_right hreach]
      have ha : H.time i.castSucc ≤ T - (H.regularizedStageEnd T v i.castSucc) ^ 2 := by
        rw [hclocks.2]
        exact le_max_right _ _
      have hterminal : gamma ⟨i.castSucc, hk⟩ (H.regularizedStageStart T u i.castSucc) ∈
          G.terminalRegularOpen := by
        obtain ⟨z, hz, _⟩ := hgammaNodes i hk.1 hsucc
        rw [hstart, ← hz, ← (H.event i).oldTerminal_eq z]
        exact ((H.event i).oldTerminal z).property
      exact (H.event i).terminal.contMDiffOn_one_of_action_minimal hstart0 hstrict hTu ha
        (hgammaAC _) hint hterminal (hminimum G.flow hlag)
    · apply G.contMDiffOn_one_of_action_minimal hstrict _ (hgammaAC _) hint (hminimum G.flow hlag)
      intro r hr
      have hsq := (sq_le_sq₀ hstart0 (hstart0.trans hr.1)).mpr hr.1
      have hstartPhys : T - (H.regularizedStageStart T u i.castSucc) ^ 2 = T - u ^ 2 := by
        rw [hclocks.1, H.stageEndTime_castSucc, min_eq_left (not_le.mp hreach).le]
      have hbefore : T - r ^ 2 < H.time i.succ := by
        linarith only [hsq, hstartPhys, not_le.mp hreach]
      exact ⟨(hclock r hr).1, hbefore⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem stageRegularizedAction_piecewise_Iic
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (T : ℝ)
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (alpha beta : ℝ → (H.stage j).Carrier)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha a c)
    (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta c b)
    (hintAlpha : IntervalIntegrable (H.stageRegularizedLagrangian j T alpha) volume a c)
    (hintBeta : IntervalIntegrable (H.stageRegularizedLagrangian j T beta) volume c b)
    (hnode : alpha c = beta c) :
    let gamma := (Iic c).piecewise alpha beta;
    Manifold.absolutelyContinuousOnInterval ThreeModel gamma a b ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j T gamma) volume a b ∧
      EqOn gamma alpha (Icc a c) ∧ EqOn gamma beta (Icc c b) ∧
      H.stageRegularizedAction j T gamma a b =
        H.stageRegularizedAction j T alpha a c + H.stageRegularizedAction j T beta c b := by
  classical
  let gamma := (Iic c).piecewise alpha beta
  have hleft : EqOn gamma alpha (Icc a c) := fun _ hr => ite_eq_left hr.2
  have hright : EqOn gamma beta (Icc c b) := by
    intro r hr
    rcases hr.1.eq_or_lt with hrc | hrc
    · subst r
      exact (show gamma c = alpha c from by simp [gamma]).trans hnode
    · exact ite_eq_right (not_le.mpr hrc)
  have hlagEq (eta zeta : ℝ → (H.stage j).Carrier) {l r : ℝ} (hlr : l ≤ r)
      (heq : EqOn eta zeta (Icc l r)) :
      EqOn (H.stageRegularizedLagrangian j T eta)
        (H.stageRegularizedLagrangian j T zeta) (uIoo l r) := by
    intro t ht
    rw [uIoo_of_le hlr] at ht
    have hev : eta =ᶠ[𝓝 t] zeta := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact heq (Ioo_subset_Icc_self hs)
    have hval := hev.self_of_nhds
    have hder := hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold stageRegularizedLagrangian lVelocity
    rw [hder, hval]
    rfl
  have hlagLeft := hlagEq gamma alpha hac hleft
  have hlagRight := hlagEq gamma beta hcb hright
  have hintLeft : IntervalIntegrable (H.stageRegularizedLagrangian j T gamma) volume a c :=
    hintAlpha.congr_uIoo hlagLeft.symm
  have hintRight : IntervalIntegrable (H.stageRegularizedLagrangian j T gamma) volume c b :=
    hintBeta.congr_uIoo hlagRight.symm
  refine ⟨Manifold.absolutelyContinuousOnInterval_piecewise_Iic halpha hbeta hac hcb hnode,
    hintLeft.trans hintRight, hleft, hright, ?_⟩
  unfold stageRegularizedAction
  rw [← intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight,
    intervalIntegral.integral_congr_uIoo hlagLeft, intervalIntegral.integral_congr_uIoo hlagRight]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
