import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmallPrefixTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarCompetitors

/-!
# S-CH11-FIX8 port of astra `WeightedCollarAction`（`PortC11P`）

来源：donor `WeightedCollarAction.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（1 个 error）。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `htransfer` 里 `intervalIntegral.integral_congr_uIoo` 之后目标是未 beta 归约的
  `(fun x ↦ weight x * …) t = (fun x ↦ …) t`，`rw [← hlag]` 找不到模式；
  在 `intro t ht` 之后补 `dsimp only`（只做 beta）。

原路径 `WeightedCollarAction` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v

private theorem sum_weighted_stage_action_eq_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (w : ℝ → ℝ), ContinuousOn w (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i,
        (∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (S i) T (eta i) r) =
          (∫ r in hi (jn i)..Real.sqrt (T - H.time i.val.succ),
            w r * H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          (∫ r in Real.sqrt (T - H.time i.val.succ)..lo (jo i),
            w r * H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
          w r * lRegularizedLagrangian (S i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v,
          w r * H.stageRegularizedLagrangian first T (gamma ⟨first, le_rfl, hle⟩) r) := by
  classical
  intro J E jo jn lo hi gamma hbounds hlo hInt w hw W D S eta hseam
  have hstart : H.regularizedStageStart T a last = a :=
    H.regularizedStageStart_eq_of_mem_Icc ha hupper
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (ha.trans hav) hpast
  have ho (i : E) : H.regularizedStageStart T a i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  let f (j : J) (r : ℝ) := w r * H.stageRegularizedLagrangian j.val T (gamma j) r
  have hfull (j : J) : IntervalIntegrable (f j) volume
      (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) := by
    have hj := H.regularizedStage_bounds ha hav hupper hpast j
    have hleft : H.regularizedStageStart T 0 j.val ≤ H.regularizedStageStart T a j.val := by
      rw [H.regularizedStageStart_eq_max_zero T ha]
      exact le_max_right _ _
    have hbase := (hInt j).mono_set (show
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) ⊆
        uIcc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hj.2.1, uIcc_of_le (hleft.trans hj.2.1)]
      exact Icc_subset_Icc hleft le_rfl)
    exact hbase.continuousOn_mul (by
      rw [uIcc_of_le hj.2.1]
      exact hw.mono (Icc_subset_Icc hj.1 hj.2.2))
  have hparts (j : J) :
      (∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val, f j r) =
        (∫ r in H.regularizedStageStart T a j.val..lo j, f j r) +
        (∫ r in lo j..hi j, f j r) +
        (∫ r in hi j..H.regularizedStageEnd T v j.val, f j r) := by
    have hs := hbounds j
    have hordered := hs.1.trans (hs.2.1.trans hs.2.2)
    have hleft := (hfull j).mono_set (show
        uIcc (H.regularizedStageStart T a j.val) (lo j) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.1, uIcc_of_le hordered]
      exact Icc_subset_Icc le_rfl (hs.2.1.trans hs.2.2))
    have hmid := (hfull j).mono_set (show uIcc (lo j) (hi j) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.1, uIcc_of_le hordered]
      exact Icc_subset_Icc hs.1 hs.2.2)
    have hright := (hfull j).mono_set (show
        uIcc (hi j) (H.regularizedStageEnd T v j.val) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.2, uIcc_of_le hordered]
      exact Icc_subset_Icc (hs.1.trans hs.2.1) le_rfl)
    rw [intervalIntegral.integral_add_adjacent_intervals hleft hmid,
      intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmid) hright]
  calc
    _ = ∑ j : J,
        ((∫ r in H.regularizedStageStart T a j.val..lo j, f j r) +
          (∫ r in lo j..hi j, f j r) +
          (∫ r in hi j..H.regularizedStageEnd T v j.val, f j r)) :=
      Finset.sum_congr rfl (fun j _ => hparts j)
    _ = _ := by
      rw [H.sum_stage_parts_eq_endpoints_add_events first last hle]
      simp only [hstart, hend, hlo, intervalIntegral.integral_same, zero_add]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      change (∫ r in hi (jn i)..H.regularizedStageEnd T v i.val.succ, f (jn i) r) +
        (∫ r in H.regularizedStageStart T a i.val.castSucc..lo (jo i), f (jo i) r) = _
      rw [ho, hn]
      exact (hseam i).symm

private theorem weighted_integral_eq_stage_of_eqOn
    (H : ObservedHistory) (j : Fin (H.eventCount + 1))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D)
    (T a b : ℝ) (beta gamma : ℝ → (H.stage j).Carrier) (w : ℝ → ℝ)
    (hmetric : ∀ r ∈ uIoo a b, S.base.metric (T - r ^ 2) = H.stageMetric j (T - r ^ 2))
    (heq : EqOn beta gamma (uIoo a b)) :
    (∫ r in a..b, w r * lRegularizedLagrangian S T beta r) =
      ∫ r in a..b, w r * H.stageRegularizedLagrangian j T gamma r := by
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  have hev : beta =ᶠ[𝓝 r] gamma := heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr)
  have hvel : lVelocity (I := ThreeModel) beta r = lVelocity (I := ThreeModel) gamma r := by
    unfold lVelocity
    rw [hev.mfderiv_eq]
    rfl
  change w r * ((1 / 2 : ℝ) *
      (S.base.metric (T - r ^ 2)).inner (beta r)
        (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
      2 * r ^ 2 * metricScalarAt (S.base.metric (T - r ^ 2)) (beta r)) =
    w r * ((1 / 2 : ℝ) * (H.stageMetric j (T - r ^ 2)).inner (gamma r)
        (lVelocity (I := ThreeModel) gamma r) (lVelocity (I := ThreeModel) gamma r) +
      2 * r ^ 2 * metricScalarAt (H.stageMetric j (T - r ^ 2)) (gamma r))
  rw [hmetric r hr, hvel, hev.self_of_nhds]

private theorem sum_weighted_stage_action_eq_smooth_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (w : ℝ → ℝ), ContinuousOn w (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (DS : E → RealTimeInterval)
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (eta : (i : E) → ℝ → W i),
      (∀ i,
        (∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (SS i) T (eta i) r) =
          (∫ r in hi (jn i)..Real.sqrt (T - H.time i.val.succ),
            w r * H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          (∫ r in Real.sqrt (T - H.time i.val.succ)..lo (jo i),
            w r * H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) →
    ∀ (DO : J → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (beta : (j : J) → ℝ → (H.stage j.val).Carrier) (tail : ℝ → (H.stage first).Carrier),
      (∀ j, ∀ r ∈ uIoo (lo j) (hi j),
        (SO j).base.metric (T - r ^ 2) = H.stageMetric j.val (T - r ^ 2)) →
      (∀ r ∈ uIoo (hi ⟨first, le_rfl, hle⟩) v,
        ST.base.metric (T - r ^ 2) = H.stageMetric first (T - r ^ 2)) →
      (∀ j, EqOn (beta j) (gamma j) (uIoo (lo j) (hi j))) →
      EqOn tail (gamma ⟨first, le_rfl, hle⟩) (uIoo (hi ⟨first, le_rfl, hle⟩) v) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j, w r * lRegularizedLagrangian (SO j) T (beta j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (SS i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v, w r * lRegularizedLagrangian ST T tail r) := by
  intro J E jo jn lo hi gamma hbounds hlo hInt w hw W DS SS eta hseam
    DO DT SO ST beta tail hmetricO hmetricT hbeta htail
  rw [H.sum_weighted_stage_action_eq_collar_action first last hle ha hav hupper hpast
    lo hi gamma hbounds hlo hInt w hw W DS SS eta hseam]
  have hO : (∑ j : J, ∫ r in lo j..hi j,
      w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
      ∑ j : J, ∫ r in lo j..hi j, w r * lRegularizedLagrangian (SO j) T (beta j) r := by
    apply Finset.sum_congr rfl
    intro j _
    exact (H.weighted_integral_eq_stage_of_eqOn j.val (SO j) T (lo j) (hi j)
      (beta j) (gamma j) w (hmetricO j) (hbeta j)).symm
  rw [hO, H.weighted_integral_eq_stage_of_eqOn first ST T _ v tail _ w hmetricT htail]

private theorem smooth_survivor_weighted_action_eq_of_projections
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S)
    (oldMap : X → (H.stage i.castSucc).Carrier)
    (newMap : X → (H.stage i.succ).Carrier)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ oldMap)
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ newMap)
    (T : ℝ) {c clock d : ℝ} (hc : c ≤ clock) (hd : clock ≤ d)
    (hclock : ∀ r ∈ Icc c d, T - r ^ 2 ∈ D.carrier)
    (hmetricOld : ∀ r ∈ Ioo clock d, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.castSucc (T - r ^ 2)) oldMap hold)
    (hmetricNew : ∀ r ∈ Ioo c clock, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.succ (T - r ^ 2)) newMap hnew)
    (eta : ℝ → X) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta)
    (gammaOld : ℝ → (H.stage i.castSucc).Carrier)
    (gammaNew : ℝ → (H.stage i.succ).Carrier)
    (hOld : EqOn (oldMap ∘ eta) gammaOld (Icc clock d))
    (hNew : EqOn (newMap ∘ eta) gammaNew (Icc c clock))
    (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :
    (∫ r in c..d, weight r * lRegularizedLagrangian S T eta r) =
      (∫ r in c..clock,
        weight r * H.stageRegularizedLagrangian i.succ T gammaNew r) +
      ∫ r in clock..d,
        weight r * H.stageRegularizedLagrangian i.castSucc T gammaOld r := by
  have hcd := hc.trans hd
  have hLcont := lRegularizedLagrangian_continuousOn_carrier S hS eta heta
  have hLag := hLcont.comp (s := Icc c d)
    (f := fun r : ℝ => (T, r))
    (continuous_const.prodMk continuous_id).continuousOn (fun r hr => hclock r hr)
  have hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d :=
    hLag.intervalIntegrable_of_Icc hcd
  have hintWeighted :
      IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T eta r)
        volume c d :=
    hint.continuousOn_mul (by simpa only [uIcc_of_le hcd] using hweight)
  have hintLeft :
      IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T eta r)
        volume c clock :=
    hintWeighted.mono_set (by
      simpa only [uIcc_of_le hc, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hd)
  have hintRight :
      IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T eta r)
        volume clock d :=
    hintWeighted.mono_set (by
      simpa only [uIcc_of_le hd, uIcc_of_le hcd] using Icc_subset_Icc hc le_rfl)
  have htransfer (j : Fin (H.eventCount + 1))
      (f : X → (H.stage j).Carrier)
      (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
      (gamma : ℝ → (H.stage j).Carrier) {l r : ℝ} (hlr : l ≤ r)
      (hmetric : ∀ t ∈ Ioo l r, S.base.metric (T - t ^ 2) =
        localPullMetric (H.stageMetric j (T - t ^ 2)) f hf)
      (hproj : EqOn (f ∘ eta) gamma (Icc l r)) :
      (∫ t in l..r, weight t * lRegularizedLagrangian S T eta t) =
        ∫ t in l..r, weight t * H.stageRegularizedLagrangian j T gamma t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [uIoo_of_le hlr] at ht
    have hprojOpen : EqOn (f ∘ eta) gamma (Ioo l r) :=
      hproj.mono Ioo_subset_Icc_self
    have heq : f ∘ eta =ᶠ[𝓝 t] gamma :=
      hprojOpen.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
    have hlag := H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hf T
      (heta.mdifferentiable one_ne_zero t) (hmetric t ht)
    rw [← hlag]
    have hvel := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold stageRegularizedLagrangian lVelocity
    rw [hvel, heq.self_of_nhds]
    rfl
  have hleft := htransfer i.succ newMap hnew gammaNew hc hmetricNew hNew
  have hright := htransfer i.castSucc oldMap hold gammaOld hd hmetricOld hOld
  calc
    _ = (∫ r in c..clock, weight r * lRegularizedLagrangian S T eta r) +
        ∫ r in clock..d, weight r * lRegularizedLagrangian S T eta r :=
      (intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight).symm
    _ = _ := congrArg₂ (fun x y : ℝ => x + y) hleft hright

/-- The weighted action of the original history is exactly the weighted sum of
its actual smooth ordinary, survivor, and tail curves. The survivor split is
derived from the actual pullback metrics and original projected curves.
No weighted seam identity or minimum is an input. -/
theorem sum_weighted_stage_action_eq_smooth_collar_action_of_physical_projections
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (weight : ℝ → ℝ), ContinuousOn weight (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DS : E → RealTimeInterval)
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (eta : (i : E) → ℝ → W i),
      (∀ i, IsSolutionOn (SS i)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ (DS i).carrier) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (eta i)) →
      (∀ i, EqOn (fun r => (eta i r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (eta i r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
    ∀ (DO : J → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (beta : (j : J) → ℝ → (H.stage j.val).Carrier) (tail : ℝ → (H.stage first).Carrier),
      (∀ j, ∀ r ∈ uIoo (lo j) (hi j),
        (SO j).base.metric (T - r ^ 2) = H.stageMetric j.val (T - r ^ 2)) →
      (∀ r ∈ uIoo (hi ⟨first, le_rfl, hle⟩) v,
        ST.base.metric (T - r ^ 2) = H.stageMetric first (T - r ^ 2)) →
      (∀ j, EqOn (beta j) (gamma j) (uIoo (lo j) (hi j))) →
      EqOn tail (gamma ⟨first, le_rfl, hle⟩) (uIoo (hi ⟨first, le_rfl, hle⟩) v) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          weight r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j,
          weight r * lRegularizedLagrangian (SO j) T (beta j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
          weight r * lRegularizedLagrangian (SS i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v,
          weight r * lRegularizedLagrangian ST T tail r) := by
  intro J E jo jn lo hi gamma hbounds hlo hInt weight hweight
    W FC DS SS hold hnew eta hSS hclockS hmetricOld hmetricNew heta hprojectOld hprojectNew
    DO DT SO ST beta tail hmetricO hmetricT hbeta htail
  have ho (i : E) : H.regularizedStageStart T a i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  have haC (i : E) : a ≤ hi (jn i) :=
    (H.regularizedStage_bounds ha hav hupper hpast (jn i)).1.trans
      ((hbounds (jn i)).1.trans (hbounds (jn i)).2.1)
  have hdV (i : E) : lo (jo i) ≤ v :=
    (hbounds (jo i)).2.1.trans ((hbounds (jo i)).2.2.trans
      (H.regularizedStage_bounds ha hav hupper hpast (jo i)).2.2)
  have hseam (i : E) :
      (∫ r in hi (jn i)..lo (jo i),
        weight r * lRegularizedLagrangian (SS i) T (eta i) r) =
        (∫ r in hi (jn i)..Real.sqrt (T - H.time i.val.succ),
          weight r * H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
        ∫ r in Real.sqrt (T - H.time i.val.succ)..lo (jo i),
          weight r * H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r := by
    exact H.smooth_survivor_weighted_action_eq_of_projections i.val (SS i) (hSS i)
      (fun z : W i => z.val.val) (fun z : W i => FC i z.val) (hold i) (hnew i)
      T (hcw i) (hwd i) (hclockS i) (hmetricOld i) (hmetricNew i) (eta i) (heta i)
      (gamma (jo i)) (gamma (jn i)) (hprojectOld i) (hprojectNew i)
      weight (hweight.mono (Icc_subset_Icc (haC i) (hdV i)))
  exact H.sum_weighted_stage_action_eq_smooth_collar_action first last hle ha hav hupper hpast
    lo hi gamma hbounds hlo hInt weight hweight W DS SS eta hseam
    DO DT SO ST beta tail hmetricO hmetricT hbeta htail

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
