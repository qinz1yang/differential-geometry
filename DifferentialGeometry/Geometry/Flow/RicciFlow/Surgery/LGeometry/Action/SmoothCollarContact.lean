import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarCompetitors

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u

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

/-- The original action partitions into a genuine prefix, ordinary pieces,
collar pieces, and the past tail. The prefix is retained without a zero-length
hypothesis. -/
private theorem sum_stage_action_eq_prefix_add_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) →
      (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
        H.stageRegularizedAction last T (gamma ⟨last, hle, le_rfl⟩)
          0 (lo ⟨last, hle, le_rfl⟩) +
        (∑ j : J, H.stageRegularizedAction j.val T (gamma j) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i))) +
        H.stageRegularizedAction first T (gamma ⟨first, le_rfl, hle⟩)
          (hi ⟨first, le_rfl, hle⟩) v := by
  classical
  intro J E jo jn lo hi gamma hbounds hInt W D S eta hseam
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper0
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  let f (j : J) (r : ℝ) := H.stageRegularizedLagrangian j.val T (gamma j) r
  have hfull (j : J) : IntervalIntegrable (f j) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := hInt j
  have hparts (j : J) :
      (∫ r in H.regularizedStageStart T 0 j.val..H.regularizedStageEnd T v j.val, f j r) =
        (∫ r in H.regularizedStageStart T 0 j.val..lo j, f j r) +
        (∫ r in lo j..hi j, f j r) +
        (∫ r in hi j..H.regularizedStageEnd T v j.val, f j r) := by
    have hs := hbounds j
    have hordered := hs.1.trans (hs.2.1.trans hs.2.2)
    have hleft := (hfull j).mono_set (show
        uIcc (H.regularizedStageStart T 0 j.val) (lo j) ⊆
        uIcc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.1, uIcc_of_le hordered]
      exact Icc_subset_Icc le_rfl (hs.2.1.trans hs.2.2))
    have hmid := (hfull j).mono_set (show uIcc (lo j) (hi j) ⊆
        uIcc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.1, uIcc_of_le hordered]
      exact Icc_subset_Icc hs.1 hs.2.2)
    have hright := (hfull j).mono_set (show
        uIcc (hi j) (H.regularizedStageEnd T v j.val) ⊆
        uIcc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.2, uIcc_of_le hordered]
      exact Icc_subset_Icc (hs.1.trans hs.2.1) le_rfl)
    rw [intervalIntegral.integral_add_adjacent_intervals hleft hmid,
      intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmid) hright]
  calc
    _ = ∑ j : J, (H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (lo j) +
        H.stageRegularizedAction j.val T (gamma j) (lo j) (hi j) +
        H.stageRegularizedAction j.val T (gamma j)
          (hi j) (H.regularizedStageEnd T v j.val)) :=
      Finset.sum_congr rfl (fun j _ => hparts j)
    _ = _ := by
      rw [H.sum_stage_parts_eq_endpoints_add_events first last hle]
      simp only [hstart, hend]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      change H.stageRegularizedAction i.val.succ T (gamma (jn i))
        (hi (jn i)) (H.regularizedStageEnd T v i.val.succ) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (H.regularizedStageStart T 0 i.val.castSucc) (lo (jo i)) = _
      rw [ho, hn]
      exact (hseam i).symm

/-- The central ordinary, survivor, and tail curves have exactly the original
history action, including the original prefix before the first collar cut.
The survivor action is obtained from its actual pullback metrics and projections.
No cost equality, minimum, or contact identity is an input. -/
theorem smooth_collar_action_eq_sum_stage_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : J) → ℝ → (H.stage j.val).Carrier) (lo hi : J → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : J → RealTimeInterval) (DS : E → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (ordinary : (j : J) → ℝ → (H.stage j.val).Carrier)
      (survivor : (i : E) → ℝ → W i) (tail : ℝ → (H.stage first).Carrier),
      (∀ i, IsSolutionOn (SS i)) →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ (DS i).carrier) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => F i z.val) (hnew i)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (survivor i)) →
      (∀ j, EqOn (ordinary j) (gamma j) (Icc (lo j) (hi j))) →
      (∀ i, EqOn (fun r => (survivor i r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => F i (survivor i r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      EqOn tail (gamma jf) (Icc (hi jf) v) →
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
        (∑ j : J, lRegularizedAction (SO j) T (ordinary j) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (SS i) T (survivor i) (hi (jn i)) (lo (jo i))) +
        lRegularizedAction ST T tail (hi jf) v =
      ∑ j : J, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) := by
  classical
  intro J E jo jn jf jl gamma lo hi hbounds hInt
    W F DO DS DT SO SS ST hold hnew ordinary survivor tail hSS
    hmetricO hmetricT hcross hclockS hmetricOld hmetricNew hsurvivor
    hordinary hprojectOld hprojectNew htail
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  have hseam (i : E) : lRegularizedAction (SS i) T (survivor i)
      (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)) := by
    obtain ⟨_, _, _, _, _, hactions⟩ := H.smooth_survivor_curve_projected_actions i.val
      (SS i) (hSS i) (fun z : W i => z.val.val) (fun z : W i => F i z.val)
      (hold i) (hnew i) (hcross i) T (hcw i) (hwd i) (hclockS i)
      (hmetricOld i) (hmetricNew i) (survivor i) (hsurvivor i)
    rw [← hactions]
    congr 1
    · apply H.stageRegularizedAction_congr
      intro r hr
      rw [uIoo_of_le (hcw i)] at hr
      exact hprojectNew i (Ioo_subset_Icc_self hr)
    · apply H.stageRegularizedAction_congr
      intro r hr
      rw [uIoo_of_le (hwd i)] at hr
      exact hprojectOld i (Ioo_subset_Icc_self hr)
  have hO (j : J) : lRegularizedAction (SO j) T (ordinary j) (lo j) (hi j) =
      H.stageRegularizedAction j.val T (gamma j) (lo j) (hi j) := by
    have heq : EqOn (ordinary j) (gamma j) (uIoo (lo j) (hi j)) := by
      intro r hr
      rw [uIoo_of_le (hbounds j).2.1] at hr
      exact hordinary j (Ioo_subset_Icc_self hr)
    simpa only [lRegularizedAction, stageRegularizedAction, one_mul] using
      H.weighted_integral_eq_stage_of_eqOn j.val (SO j) T (lo j) (hi j)
        (ordinary j) (gamma j) (fun _ => 1) (fun r _ => hmetricO j (T - r ^ 2)) heq
  have hTail : lRegularizedAction ST T tail (hi jf) v =
      H.stageRegularizedAction first T (gamma jf) (hi jf) v := by
    have htv : hi jf ≤ v := by simpa only [jf, hend] using (hbounds jf).2.2
    have heq : EqOn tail (gamma jf) (uIoo (hi jf) v) := by
      intro r hr
      rw [uIoo_of_le htv] at hr
      exact htail (Ioo_subset_Icc_self hr)
    simpa only [lRegularizedAction, stageRegularizedAction, one_mul] using
      H.weighted_integral_eq_stage_of_eqOn first ST T (hi jf) v
        tail (gamma jf) (fun _ => 1) (fun r _ => hmetricT (T - r ^ 2)) heq
  rw [show (∑ j : J, lRegularizedAction (SO j) T (ordinary j) (lo j) (hi j)) =
      ∑ j : J, H.stageRegularizedAction j.val T (gamma j) (lo j) (hi j) from
        Finset.sum_congr rfl (fun j _ => hO j), hTail]
  exact (H.sum_stage_action_eq_prefix_add_collar_action first last hle hv hupper hpast
    lo hi gamma hbounds hInt W DS SS survivor hseam).symm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
