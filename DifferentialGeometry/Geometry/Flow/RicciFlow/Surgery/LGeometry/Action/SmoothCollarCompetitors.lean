import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CollarCompetitors
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v

theorem smooth_curve_projected_action
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (f : X → (H.stage j).Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T c d : ℝ) (eta : ℝ → X) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d)
    (hmetric : ∀ r ∈ uIoo c d, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric j (T - r ^ 2)) f hf) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (f ∘ eta) c d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j T (f ∘ eta)) volume c d ∧
      H.stageRegularizedAction j T (f ∘ eta) c d = lRegularizedAction S T eta c d := by
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (f ∘ eta) :=
    (hf.contMDiff.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp heta
  have heq : EqOn (lRegularizedLagrangian S T eta)
      (H.stageRegularizedLagrangian j T (f ∘ eta)) (uIoo c d) := by
    intro r hr
    exact (H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hf T
      (heta.mdifferentiable one_ne_zero r) (hmetric r hr)).symm
  exact ⟨Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hcomp.contMDiffOn,
    hint.congr_uIoo heq, H.stageRegularizedAction_comp_eq_of_localPullMetric j S f hf T c d
      eta heta hmetric⟩

theorem smooth_survivor_curve_projected_actions
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S)
    (oldMap : X → (H.stage i.castSucc).Carrier)
    (newMap : X → (H.stage i.succ).Carrier)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ oldMap)
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ newMap)
    (hcross : ∀ x, (H.event i).RegularCrossing (oldMap x) (newMap x))
    (T : ℝ) {c w d : ℝ} (hcw : c ≤ w) (hwd : w ≤ d)
    (hclock : ∀ r ∈ Icc c d, T - r ^ 2 ∈ D.carrier)
    (hmetricOld : ∀ r ∈ Ioo w d, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.castSucc (T - r ^ 2)) oldMap hold)
    (hmetricNew : ∀ r ∈ Ioo c w, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.succ (T - r ^ 2)) newMap hnew)
    (eta : ℝ → X) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (newMap ∘ eta) c w ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel (oldMap ∘ eta) w d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian i.succ T (newMap ∘ eta)) volume c w ∧
      IntervalIntegrable (H.stageRegularizedLagrangian i.castSucc T (oldMap ∘ eta)) volume w d ∧
      (∃ z : (H.event i).old, z.val.val = oldMap (eta w) ∧
        (H.event i).oldOutput z = newMap (eta w)) ∧
      H.stageRegularizedAction i.succ T (newMap ∘ eta) c w +
          H.stageRegularizedAction i.castSucc T (oldMap ∘ eta) w d =
        lRegularizedAction S T eta c d := by
  have hcd := hcw.trans hwd
  have hc := lRegularizedLagrangian_continuousOn_carrier S hS eta heta
  have hLag := hc.comp (s := Icc c d)
    (f := fun r : ℝ => (T, r))
    (continuous_const.prodMk continuous_id).continuousOn (fun r hr => hclock r hr)
  have hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d :=
    hLag.intervalIntegrable_of_Icc hcd
  have hintLeft : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c w :=
    hint.mono_set (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hintRight : IntervalIntegrable (lRegularizedLagrangian S T eta) volume w d :=
    hint.mono_set (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  obtain ⟨hACLeft, hIntLeft, hActionLeft⟩ :=
    H.smooth_curve_projected_action i.succ S newMap hnew T c w eta heta hintLeft
      (by simpa only [uIoo_of_le hcw] using hmetricNew)
  obtain ⟨hACRight, hIntRight, hActionRight⟩ :=
    H.smooth_curve_projected_action i.castSucc S oldMap hold T w d eta heta hintRight
      (by simpa only [uIoo_of_le hwd] using hmetricOld)
  refine ⟨hACLeft, hACRight, hIntLeft, hIntRight, ?_, ?_⟩
  · obtain ⟨z, _, hz, hzout⟩ := hcross (eta w)
    exact ⟨z, hz, hzout⟩
  · rw [hActionLeft, hActionRight]
    exact lRegularizedAction_add S T eta c w d hintLeft hintRight

/-- The original fixed prefix and the same smooth ordinary, survivor and tail
pieces form a genuine competitor in the actual history. Every metric equality
is with that history. The past endpoint and the final clock are unrestricted
apart from their actual domains; no minimum or cost estimate is an input. -/
theorem regularizedCost_le_smooth_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) (B : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x) :
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
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume 0 (lo jl) →
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
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ j, ∀ r ∈ Icc (lo j) (hi j), T - r ^ 2 ∈ (DO j).carrier) →
      (∀ r ∈ Icc (hi jf) v, T - r ^ 2 ∈ DT.carrier) →
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
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (ordinary j)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (survivor i)) →
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 tail →
      ordinary jl (lo jl) = gamma jl (lo jl) →
      (∀ i, ordinary (jo i) (lo (jo i)) = (survivor i (lo (jo i))).val.val) →
      (∀ i, ordinary (jn i) (hi (jn i)) = F i (survivor i (hi (jn i))).val) →
      ordinary jf (hi jf) = tail (hi jf) →
      H.regularizedCost first last hle T B 0 v (gamma jl 0) (tail v) ≤
        ((H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
          (∑ j : J, lRegularizedAction (SO j) T (ordinary j) (lo j) (hi j)) +
          (∑ i : E, lRegularizedAction (SS i) T (survivor i) (hi (jn i)) (lo (jo i))) +
          lRegularizedAction ST T tail (hi jf) v : ℝ) : WithTop ℝ) := by
  classical
  intro J E jo jn jf jl gamma lo hi hbounds hprefixAC hprefixInt
    W F DO DS DT SO SS ST hold hnew ordinary survivor tail hSO hSS hST
    hmetricO hmetricT hclockO hclockT hcross hclockS hmetricOld hmetricNew
    hordinary hsurvivor htail hfix hjoinOld hjoinNew hjoinTail
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
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  have hoinj : Function.Injective jo := by
    intro i k h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun j : J => j.val.val) h
  have hninj : Function.Injective jn := by
    intro i k h
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg (fun j : J => j.val.val) h
    change i.val.val + 1 = k.val.val + 1 at hv
    omega
  have hone (i : E) : jo i ≠ jl := by
    intro h
    have he := congrArg (fun j : J => j.val.val) h
    have hi := i.property.2
    change i.val.val = last.val at he
    change i.val.val + 1 ≤ last.val at hi
    omega
  have hnne (i : E) : jn i ≠ jf := by
    intro h
    have he := congrArg (fun j : J => j.val.val) h
    have hi := i.property.1
    change i.val.val + 1 = first.val at he
    change first.val ≤ i.val.val at hi
    omega
  have hocover (j : J) : j = jl ∨ ∃ i, jo i = j := by
    by_cases hj : j = jl
    · exact Or.inl hj
    · right
      have hneq : j.val.val ≠ last.val := fun h => hj (Subtype.ext (Fin.ext h))
      let i : Fin H.eventCount := ⟨j.val.val, by
        have hbound := j.property.2
        have hlast := last.isLt
        change j.val.val ≤ last.val at hbound
        omega⟩
      refine ⟨⟨i, j.property.1, ?_⟩, rfl⟩
      change j.val.val + 1 ≤ last.val
      have hbound := j.property.2
      change j.val.val ≤ last.val at hbound
      omega
  have hncover (j : J) : j = jf ∨ ∃ i, jn i = j := by
    by_cases hj : j = jf
    · exact Or.inl hj
    · right
      have hneq : j.val.val ≠ first.val := fun h => hj (Subtype.ext (Fin.ext h))
      have hpos : 0 < j.val.val := by
        have hbound := j.property.1
        change first.val ≤ j.val.val at hbound
        omega
      let i : Fin H.eventCount := ⟨j.val.val - 1, by have hb := j.val.isLt; omega⟩
      refine ⟨⟨i, ?_, ?_⟩, ?_⟩
      · change first.val ≤ j.val.val - 1
        have hbound := j.property.1
        change first.val ≤ j.val.val at hbound
        omega
      · change j.val.val - 1 + 1 ≤ last.val
        have hbound := j.property.2
        change j.val.val ≤ last.val at hbound
        omega
      · apply Subtype.ext
        apply Fin.ext
        change j.val.val - 1 + 1 = j.val.val
        omega
  have hfill (V : J → Type u) (endpoint : J) (p : E → J)
      (hinj : Function.Injective p) (hne : ∀ i, p i ≠ endpoint)
      (hcover : ∀ j, j = endpoint ∨ ∃ i, p i = j)
      (v0 : V endpoint) (vE : ∀ i, V (p i)) :
      ∃ out : ∀ j, V j, out endpoint = v0 ∧ ∀ i, out (p i) = vE i := by
    have hchoose (j : J) : ∃ y : V j,
        (j = endpoint → HEq y v0) ∧ (∀ i, p i = j → HEq y (vE i)) := by
      rcases hcover j with rfl | ⟨i, rfl⟩
      · exact ⟨v0, fun _ => HEq.rfl, fun i h => (hne i h).elim⟩
      · refine ⟨vE i, fun h => (hne i h).elim, ?_⟩
        intro k hk
        have he := hinj hk
        subst k
        rfl
    choose out hout using hchoose
    exact ⟨out, eq_of_heq ((hout endpoint).1 rfl),
      fun i => eq_of_heq ((hout (p i)).2 i rfl)⟩
  obtain ⟨left, hleftLast, hleftOld⟩ := hfill (fun j => ℝ → (H.stage j.val).Carrier)
    jl jo hoinj hone hocover (gamma jl) (fun i r => (survivor i r).val.val)
  obtain ⟨right, hrightFirst, hrightNew⟩ := hfill (fun j => ℝ → (H.stage j.val).Carrier)
    jf jn hninj hnne hncover tail (fun i r => F i (survivor i r).val)
  have hpiece (j : J) {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D)
      (hS : IsSolutionOn S) (hmetric : ∀ t, S.base.metric t = H.stageMetric j.val t)
      (eta : ℝ → (H.stage j.val).Carrier) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta)
      {a b : ℝ} (hab : a ≤ b) (hclock : ∀ r ∈ Icc a b, T - r ^ 2 ∈ D.carrier) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta a b ∧
        IntervalIntegrable (H.stageRegularizedLagrangian j.val T eta) volume a b ∧
        H.stageRegularizedAction j.val T eta a b = lRegularizedAction S T eta a b := by
    have hlag : H.stageRegularizedLagrangian j.val T eta = lRegularizedLagrangian S T eta := by
      funext r
      simp only [stageRegularizedLagrangian, lRegularizedLagrangian,
        SolutionOn.scalar, SolutionFamily.scalar, hmetric]
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS eta heta
    have hcont := hc.comp (s := Icc a b) (f := fun r : ℝ => (T, r))
      (continuous_const.prodMk continuous_id).continuousOn (fun r hr => hclock r hr)
    refine ⟨Manifold.absolutelyContinuousOnInterval_of_contMDiffOn heta.contMDiffOn, ?_, ?_⟩
    · rw [hlag]
      exact hcont.intervalIntegrable_of_Icc hab
    · unfold stageRegularizedAction lRegularizedAction
      rw [hlag]
  have hO (j : J) := hpiece j (SO j) (hSO j) (hmetricO j)
    (ordinary j) (hordinary j) (hbounds j).2.1 (hclockO j)
  have htailBound : hi jf ≤ v := by simpa only [jf, hend] using (hbounds jf).2.2
  have hT := hpiece jf ST hST hmetricT tail htail htailBound hclockT
  have hSproj (i : E) := H.smooth_survivor_curve_projected_actions i.val
    (SS i) (hSS i) (fun z : W i => z.val.val) (fun z : W i => F i z.val)
    (hold i) (hnew i) (hcross i) T (hcw i) (hwd i) (hclockS i)
    (hmetricOld i) (hmetricNew i) (survivor i) (hsurvivor i)
  have hleftAC (j : J) : Manifold.absolutelyContinuousOnInterval ThreeModel (left j)
      (H.regularizedStageStart T 0 j.val) (lo j) := by
    rcases hocover j with rfl | ⟨i, rfl⟩
    · rw [hleftLast]
      simpa only [jl, hstart] using hprefixAC
    · rw [hleftOld]
      simpa only [jo, ho i, Function.comp_def] using (hSproj i).2.1
  have hrightAC (j : J) : Manifold.absolutelyContinuousOnInterval ThreeModel (right j)
      (hi j) (H.regularizedStageEnd T v j.val) := by
    rcases hncover j with rfl | ⟨i, rfl⟩
    · rw [hrightFirst]
      simpa only [jf, hend] using hT.1
    · rw [hrightNew]
      simpa only [jn, hn i, Function.comp_def] using (hSproj i).1
  have hleftInt (j : J) : IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left j))
      volume (H.regularizedStageStart T 0 j.val) (lo j) := by
    rcases hocover j with rfl | ⟨i, rfl⟩
    · rw [hleftLast]
      simpa only [jl, hstart] using hprefixInt
    · rw [hleftOld]
      simpa only [jo, ho i, Function.comp_def] using (hSproj i).2.2.2.1
  have hrightInt (j : J) : IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right j))
      volume (hi j) (H.regularizedStageEnd T v j.val) := by
    rcases hncover j with rfl | ⟨i, rfl⟩
    · rw [hrightFirst]
      simpa only [jf, hend] using hT.2.1
    · rw [hrightNew]
      simpa only [jn, hn i, Function.comp_def] using (hSproj i).2.2.1
  have hmatchL (j : J) : left j (lo j) = ordinary j (lo j) := by
    rcases hocover j with rfl | ⟨i, rfl⟩
    · rw [hleftLast]
      exact hfix.symm
    · rw [hleftOld]
      exact (hjoinOld i).symm
  have hmatchR (j : J) : ordinary j (hi j) = right j (hi j) := by
    rcases hncover j with rfl | ⟨i, rfl⟩
    · rw [hrightFirst]
      exact hjoinTail
    · rw [hrightNew]
      exact hjoinNew i
  have hseam (i : E) : lRegularizedAction (SS i) T (survivor i) (hi (jn i)) (lo (jo i)) =
      H.stageRegularizedAction i.val.succ T (right (jn i)) (hi (jn i))
        (Real.sqrt (T - H.time i.val.succ)) +
      H.stageRegularizedAction i.val.castSucc T (left (jo i))
        (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)) := by
    rw [hrightNew, hleftOld]
    exact (hSproj i).2.2.2.2.2.symm
  have hcost := H.regularizedCost_le_collar_piece_action first last hle hv hupper hpast B hscalar
    lo hi left ordinary right hbounds hleftAC (fun j => (hO j).1) hrightAC
    hleftInt (fun j => (hO j).2.1) hrightInt hmatchL hmatchR W F DS SS survivor hcross
    (fun i => by rw [hleftOld]) (fun i => by rw [hrightNew]) hseam
  have hOrdAction : (∑ j : J, H.stageRegularizedAction j.val T (ordinary j) (lo j) (hi j)) =
      ∑ j : J, lRegularizedAction (SO j) T (ordinary j) (lo j) (hi j) :=
    Finset.sum_congr rfl (fun j _ => (hO j).2.2)
  rw [hleftLast, hrightFirst, hOrdAction, hT.2.2] at hcost
  exact hcost

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
