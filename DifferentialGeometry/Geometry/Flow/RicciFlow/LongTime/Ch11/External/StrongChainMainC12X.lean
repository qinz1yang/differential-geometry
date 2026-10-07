import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongChainRestrictInvC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongSupplyV2PackMainC12X

/-!
# S16 chain layer: tower lift of the producer `strong` invariant (C12X, S16 G4 / G5a)

**Conditional; not counted as S16 supplied (R-S16 D-5).** The premise `hstrong` is, verbatim
for every state of the chain, the full-history `strong` field of the producer spec
`docs/geometrization/chapter8/out/CH12X-S16-PRODUCER-SPEC.md` §1 (constants `C1 C2`, accuracy
`C.epsilon`). Once ch8 adds that field to `PreparedSpatialState`, `hstrong n` is
`(S.state n).strong` and the theorems below become unconditional.

* `hfull_of_stateStrong_C12X`: the premise `hfull` of S16C's
  `strongCanonicalSupplyV2_of_towerFull_C12X` (`ρ := q.neckRadius`, `ε := C.epsilon`). For a
  slice at time `t`, `N := ⌈t⌉`: `s.history = (H.restrict N).restrict t` with
  `H := (S.state (N+1)).history` and `t ≤ N < 3^N = E_{N+1}`; the field at `t` on `H`, then TB
  (`historyStrongNeckFull_restrict_C12X`, `b := t`) and TA along `restrict_restrict`.
* `strongCanonicalSupplyV2_of_stateStrong_C12X`: through S16C's packaging.
* `exists_w1_params_strong_C12X`: the conclusion of `w1_params_of_preparedSpatialChain_C11P2`
  together with `StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2` on the same `(F, q)`
  (constants `C1 C2` of the `canonical` field).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open Set Filter TopologicalSpace
open scoped Topology NNReal ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-- **Tower lift of the `strong` field (conditional, R-S16 D-5).** -/
theorem hfull_of_stateStrong_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hpref : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t)
    (C1 C2 : ℝ)
    (hstrong : ∀ n : ℕ, ∀ t : Icc (0 : ℝ) (S.state n).history.toHistory.horizon,
      (t : ℝ) < preparedSpatialHorizon n →
      (S.state n).history.time ((S.state n).history.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : ((S.state n).history.toHistory.stageAt t).Carrier,
        ((S.state n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) C.epsilon C1 C2 x,
          W.capTubeHasNeckChart C.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ) (G : ((S.state n).history.stage
                ((S.state n).history.toHistory.activeStage t)).IncomingSlab
                ((S.state n).history.time ((S.state n).history.toHistory.activeStage t)) s'),
              (∀ τ ∈ Icc ((S.state n).history.time
                  ((S.state n).history.toHistory.activeStage t)) (t : ℝ),
                G.flow.base.metric τ = (S.state n).history.toHistory.stageMetric
                  ((S.state n).history.toHistory.activeStage t) τ) ∧
              (S.state n).history.toHistory.HistoryStrongNeckFull_C12X
                ((S.state n).history.toHistory.activeStage t) G C.epsilon x t) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric C.epsilon C1 C2 x,
        W.capTubeHasNeckChart C.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (s' : ℝ)
            (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
            (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
              G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
            s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G C.epsilon x
              s.time := by
  obtain ⟨Ftower, Fctrl⟩ := F
  change Ftower = S.tower at hTower
  subst hTower
  refine ⟨0, fun s _ x hR => ?_⟩
  have htN : s.time ≤ ((⌈s.time⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hNlt : ((⌈s.time⌉₊ : ℕ) : ℝ) < (3 : ℝ) ^ ⌈s.time⌉₊ := nat_lt_three_pow _
  let H := (S.state (⌈s.time⌉₊ + 1)).history
  have hHhor : H.toHistory.horizon = (3 : ℝ) ^ ⌈s.time⌉₊ := (S.state _).horizon_eq
  let a : Icc (0 : ℝ) H.toHistory.horizon := S.observationTime ⌈s.time⌉₊
  let t' : Icc (0 : ℝ) (H.toHistory.restrict a).horizon := ⟨s.time, s.positive.le, htN⟩
  let tH : Icc (0 : ℝ) H.toHistory.horizon := ⟨t'.1, t'.2.1, t'.2.2.trans a.2.2⟩
  have R1 : (H.toHistory.restrict tH).SamePresentation s.history :=
    (H.toHistory.restrict_restrict a t').symm
  have hcast : Fin.cast (congrArg (· + 1) R1.count_eq)
      (Fin.last (H.toHistory.restrict tH).eventCount) = Fin.last s.history.eventCount :=
    Fin.ext R1.count_eq
  have hstage : (H.toHistory.restrict tH).stage (Fin.last _) = s.stage :=
    (R1.stage_eq _).trans (congrArg s.history.stage hcast)
  have htime : (H.toHistory.restrict tH).time (Fin.last _) =
      s.history.time (Fin.last s.history.eventCount) :=
    (R1.time_eq _).trans (congrArg s.history.time hcast)
  have hdom : s.time ∈ (H.toHistory.restrict tH).stageDomain (Fin.last _) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨(H.toHistory.restrict tH).time_le_horizon, le_rfl⟩
  have hmetric : HEq (H.toHistory.stageMetric (H.toHistory.activeStage tH) s.time) s.metric := by
    have h1 := H.toHistory.restrict_stageMetric tH (Fin.last _) s.time hdom
    have h2 := R1.metric_heq (Fin.last _) s.time hdom
    rw [hcast] at h2
    exact h1.symm.trans h2
  let xH : (H.toHistory.stageAt tH).Carrier := s16d_castPoint hstage.symm x
  have hxH : HEq xH x := s16d_castPoint_heq hstage.symm x
  have hscal := s16d_scalar_eq hstage hmetric hxH
  have hρ : q.neckRadius s.time = (S.state (⌈s.time⌉₊ + 1)).parameters.neckRadius s.time :=
    hpref _ s.time ⟨s.positive.le, htN⟩
  have hthr : ((S.state (⌈s.time⌉₊ + 1)).parameters.neckRadius tH ^ 2)⁻¹ < metricScalarAt
      (H.toHistory.stageMetric (H.toHistory.activeStage tH) tH) xH := by
    change ((S.state (⌈s.time⌉₊ + 1)).parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt
      (H.toHistory.stageMetric (H.toHistory.activeStage tH) s.time) xH
    rw [← hρ]
    exact hR.trans_eq hscal.symm
  have hE : (tH : ℝ) < preparedSpatialHorizon (⌈s.time⌉₊ + 1) := by
    change s.time < (3 : ℝ) ^ ⌈s.time⌉₊
    linarith
  have hreg : H.time (H.toHistory.activeStage tH) < (tH : ℝ) := by
    change (H.toHistory.restrict tH).time (Fin.last _) < s.time
    rw [htime]
    exact s.preceding
  obtain ⟨W, hW, hneck⟩ := hstrong (⌈s.time⌉₊ + 1) tH hE hreg xH hthr
  obtain ⟨W', hW', hrefl⟩ := s16d_witness_transport hstage hmetric hxH W hW
  refine ⟨W', hW', fun nk' hnk' => ?_⟩
  obtain ⟨nk, hnk⟩ := hrefl nk' hnk'
  obtain ⟨s', G, hGa, hGf⟩ := hneck nk hnk
  have hK := H.toHistory.historyStrongNeckFull_restrict_C12X tH (Fin.last _) G hGf
  have hGK := H.toHistory.incomingAgree_restrict_last_C12X tH G (t := s.time) le_rfl hGa
  refine ⟨s', s16d_castSlab hstage htime G, ?_, ?_⟩
  · exact ObservedHistory.incomingAgree_of_samePresentation_last_C12X R1
      (s16d_castSlab_heq hstage htime G) le_rfl hGK
  · exact ObservedHistory.HistoryStrongNeckFull_C12X.of_samePresentation_C12X R1 R1.count_eq
      (s16d_castSlab_heq hstage htime G) hxH hK

/-- **S16 v2 from the `strong` field (conditional, R-S16 D-5)**：through S16C's packaging. -/
theorem strongCanonicalSupplyV2_of_stateStrong_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hpref : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t)
    (C1 C2 : ℝ)
    (hstrong : ∀ n : ℕ, ∀ t : Icc (0 : ℝ) (S.state n).history.toHistory.horizon,
      (t : ℝ) < preparedSpatialHorizon n →
      (S.state n).history.time ((S.state n).history.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : ((S.state n).history.toHistory.stageAt t).Carrier,
        ((S.state n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) C.epsilon C1 C2 x,
          W.capTubeHasNeckChart C.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ) (G : ((S.state n).history.stage
                ((S.state n).history.toHistory.activeStage t)).IncomingSlab
                ((S.state n).history.time ((S.state n).history.toHistory.activeStage t)) s'),
              (∀ τ ∈ Icc ((S.state n).history.time
                  ((S.state n).history.toHistory.activeStage t)) (t : ℝ),
                G.flow.base.metric τ = (S.state n).history.toHistory.stageMetric
                  ((S.state n).history.toHistory.activeStage t) τ) ∧
              (S.state n).history.toHistory.HistoryStrongNeckFull_C12X
                ((S.state n).history.toHistory.activeStage t) G C.epsilon x t) :
    StrongCanonicalSupplyV2_C11E F q.neckRadius C.epsilon C1 C2 :=
  strongCanonicalSupplyV2_of_towerFull_C12X
    (hfull_of_stateStrong_C12X S F hTower q hpref C1 C2 hstrong)

/-- **W1 + parameter-level enhanced fields + S16 (conditional, R-S16 D-5)**：the conclusion of
`w1_params_of_preparedSpatialChain_C11P2` and, on the same `(F, q)`, the S16 conjunct of
`a12Enhanced_of_chain_C11P2`'s `hext`, from the `strong` field with the constants of `canonical`. -/
theorem exists_w1_params_strong_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hstrong : ∀ n : ℕ, ∀ t : Icc (0 : ℝ) (S.state n).history.toHistory.horizon,
      (t : ℝ) < preparedSpatialHorizon n →
      (S.state n).history.time ((S.state n).history.toHistory.activeStage t) < (t : ℝ) →
      ∀ x : ((S.state n).history.toHistory.stageAt t).Carrier,
        ((S.state n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness ((S.state n).history.toHistory.stageMetric
            ((S.state n).history.toHistory.activeStage t) t) C.epsilon (max C.C1s C.Cbirth)
            (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon ∧
          ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
            ∃ (s' : ℝ) (G : ((S.state n).history.stage
                ((S.state n).history.toHistory.activeStage t)).IncomingSlab
                ((S.state n).history.time ((S.state n).history.toHistory.activeStage t)) s'),
              (∀ τ ∈ Icc ((S.state n).history.time
                  ((S.state n).history.toHistory.activeStage t)) (t : ℝ),
                G.flow.base.metric τ = (S.state n).history.toHistory.stageMetric
                  ((S.state n).history.toHistory.activeStage t) τ) ∧
              (S.state n).history.toHistory.HistoryStrongNeckFull_C12X
                ((S.state n).history.toHistory.activeStage t) G C.epsilon x t) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      F.tower = S.tower ∧ ε = C.epsilon ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t) ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
      CollarWindowSupply_C11E.{u} q ∧ ModelConstraintsSupply_C11E q εProf_C11E.{u} ∧
      ConeEpsilonSupply_C11E ε ∧ StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hρanti, hpref, -, hcan, hwin,
    hnc, -, hδlim, hrecent⟩ := S.exists_surgery_with_spatial_control_and_decay
  obtain ⟨hfixed, hrad, hord, hacc, -⟩ := hstatic
  refine ⟨F, q, κ, records, C.epsilon, max C.C1s C.Cbirth,
    max C.C2s (max C.Cbirth (C.Cgrad : ℝ)), hTower, rfl, ⟨hfixed, hrad, hord, hacc⟩, fun t ht => ?_,
    canonicalConstantsSupply_of_closedBirthConstants_C11A C, hκ, hκanti, hδanti, hρanti,
    hcan, hwin, hnc, hδlim, hrecent, collarWindowSupply_of_static_C11P2 hfixed hrad hP3,
    modelConstraintsSupply_of_static_C11P2 hacc hord hrad hprof,
    coneEpsilonSupply_of_closedBirth_C11P2 C,
    strongCanonicalSupplyV2_of_stateStrong_C12X S F hTower q (fun n t ht => (hpref n t ht).2.1)
      _ _ hstrong⟩
  change q.delta t = ((S.observation (Nat.ceil t)).parameters).delta t
  exact (hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩).1

end GC.LongTime.Ch11

end
