import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.FiniteObservationContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.SurgeryEventControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryEventVolumeBound

/-!
# S-CH11-FIX8 patched-at-path astra `GeometricObservationExtension`

来源：donor `GeometricObservationExtension.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 heartbeat 超限（`observation_initial_budget_eq` 末尾 `exact congrArg f (Sigma.ext hs hm)`
的 `isDefEq`）。本 port 只有 elaboration 层面修补（no statement / definition / proof idea altered；
不加 `set_option`）：
* `observation_initial_budget_eq` 的证明：不再对 `Sigma` 对用 `congrArg f`（要让 elaborator 展开 `f` 去
  匹配带 instance 的目标），改为对一般的 `P Q : OrientedThreeStage`、`g : P.Metric`、`g' : Q.Metric`
  先证同一等式（`subst` + `cases` 后 `rfl`），再 `exact key _ _ _ _ hs hm`。

本文件在原路径（patched-at-path）：下游 `NoncollapsedGeometricObservation` / `CommonScaffoldObservation`
有 `open private observation_initial_budget_eq from …GeometricObservationExtension`，所以不用 shim。
-/

set_option autoImplicit false

noncomputable section

namespace GC.GeneralFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem observation_initial_budget_eq {H K : ObservedHistory.{u}}
    (hp : H.IsPrefixOf K) (v C B : ℝ) :
    (Nat.card (ConnectedComponents (K.stage 0).Carrier) : ℝ) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel (K.stage 0).Carrier
            (K.initialMetric 0) univ).toReal / v) =
      Nat.card (ConnectedComponents (H.stage 0).Carrier) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
            (H.initialMetric 0) univ).toReal / v) := by
  have hs : K.stage 0 = H.stage 0 := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero]
      using hp.presentation.stage_eq 0
  have hm : HEq (K.initialMetric 0) (H.initialMetric 0) := by
    simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
      ObservedHistory.restrict_stage_zero] using hp.presentation.initialMetric_heq 0
  have key : ∀ (P Q : OrientedThreeStage.{u}) (g : P.Metric) (g' : Q.Metric),
      P = Q → HEq g g' →
      (Nat.card (ConnectedComponents P.Carrier) : ℝ) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel P.Carrier g univ).toReal / v) =
      (Nat.card (ConnectedComponents Q.Carrier) : ℝ) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel Q.Carrier g' univ).toReal / v) := by
    intro P Q g g' hPQ hgg'
    subst hPQ
    cases eq_of_heq hgg'
    rfl
  exact key _ _ _ _ hs hm

/-- Extend the selected records and preserve surgery control on the same finite observation. -/
theorem exists_geometric_observation_extension_preserving_control
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ w : ℝ, 0 < w →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                  (H.coreEvent i).outputMetric univ +
                ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * w) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
          ∃ (K : RetainedCoreHistory.{u})
            (A' : InitialIdentification P g K.toHistory) (q : CutoffParameters)
            (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
            (hc : H.eventCount ≤ K.eventCount),
            K.horizon = B ∧ A.IsPrefixOf A' ∧
            (HistoryEventControl H → HistoryEventControl K) ∧
            (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
              q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
            K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records (Fin.castLE hc i)).nominalRadius (old i).nominalRadius ∧
              HEq (records (Fin.castLE hc i)).delta (old i).delta ∧
              HEq (records (Fin.castLE hc i)).order (old i).order ∧
              HEq (records (Fin.castLE hc i)).neck (old i).neck ∧
              HEq (records (Fin.castLE hc i)).static (old i).static) ∧
            ∀ i : Fin K.eventCount,
              ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
                riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                    (K.coreEvent i).outputMetric univ +
                  ENNReal.ofReal
                    ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * min w v) ≤
                riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
                  (K.coreEvent i).terminal.metric F := by
  classical
  obtain ⟨p₀, δbound, ρbound, v, hδ, hρ, hv, step⟩ :=
    exists_geometric_observation_step P g B hB
  obtain ⟨a, ha, hfixed, hlower⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨p₀, δbound, ρbound, v, hδ, hρ, hv, ?_⟩
  intro H A p old hHB hold w hw hdebitOld
  let d := min w v
  have hd : 0 < d := lt_min hw hv
  let S : Set (RetainedCoreHistory.{u}) := {K | K.horizon ≤ B ∧
    ∃ (A' : InitialIdentification P g K.toHistory), A.IsPrefixOf A' ∧
    (HistoryEventControl H → HistoryEventControl K) ∧
    ∃ (q : CutoffParameters)
      (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
      (hc : H.eventCount ≤ K.eventCount),
      (∀ t : ℝ, t ≤ H.horizon → q.delta t = p.delta t ∧
        q.neckRadius t = p.neckRadius t ∧ q.protectedRadius t = p.protectedRadius t) ∧
      K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
      (∀ i : Fin H.eventCount,
        HEq (records (Fin.castLE hc i)).nominalRadius (old i).nominalRadius ∧
        HEq (records (Fin.castLE hc i)).delta (old i).delta ∧
        HEq (records (Fin.castLE hc i)).order (old i).order ∧
        HEq (records (Fin.castLE hc i)).neck (old i).neck ∧
        HEq (records (Fin.castLE hc i)).static (old i).static) ∧
      ∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * d) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F}
  have hH : H ∈ S := by
    refine ⟨hHB, A, InitialIdentification.IsPrefixOf.refl A, fun h => h,
      p, old, le_rfl, (fun _ _ => ⟨rfl, rfl, rfl⟩), hold, ?_, ?_⟩
    · exact fun i => ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    · intro i
      obtain ⟨F, hF, hvol⟩ := hdebitOld i
      refine ⟨F, hF, (add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal ?_)).trans hvol⟩
      exact mul_le_mul_of_nonneg_left (min_le_left w v) (Nat.cast_nonneg _)
  have hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory := by
    rintro K ⟨_, A', hA', _⟩
    exact hA'.1
  let budget : ℝ := Nat.card (ConnectedComponents (H.stage 0).Carrier) +
    2 * (Real.exp ((3 / a) * B) *
      (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
        (H.initialMetric 0) univ).toReal / d)
  have hcount : ∀ K ∈ S, K.eventCount ≤ ⌈budget⌉₊ := by
    intro K hK
    obtain ⟨hKB, A', hA', _, q, records, _, _, _, _, hdebit⟩ := hK
    obtain ⟨hfixedK, hlowerK⟩ := A'.fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hlower
    have hb := K.toHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
      records ha hfixedK hlowerK hd hKB hdebit
    rw [observation_initial_budget_eq hA'.1 d (3 / a) B] at hb
    exact_mod_cast hb.trans (Nat.le_ceil budget)
  have hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s), s ≤ B →
        G.flow.base.metric (K.time (Fin.last K.eventCount)) =
          K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
            (K.time (Fin.last K.eventCount)) s)
          (hi : E.incoming.flow.base.metric (K.time (Fin.last K.eventCount)) =
            K.initialMetric (Fin.last K.eventCount)),
          E.incoming = G ∧ K.appendEvent E.incoming.lt E hi ∈ S := by
    intro K hK hKB s G hs hG hsing
    obtain ⟨_, A', hA', hcontrol, q, records, hc, hparameters, hclass, hOld, hdebit⟩ := hK
    obtain ⟨Q, E, hi, A'', q', _, records', hEG, _, hAA', _, _, _, _, hclass',
      hOld', _, _, _, _, _, hbfr, hdiscard, hdebitE⟩ :=
      step K A' q records hKB hclass s G hs hG hsing
    have hcontrolE : SurgeryEventControl E := ⟨hEG.symm ▸ hsing, hbfr, hdiscard⟩
    refine ⟨Q, E, hi, hEG, hs, A'', hA'.trans hAA',
      (fun hH => history_control_append K (hcontrol hH) E hi hcontrolE),
      q.spliceAfter q' K.horizon,
      records', hc.trans (Nat.le_succ _), ?_, hclass', ?_, ?_⟩
    · intro t ht
      have hsplice := q.spliceAfter_eval_of_le q' (ht.trans hA'.1.horizon_le)
      have hparam := hparameters t ht
      exact ⟨hsplice.1.trans hparam.1, hsplice.2.1.trans hparam.2.1,
        hsplice.2.2.trans hparam.2.2⟩
    · intro i
      have h₁ := hOld' (Fin.castLE hc i)
      have h₂ := hOld i
      exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
        h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩
    · apply K.appendEvent_compact_volume_debit E.incoming.lt E hi d hdebit
      obtain ⟨F, hF, hvol⟩ := hdebitE
      refine ⟨F, hF, (add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal ?_)).trans hvol⟩
      exact mul_le_mul_of_nonneg_left (min_le_right w v) (Nat.cast_nonneg _)
  obtain ⟨J, hJ, heq | hclosed⟩ :=
    H.exists_closedSlab_extension_of_eventCount_bounded S hH hprefix
      (fun K hK => hK.1) hcount hproduce
  · obtain ⟨_, A', hA', hcontrol, q, records, hc, hparameters, hclass, hOld, hdebit⟩ := hJ
    exact ⟨J, A', q, records, hc, heq, hA', hcontrol, hparameters, hclass, hOld, hdebit⟩
  · obtain ⟨hJB, G, hG, _⟩ := hclosed
    obtain ⟨_, A', hA', hcontrol, q, records, hc, hparameters, hclass, hOld, hdebit⟩ := hJ
    obtain ⟨A'', hAA'⟩ := marked_closed_extension J A' hJB G hG
    refine ⟨J.extendHorizon B hJB G hG, A'', q,
      fun i => GeometricCutoffRecord.extendHorizon B hJB G hG (records i),
      hc, rfl, hA'.trans hAA',
      (fun hH => history_control_extend J (hcontrol hH) hJB G hG),
      hparameters, ?_, hOld, hdebit⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hclass
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Extend the actual observation within one finite-horizon canonical class, retaining its records. -/
theorem exists_geometric_observation_extension
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ w : ℝ, 0 < w →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                  (H.coreEvent i).outputMetric univ +
                ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * w) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
          ∃ (K : RetainedCoreHistory.{u})
            (A' : InitialIdentification P g K.toHistory) (q : CutoffParameters)
            (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i q)
            (hc : H.eventCount ≤ K.eventCount),
            K.horizon = B ∧ A.IsPrefixOf A' ∧
            K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records (Fin.castLE hc i)).nominalRadius (old i).nominalRadius ∧
              HEq (records (Fin.castLE hc i)).delta (old i).delta ∧
              HEq (records (Fin.castLE hc i)).order (old i).order ∧
              HEq (records (Fin.castLE hc i)).neck (old i).neck ∧
              HEq (records (Fin.castLE hc i)).static (old i).static) ∧
            ∀ i : Fin K.eventCount,
              ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
                riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                    (K.coreEvent i).outputMetric univ +
                  ENNReal.ofReal
                    ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * min w v) ≤
                riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
                  (K.coreEvent i).terminal.metric F := by
  obtain ⟨p₀, δbound, ρbound, v, hδ, hρ, hv, extend⟩ :=
    exists_geometric_observation_extension_preserving_control P g B hB
  refine ⟨p₀, δbound, ρbound, v, hδ, hρ, hv, ?_⟩
  intro H A p old hHB hold w hw hdebitOld
  obtain ⟨K, A', q, records, hc, hKB, hA, _, _, hclass, hOld, hdebit⟩ :=
    extend H A p old hHB hold w hw hdebitOld
  exact ⟨K, A', q, records, hc, hKB, hA, hclass, hOld, hdebit⟩

end GC.GeneralFlow

end
