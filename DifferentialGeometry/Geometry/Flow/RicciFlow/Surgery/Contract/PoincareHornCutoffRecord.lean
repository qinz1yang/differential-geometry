import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PreparedHistoryCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentClassification

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
private theorem incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq
    {P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld)) :
    HEq (H.toHistory.event i).incoming E.incoming ∧
      HEq (H.toHistory.event i).terminal E.terminal ∧
      ((H.toHistory.event i).poincareStandardDiscarded ↔ E.poincareStandardDiscarded) ∧
      ((H.toHistory.event i).transition.boundaryFrameReversing ↔ E.transition.boundaryFrameReversing) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have heq := eq_of_heq hE
  change HEq (H.coreEvent i).incoming E.incoming ∧
    HEq (H.coreEvent i).terminal E.terminal ∧
    ((H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded ↔ E.poincareStandardDiscarded) ∧
    ((H.coreEvent i).transition.boundaryFrameReversing ↔ E.transition.boundaryFrameReversing)
  rw [heq]
  exact ⟨HEq.rfl, HEq.rfl, Iff.rfl, Iff.rfl⟩


theorem exists_neckRadius_horn_cutoff_history_extension_with_poincareStandardDiscarded :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
      4 ≤ recenterConstant ∧
    ∀ Dcap : ℝ, 0 < Dcap → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∃ δ ε₀ C Λ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧ 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ (D : OneStepIncoming.{u}),
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
      H.stage (Fin.last H.eventCount) = D.stage →
      H.time (Fin.last H.eventCount) = D.startTime →
      HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      ∃ (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε₀ Λ) (Q : ℝ)
        (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        Q = max (max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹)
          (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) + 1 ∧
        max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹ < Q ∧
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => ρ D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        ((∀ j, Nonempty (IncomingBackwardNeck K.toHistory i
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).lowerOrder (horder j)) (Real.sqrt Q⁻¹))) →
          ∃ G : GeometricCutoffRecord K.toHistory i parameters,
            G.delta = (fun _ => δ) ∧
            G.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
            HEq G.neck Nrecord ∧ (∀ j, (G.neck j).scale = Q) ∧
              E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, hfactory⟩ :=
    exists_uniform_horn_cutoff_history_extension_at_scale_with_record_neck_precision_bound.{u}
  obtain ⟨eta, heta, htopology⟩ :=
    GeometricCutoffRecord.exists_poincareStandardDiscarded_cutting_scale_of_incoming.{u}
  obtain ⟨C, hC, hthreshold⟩ := htopology eta heta le_rfl
  refine ⟨fixed, c, hc, ?_⟩
  intro Dcap hDcap m accuracy haccuracy
  obtain ⟨δ, ε₀, hδ, hδ1, hδη, hε₀, hmake⟩ :=
    hfactory Dcap hDcap m accuracy haccuracy eta heta
  obtain ⟨Cp, Λ, hCp, hΛ, hpresentation⟩ :=
    OneStepIncoming.exists_neckRadius_terminalCorePresentation_with_scale_bound hε₀
  refine ⟨δ, ε₀, C, Λ, hδ, hδ1, hε₀, hC, hΛ, ?_⟩
  intro D P₀ g₀ H initial htime hstage hstart hinit
  obtain ⟨R, _, hclass⟩ := hthreshold D.stage D.startTime D.endTime D.slab D.terminal
  obtain ⟨q, _, hpresent⟩ := hpresentation D
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotectρ, P, _, hRP, _, _⟩ :=
    hpresent (max q (Cp * R)) (le_max_left _ _)
  have hprotected : R < (P.coreRadius ^ 2)⁻¹ := by
    have hh : Cp * R < Cp * (P.coreRadius ^ 2)⁻¹ := (le_max_right _ _).trans_lt hRP
    exact (mul_lt_mul_iff_right₀ (zero_lt_one.trans_le hCp)).mp hh
  let Q := max (max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹)
    (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) + 1
  have hQscale : max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹ < Q := by
    dsimp [Q]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hQnominal : (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) < Q := by
    dsimp [Q]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hA : 0 ≤ (P.coreRadius ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hQhorn : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hA).trans_lt hQscale
  have hQtop : C ^ 2 * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hA).trans_lt hQscale
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hS, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpD, hpAcc, hprotect, hmeets, hNscale, hNrecord, hTube, hrecord, hvol, hcap⟩ :=
    hmake H initial htime (D.withNeckRadius ρ hρ) hstage hstart hinit P le_rfl Q hQhorn hQnominal
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotectρ, P, Q,
    Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    rfl, hQscale, hQ, hS, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpD, hpAcc, hprotect, hmeets, hNscale, hNrecord, hTube, ?_, hvol, hcap⟩
  intro hback
  have hbackRecord : ∀ j, Nonempty (IncomingBackwardNeck K.toHistory i (Nrecord j) (Real.sqrt Q⁻¹)) := by
    intro j
    obtain ⟨B⟩ := hback (eOriginal.symm j)
    have he := hNrecord (eOriginal.symm j)
    rw [eOriginal.apply_symm_apply] at he
    rw [he]
    change Nonempty (IncomingBackwardNeck K.toHistory i
      (((((NOriginal (eOriginal.symm j)).monoDelta (hδOriginal (eOriginal.symm j)) hδ1').lowerOrder
        (horder (eOriginal.symm j))).rotatedDatum (rotation (eOriginal.symm j))
        (hmark (eOriginal.symm j)) (side (eOriginal.symm j))).oriented.toNormalizedNeck) _)
    exact ⟨IncomingBackwardNeck.oriented _ (B.rotatedDatum
      (rotation (eOriginal.symm j)) (hmark (eOriginal.symm j)) (side (eOriginal.symm j)))⟩
  obtain ⟨G, hGdelta, hGorder, hGneck, hGscale⟩ := hrecord hbackRecord
  obtain ⟨hKincoming, hKterminal, hKstd, hKboundary⟩ :=
    incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq E
      hsrc hout hsrcTime houtTime hOld hEvent
  have hcomplete := (K.toHistory.event i).transition.toSmoothCutCapCompletion
    (hKboundary.mpr hBoundary)
  have hstd := hclass K.toHistory i hsrc hsrcTime houtTime
    (hKincoming.trans (heq_of_eq hS)) (hKterminal.trans hL)
    parameters G
    (by intro j; rw [hGdelta]; exact hδη)
    (by rw [hpR]; exact hprotected)
    (by intro j; rw [hpR, hGscale]; exact hQtop) hcomplete
  exact ⟨G, hGdelta, hGorder, hGneck, hGscale, hKstd.mp hstd, hstd⟩

private theorem RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq
    {Q : OrientedThreeStage.{u}} (H K : RetainedCoreHistory.{u}) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hK : K = H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit)
    (i : Fin K.eventCount) (hi : i.val = H.eventCount)
    {p₀ q : CutoffParameters} {δ₀ ρ₀ : ℝ}
    (hH : H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀)
    (new : GeometricCutoffRecord K.toHistory i q)
    (hfixed : q.fixed = p₀.fixed) (hradius : q.modelRadius = p₀.modelRadius)
    (horder : q.modelOrder = p₀.modelOrder) (haccuracy : q.modelAccuracy = p₀.modelAccuracy)
    (hrecenter : q.recenterConstant = p₀.recenterConstant)
    (hnew : ∀ b, (new.static b).hasCanonicalWindow)
    (hδnew : q.delta s ≤ δ₀) (hρnew : q.neckRadius s ≤ ρ₀) :
    K.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ := by
  subst K
  have hi' : i = Fin.last H.eventCount := Fin.ext hi
  subst i
  exact H.hasCanonicalCutoffRecords_appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld)
    hinit hH new hfixed hradius horder haccuracy hrecenter hnew hδnew hρnew

theorem exists_neckRadius_horn_cutoff_history_extension_with_canonical_windows_and_poincareStandardDiscarded :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
      4 ≤ recenterConstant ∧
    ∀ Dcap : ℝ, 0 < Dcap → transitionEnd < Dcap + 1 → ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∀ η ρ₀ : ℝ, 0 < η → 0 < ρ₀ →
    ∃ δ ε₀ C Λ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧ 0 < ε₀ ∧ 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ (D : OneStepIncoming.{u}), D.parameters.neckRadius D.endTime ≤ ρ₀ →
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
      H.stage (Fin.last H.eventCount) = D.stage →
      H.time (Fin.last H.eventCount) = D.startTime →
      HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) →
      ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
        (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
        (Antitone D.parameters.neckRadius → Antitone ρ) ∧
        (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
        (HasRecenterConstants.{u} D.parameters →
          HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
        D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      ∃ (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) ε₀ Λ) (Q : ℝ)
        (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        Q = max (max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹)
          (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) + 1 ∧
        max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹ < Q ∧
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => ρ D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        ((∀ j, Nonempty (IncomingBackwardNeck K.toHistory i
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).lowerOrder (horder j)) (Real.sqrt Q⁻¹))) →
          ∃ G : GeometricCutoffRecord K.toHistory i parameters,
            G.delta = (fun _ => δ) ∧
            G.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
            HEq G.neck Nrecord ∧ (∀ j, (G.neck j).scale = Q) ∧
              E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
              (∀ b, (G.static b).hasCanonicalWindow) ∧
              ∀ p₀ : CutoffParameters,
                p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
                p₀.modelOrder = m → p₀.modelRadius = Dcap → p₀.modelAccuracy = accuracy →
                H.hasCanonicalCutoffRecords p₀ η ρ₀ → K.hasCanonicalCutoffRecords p₀ η ρ₀) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, hfactory⟩ :=
    exists_uniform_horn_cutoff_history_extension_at_scale_with_record_windows_precision_bound.{u}
  obtain ⟨eta, heta, htopology⟩ :=
    GeometricCutoffRecord.exists_poincareStandardDiscarded_cutting_scale_of_incoming.{u}
  obtain ⟨C, hC, hthreshold⟩ := htopology eta heta le_rfl
  refine ⟨fixed, c, hc, ?_⟩
  intro Dcap hDcap hDfit m accuracy haccuracy η ρ₀ hη hρ₀
  obtain ⟨δ, ε₀, hδ, hδ1, hδη, hε₀, hmake⟩ :=
    hfactory Dcap hDcap hDfit m accuracy haccuracy (min eta η) (lt_min heta hη)
  obtain ⟨Cp, Λ, hCp, hΛ, hpresentation⟩ :=
    OneStepIncoming.exists_neckRadius_terminalCorePresentation_with_scale_bound hε₀
  refine ⟨δ, ε₀, C, Λ, hδ, hδ1, hδη.trans (min_le_right _ _), hε₀, hC, hΛ, ?_⟩
  intro D hρseed P₀ g₀ H initial htime hstage hstart hinit
  obtain ⟨R, _, hclass⟩ := hthreshold D.stage D.startTime D.endTime D.slab D.terminal
  obtain ⟨q, _, hpresent⟩ := hpresentation D
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotectρ, P, _, hRP, _, _⟩ :=
    hpresent (max q (Cp * R)) (le_max_left _ _)
  have hprotected : R < (P.coreRadius ^ 2)⁻¹ := by
    have hh : Cp * R < Cp * (P.coreRadius ^ 2)⁻¹ := (le_max_right _ _).trans_lt hRP
    exact (mul_lt_mul_iff_right₀ (zero_lt_one.trans_le hCp)).mp hh
  let Q := max (max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹)
    (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) + 1
  have hQscale : max (2 * Λ) (C ^ 2) * (P.coreRadius ^ 2)⁻¹ < Q := by
    dsimp [Q]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hQnominal : (((δ ^ 2 * ρ D.endTime) ^ 2)⁻¹) < Q := by
    dsimp [Q]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hA : 0 ≤ (P.coreRadius ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hQhorn : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hA).trans_lt hQscale
  have hQtop : C ^ 2 * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hA).trans_lt hQscale
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQ, hS, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpD, hpAcc, hprotect, hmeets, hNscale, hNrecord, hTube, hrecord, hvol, hcap⟩ :=
    hmake H initial htime (D.withNeckRadius ρ hρ) hstage hstart hinit P le_rfl Q hQhorn hQnominal
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotectρ, P, Q,
    Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    rfl, hQscale, hQ, hS, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpD, hpAcc, hprotect, hmeets, hNscale, hNrecord, hTube, ?_, hvol, hcap⟩
  intro hback
  have hbackRecord : ∀ j, Nonempty (IncomingBackwardNeck K.toHistory i (Nrecord j) (Real.sqrt Q⁻¹)) := by
    intro j
    obtain ⟨B⟩ := hback (eOriginal.symm j)
    have he := hNrecord (eOriginal.symm j)
    rw [eOriginal.apply_symm_apply] at he
    rw [he]
    change Nonempty (IncomingBackwardNeck K.toHistory i
      (((((NOriginal (eOriginal.symm j)).monoDelta (hδOriginal (eOriginal.symm j)) hδ1').lowerOrder
        (horder (eOriginal.symm j))).rotatedDatum (rotation (eOriginal.symm j))
        (hmark (eOriginal.symm j)) (side (eOriginal.symm j))).oriented.toNormalizedNeck) _)
    exact ⟨IncomingBackwardNeck.oriented _ (B.rotatedDatum
      (rotation (eOriginal.symm j)) (hmark (eOriginal.symm j)) (side (eOriginal.symm j)))⟩
  obtain ⟨G, hGdelta, hGorder, hGneck, hGscale, hcanonical⟩ := hrecord hbackRecord
  obtain ⟨hKincoming, hKterminal, hKstd, hKboundary⟩ :=
    incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq E
      hsrc hout hsrcTime houtTime hOld hEvent
  have hcomplete := (K.toHistory.event i).transition.toSmoothCutCapCompletion
    (hKboundary.mpr hBoundary)
  have hstd := hclass K.toHistory i hsrc hsrcTime houtTime
    (hKincoming.trans (heq_of_eq hS)) (hKterminal.trans hL)
    parameters G
    (by intro j; rw [hGdelta]; exact hδη.trans (min_le_left _ _))
    (by rw [hpR]; exact hprotected)
    (by intro j; rw [hpR, hGscale]; exact hQtop) hcomplete
  refine ⟨G, hGdelta, hGorder, hGneck, hGscale, hKstd.mp hstd, hstd, hcanonical, ?_⟩
  intro p₀ hpf hpc hpm hpD₀ hpε hInv
  obtain ⟨Eappend, hOldAppend, hInitial, _, hK⟩ := happend
  apply H.hasCanonicalCutoffRecords_of_appendEvent_eq K Eappend hOldAppend hInitial hK i hi
    hInv G (hpFixed.trans hpf.symm) (hpD.trans hpD₀.symm)
      (hpM.trans hpm.symm) (hpAcc.trans hpε.symm) (hpC.trans hpc.symm) hcanonical
  · rw [hpδ]
    exact hδη.trans (min_le_right _ _)
  · rw [hpρ]
    exact (hρle D.endTime (D.startTime_nonneg.trans D.startTime_lt_endTime.le)).trans hρseed


open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


private theorem cap_neck_chart_mono_tolerances
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps eps' C1 C2 : ℝ} {x : M} {t : ℝ}
    {W : CanonicalWitness S eps C1 C2 x t} (hW : W.capTubeHasNeckChart eps)
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    (W.monoEps heps hsmall).capTubeHasNeckChart eps' := by
  intro cap depth htag
  obtain ⟨v, nk, hmap⟩ := hW.mono_eps heps hsmall cap depth htag
  exact ⟨v, nk.mono heps hsmall, hmap⟩

private theorem canonical_neighborhoods_of_incoming_heq
    {P Q : OrientedThreeStage.{u}} {a b s t : ℝ}
    {G : P.IncomingSlab a s} {F : Q.IncomingSlab b t}
    (hP : P = Q) (ha : a = b) (hs : s = t) (hG : HEq G F)
    {eps C1 C2 q : ℝ}
    (hcanonical : ∀ x : Q.Carrier, ∀ v ∈ Ioo b t, q < F.flow.scalar v x →
      ∃ W : CanonicalWitness F.flow eps C1 C2 x v, W.capTubeHasNeckChart eps) :
    ∀ x : P.Carrier, ∀ v ∈ Ioo a s, q < G.flow.scalar v x →
      ∃ W : CanonicalWitness G.flow eps C1 C2 x v, W.capTubeHasNeckChart eps := by
  cases hP
  cases ha
  cases hs
  cases eq_of_heq hG
  exact hcanonical

private theorem derivative_bound_of_incoming_heq
    {P Q : OrientedThreeStage.{u}} {a b s t : ℝ}
    {G : P.IncomingSlab a s} {F : Q.IncomingSlab b t}
    (hP : P = Q) (ha : a = b) (hs : s = t) (hG : HEq G F) {Ctime : ℝ≥0} {q : ℝ}
    (hbound : ∀ x : Q.Carrier, ∀ v ∈ Ioo b t, q < F.flow.scalar v x →
      |derivWithin (fun w => F.flow.scalar w x) (Iic v) v| ≤ Ctime * F.flow.scalar v x ^ 2) :
    ∀ x : P.Carrier, ∀ v ∈ Ioo a s, q < G.flow.scalar v x →
      |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2 := by
  cases hP
  cases ha
  cases hs
  cases eq_of_heq hG
  exact hbound

theorem MetricCutCapEvent.exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ {P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
        {a s : ℝ} (E : MetricCutCapEvent P Q a s),
        H.stage i.castSucc = P → H.stage i.succ = Q → H.time i.castSucc = a → H.time i.succ = s →
      ∀ hOld : E.old = E.transition.trace.retainedCore,
        HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld) → E.transition.boundaryFrameReversing →
      ∀ (parameters : CutoffParameters) (Record : GeometricCutoffRecord H.toHistory i parameters)
        (C q0 q : ℝ) (Ctime : ℝ≥0), 0 ≤ C → 0 < q0 →
        q < ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ →
        (∀ j, C * ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ < (Record.neck j).scale) →
        (∀ j, Record.delta j ≤ eps) →
        (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q0 < E.incoming.flow.scalar t x →
          |derivWithin (fun v => E.incoming.flow.scalar v x) (Iic t) t| ≤
            Ctime * E.incoming.flow.scalar t x ^ 2) →
        (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < E.incoming.flow.scalar t x →
          ¬ Nonempty (SpatialNeck (E.incoming.flow.base.metric t) eps x) →
          ∃ U : Set P.Carrier,
            (∀ y ∈ U, ∀ z ∈ U, E.incoming.flow.scalar t y ≤ C * E.incoming.flow.scalar t z) ∧
            (U = connectedComponent x ∨
              ∃ V : Set P.Carrier, Nonempty (CapCore V) ∧ V ⊆ U ∧
                riemannianBallOf (E.incoming.flow.base.metric t) x
                  (1000 / Real.sqrt (metricScalarAt (E.incoming.flow.base.metric t) x)) ⊆ interior V)) →
        (∀ (c : ConnectedComponents P.Carrier) (t : ℝ), t ∈ Ioo a s →
          ∀ x : (P.toClosedOrientedManifold.component c).Carrier, q < E.incoming.flow.scalar t x.val →
          ¬ Nonempty (SpatialNeck ((E.incoming.flow.base.metric t).restrictOpen (P.componentOpen c)) eps x) →
          Nonempty (PositiveComponent (M := (P.toClosedOrientedManifold.component c).Carrier) univ) ∨
          admitsConstantPositiveSectionalCurvature (I := ThreeModel)
            (M := (P.toClosedOrientedManifold.component c).Carrier) ∨
          ∃ (K : CompactDomain (P.toClosedOrientedManifold.component c).Carrier)
            (v : (P.toClosedOrientedManifold.component c).Carrier)
            (nk : SpatialNeck ((E.incoming.flow.base.metric t).restrictOpen (P.componentOpen c)) eps v)
            (level : ℝ),
            0 < metricScalarAt ((E.incoming.flow.base.metric t).restrictOpen (P.componentOpen c)) x ∧
            Nonempty (CapCore K.carrier) ∧ |level| ≤ 4 ∧
            frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, level)) ∧
            riemannianBallOf ((E.incoming.flow.base.metric t).restrictOpen (P.componentOpen c)) x
              (1000 / Real.sqrt (metricScalarAt
                ((E.incoming.flow.base.metric t).restrictOpen (P.componentOpen c)) x)) ⊆ interior K.carrier) →
        E.poincareStandardDiscarded ∧ (H.toHistory.event i).poincareStandardDiscarded := by
  obtain ⟨eta, heta, hclass⟩ :=
    GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P Q H i a s E hsrc hout hstart hend hOld hEvent hBoundary
    parameters Record C q0 q Ctime hC hq0 hprotected hscale hdelta hbound hspatial hcomponents
  cases hsrc
  cases hout
  cases hstart
  cases hend
  obtain ⟨hKincoming, _, hKstd, hKboundary⟩ :=
    incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq E
      rfl rfl rfl rfl hOld hEvent
  have hG : (H.coreEvent i).toMetricCutCapEvent.incoming = E.incoming := eq_of_heq hKincoming
  have hstd := hclass eps heps H.toHistory i parameters Record hdelta C q0 q Ctime hC hq0
    hprotected hscale
    (by rw [← hG] at hbound; exact hbound)
    (by rw [← hG] at hspatial; exact hspatial)
    (by rw [← hG] at hcomponents; exact hcomponents)
    ((H.toHistory.event i).transition.toSmoothCutCapCompletion (hKboundary.mpr hBoundary))
  exact ⟨hKstd.mp hstd, hstd⟩

private theorem exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ {P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
        {a s : ℝ} (E : MetricCutCapEvent P Q a s),
        H.stage i.castSucc = P → H.stage i.succ = Q → H.time i.castSucc = a → H.time i.succ = s →
      ∀ hOld : E.old = E.transition.trace.retainedCore,
        HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld) → E.transition.boundaryFrameReversing →
      ∀ (parameters : CutoffParameters) (Record : GeometricCutoffRecord H.toHistory i parameters)
        (C1 C2 q A Qscale : ℝ), 1 ≤ C2 → 0 < q → q < A → C2 ^ 2 * A < Qscale →
        ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ = A →
        (∀ j, Record.delta j ≤ eps) → (∀ j, (Record.neck j).scale = Qscale) →
        (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < E.incoming.flow.scalar t x →
          ∃ W : CanonicalWitness E.incoming.flow eps C1 C2 x t, W.capTubeHasNeckChart eps) →
        ∀ Ctime : ℝ≥0, (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < E.incoming.flow.scalar t x →
          |derivWithin (fun v => E.incoming.flow.scalar v x) (Iic t) t| ≤
            Ctime * E.incoming.flow.scalar t x ^ 2) →
        E.poincareStandardDiscarded ∧ (H.toHistory.event i).poincareStandardDiscarded := by
  obtain ⟨eta, heta, hclass⟩ :=
    GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P Q H i a s E hsrc hout hstart hend hOld hEvent hBoundary
    parameters Record C1 C2 q A Qscale hC2 hq hqA hscale hA hdelta hneck hcanonical Ctime hderiv
  obtain ⟨hKincoming, _, hKstd, hKboundary⟩ :=
    incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq E
      hsrc hout hstart hend hOld hEvent
  have hcanonicalK := canonical_neighborhoods_of_incoming_heq hsrc hstart hend hKincoming hcanonical
  have hderivK := derivative_bound_of_incoming_heq hsrc hstart hend hKincoming hderiv
  have hstd := hclass eps heps H.toHistory i parameters Record hdelta C1 C2 q hC2 hq
    (hA.symm ▸ hqA) (fun j => by rw [hA, hneck]; exact hscale) hcanonicalK Ctime hderivK
    ((H.toHistory.event i).transition.toSmoothCutCapCompletion (hKboundary.mpr hBoundary))
  exact ⟨hKstd.mp hstd, hstd⟩

theorem exists_horn_cutoff_with_volume_decrease_and_standard_discard_of_canonical_neighborhoods
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∃ εcan : ℝ, 0 < εcan ∧ εcan < 1 / 11 ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ q0 qcan originalCoreFloor protectedFloor : ℝ,
      0 < q0 → 0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Λq * max q0 1 ≤ Q ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    (∀ y, ∀ t ∈ Ioo D.startTime D.endTime, qcan < D.slab.flow.scalar t y →
      |derivWithin (fun v => D.slab.flow.scalar v y) (Iic t) t| ≤
        Ctime * D.slab.flow.scalar t y ^ 2) →
    (∀ x t, t ∈ Ioo D.startTime D.endTime → qcan < D.slab.flow.scalar t x →
      ∃ W : CanonicalWitness D.slab.flow εcan C1 C2 x t, W.capTubeHasNeckChart εcan) →
    ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
      (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
      (Antitone D.parameters.neckRadius → Antitone ρ) ∧
      (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
      (HasRecenterConstants.{u} D.parameters →
        HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
      D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      let D' := D.withNeckRadius ρ hρ
      ∃ P : TerminalCorePresentation D' ε₀ Λ,
        P.coreRadius = D.parameters.delta D.endTime * ρ D.endTime ∧
        qcan < (P.coreRadius ^ 2)⁻¹ ∧
        (P.coreRadius ^ 2)⁻¹ ≤
          max (max ((D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime)^2)⁻¹
            ((D.parameters.protectedRadius D.endTime)^2)⁻¹) (4 * (max (C * qcan) 0 + 1) / C) ∧
        (∀ x : D.slab.terminalRegularOpen,
          metricScalarAt D.terminal.metric x ≤ ((D.parameters.protectedRadius D.endTime)^2)⁻¹ →
            ∃ c ∈ P.component, x ∈ interior (P.core c)) ∧
        (∀ c e, ∃ (p : D.slab.terminalRegularOpen)
          (N : SpatialNeck D.terminal.metric (1 / 156000) p) (level : ℝ),
          |level| ≤ 3 ∧ metricScalarAt D.terminal.metric p ≤ 2 * Λ * (P.coreRadius ^ 2)⁻¹ ∧
          ∀ y, P.horn c e (y, 0) = N.map (y, level)) ∧
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D'.stage Qout D'.startTime D'.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D'.slab ∧ HEq E.terminal D'.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D'.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D'.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D'.stage ∧ K.time i.castSucc = D'.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D'.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D'.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D'.parameters.neckRadius D'.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D'.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * ε₀ ∧ ⌊ε₀⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasCanonicalWindow) ∧
          E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
          (p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
            p₀.modelOrder = m → p₀.modelAccuracy = accuracy → ηrecord ≤ δold →
            D.parameters.neckRadius D.endTime ≤ ρold →
              K.hasCanonicalCutoffRecords p₀ δold ρold)) ∧
        (∃ Kvol : Set D'.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D'.slab.terminalRegularOpen D'.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, hfactory⟩ :=
    exists_horn_cutoff_with_uniform_volume_decrease_above_scale_of_core_radius_lower_bound
      P₀ g₀
  obtain ⟨eta, heta, htopology⟩ :=
    exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance.{u}
  let epsTop := min eta (1 / 22)
  have hTop : 0 < epsTop := lt_min heta (by norm_num)
  have hTopSmall : epsTop < 1 / 11 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨fixed, c, hc, ?_⟩
  intro Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  obtain ⟨εold, δold, hεold, hδold, hfactory⟩ :=
    hfactory Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  refine ⟨εold, δold, hεold, hδold, ?_⟩
  intro m accuracy haccuracy ηrecord hηrecord
  obtain ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, hmake⟩ :=
    hfactory m accuracy haccuracy (min ηrecord epsTop) (lt_min hηrecord hTop)
  have hδrecord : δ ≤ ηrecord := hδη.trans (min_le_left _ _)
  have hδTop : δ ≤ epsTop := hδη.trans (min_le_right _ _)
  refine ⟨δ, ε₀, Λq, hδ, hδ1, hδrecord, hε₀, hΛq, ?_⟩
  obtain ⟨epsGeometry, hGeom, hGeomSmall, hgeometry⟩ :=
    OneStepIncoming.exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_canonical_neighborhoods.{u} hε₀
  let epsCan := min epsGeometry epsTop
  refine ⟨epsCan, lt_min hGeom hTop, (min_le_left _ _).trans_lt hGeomSmall, ?_⟩
  intro C1 C2 hC2
  obtain ⟨C, Λ, hC, hΛ, hgeometry⟩ := hgeometry C1 C2 hC2
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro q0 qcan originalCoreFloor protectedFloor hq0 hqcan hcoreFloor hprotectedFloor
  obtain ⟨radiusFloor, hradiusFloor, hgeometry⟩ :=
    hgeometry (C * qcan) originalCoreFloor protectedFloor
      (mul_pos (zero_lt_one.trans_le hC) hqcan) hcoreFloor hprotectedFloor
  obtain ⟨Q, v, hQ, hv, hQmin, hQtopFloor, hvQ, hmake⟩ :=
    hmake q0 hq0 Λ radiusFloor hΛ hradiusFloor (C2 ^ 2 * (radiusFloor ^ 2)⁻¹)
  refine ⟨Q, v, hQ, hv, hQmin, hvQ, ?_⟩
  intro p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing stepParameters hinit D
    hderiv hfinal hcore hprotected hderivCan hcanonical
  have hgeo : ∀ x t, t ∈ Ioo D.startTime D.endTime → C * qcan < D.slab.flow.scalar t x →
      ∃ W : CanonicalWitness D.slab.flow epsGeometry C1 C2 x t, W.capTubeHasNeckChart epsGeometry := by
    intro x t ht hx
    have hqle : qcan ≤ C * qcan := le_mul_of_one_le_left hqcan.le hC
    obtain ⟨W, hW⟩ := hcanonical x t ht (hqle.trans_lt hx)
    exact ⟨W.monoEps (min_le_left _ _) hGeomSmall,
      cap_neck_chart_mono_tolerances hW (min_le_left _ _) hGeomSmall⟩
  have htop : ∀ x t, t ∈ Ioo D.startTime D.endTime → qcan < D.slab.flow.scalar t x →
      ∃ W : CanonicalWitness D.slab.flow epsTop C1 C2 x t, W.capTubeHasNeckChart epsTop := by
    intro x t ht hx
    obtain ⟨W, hW⟩ := hcanonical x t ht hx
    exact ⟨W.monoEps (min_le_right _ _) hTopSmall,
      cap_neck_chart_mono_tolerances hW (min_le_right _ _) hTopSmall⟩
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hfloor, _, hscale, hupper, hlow, hbase⟩ := hgeometry D hcore hprotected hgeo
  have hqcore : qcan < (P.coreRadius ^ 2)⁻¹ :=
    (mul_lt_mul_iff_right₀ (zero_lt_one.trans_le hC)).mp hscale
  have hQtop : C2 ^ 2 * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_left
      (inv_anti₀ (sq_pos_of_pos hradiusFloor) ((sq_le_sq₀ hradiusFloor.le P.coreRadius_pos.le).mpr hfloor))
      (sq_nonneg C2)).trans_lt hQtopFloor
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hqcore, hupper, hlow, hbase, ?_⟩
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotectedNew, hretained, hNscale, hsource, hNrecord, hTube,
    hrecord, hvol, hcap⟩ :=
    hmake p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing
      (stepParameters.withNeckRadius ρ hρ) hinit hderiv hfinal P le_rfl le_rfl hfloor
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩ := hrecord
  have htopE : ∀ x t, t ∈ Ioo D.startTime D.endTime → qcan < E.incoming.flow.scalar t x →
      ∃ W : CanonicalWitness E.incoming.flow epsTop C1 C2 x t, W.capTubeHasNeckChart epsTop := by
    rw [hG]
    exact htop
  have hderivE : ∀ x, ∀ t ∈ Ioo D.startTime D.endTime, qcan < E.incoming.flow.scalar t x →
      |derivWithin (fun v => E.incoming.flow.scalar v x) (Iic t) t| ≤
        Ctime * E.incoming.flow.scalar t x ^ 2 := by
    rw [hG]
    exact hderivCan
  obtain ⟨hstdE, hstdK⟩ := htopology epsTop (min_le_left _ _) E
    hsrc hout hsrcTime houtTime hOld hEvent hBoundary parameters Record C1 C2 qcan
    (P.coreRadius ^ 2)⁻¹ Q hC2 hqcan hqcore hQtop
    (by rw [hpR]) (by intro j; rw [hRecordDelta]; exact hδTop) hRecordScale htopE Ctime hderivE
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotectedNew, hretained, hNscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows,
      hstdE, hstdK, ?_⟩, hvol, hcap⟩
  intro hfixed hrecenter hmodelOrder hmodelAccuracy hηold hρold
  obtain ⟨Eappend, hOldAppend, hInitial, _, hK⟩ := happend
  apply H.hasCanonicalCutoffRecords_of_appendEvent_eq K Eappend hOldAppend hInitial hK i hi
    hInv Record (hpFixed.trans hfixed.symm) (hpDnew.trans hpD.symm)
    (hpM.trans hmodelOrder.symm) (hpAcc.trans hmodelAccuracy.symm)
    (hpC.trans hrecenter.symm) hRecordWindows
  · rw [hpδ]
    exact hδrecord.trans hηold
  · rw [hpρ]
    exact (hρle D.endTime (D.startTime_nonneg.trans D.startTime_lt_endTime.le)).trans hρold


theorem exists_horn_cutoff_with_volume_decrease_and_standard_discard_of_spatial_neighborhoods
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0)
    (hmargin : Dtrace + 1 ≤ Dbig) (htol : 0 < tol) (htolsmall : tol ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + tol⁻¹ + 1 < r)
    (hfit : 64 * (r + tol⁻¹) < Dtrace) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εold δold epsSpatial : ℝ, 0 < εold ∧ 0 < δold ∧ 0 < epsSpatial ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∀ q0 : ℝ, 0 < q0 →
    ∃ δ ε₀ Qmin : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Qmin ∧
    ∀ Λmax coreFloor Cscalar : ℝ, 1 ≤ Λmax → 0 < coreFloor → 0 ≤ Cscalar → ∀ Qlower : ℝ,
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Qmin ≤ Q ∧ Qlower < Q ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount) →
    let D : OneStepIncoming := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := stepParameters }
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ ε₀ →
      Λ ≤ Λmax → coreFloor ≤ P.coreRadius →
      ∀ qcan : ℝ, qcan < (P.coreRadius ^ 2)⁻¹ →
        (∀ x : (H.stage (Fin.last H.eventCount)).Carrier, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, qcan < G.flow.scalar t x →
          ¬ Nonempty (SpatialNeck (G.flow.base.metric t) epsSpatial x) →
          ∃ U : Set (H.stage (Fin.last H.eventCount)).Carrier,
            (∀ y ∈ U, ∀ z ∈ U, G.flow.scalar t y ≤ Cscalar * G.flow.scalar t z) ∧
            (U = connectedComponent x ∨
              ∃ V : Set (H.stage (Fin.last H.eventCount)).Carrier, Nonempty (CapCore V) ∧ V ⊆ U ∧
                riemannianBallOf (G.flow.base.metric t) x
                  (1000 / Real.sqrt (metricScalarAt (G.flow.base.metric t) x)) ⊆ interior V)) →
        (∀ (c : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ), t ∈ Ioo (H.time (Fin.last H.eventCount)) s →
          ∀ x : ((H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.component c).Carrier, qcan < G.flow.scalar t x.val →
          ¬ Nonempty (SpatialNeck ((G.flow.base.metric t).restrictOpen ((H.stage (Fin.last H.eventCount)).componentOpen c)) epsSpatial x) →
          Nonempty (PositiveComponent (M := ((H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.component c).Carrier) univ) ∨
          admitsConstantPositiveSectionalCurvature (I := ThreeModel)
            (M := ((H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.component c).Carrier) ∨
          ∃ (K : CompactDomain ((H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.component c).Carrier)
            (v : ((H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.component c).Carrier)
            (nk : SpatialNeck ((G.flow.base.metric t).restrictOpen ((H.stage (Fin.last H.eventCount)).componentOpen c)) epsSpatial v)
            (level : ℝ),
            0 < metricScalarAt ((G.flow.base.metric t).restrictOpen ((H.stage (Fin.last H.eventCount)).componentOpen c)) x ∧
            Nonempty (CapCore K.carrier) ∧ |level| ≤ 4 ∧
            frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, level)) ∧
            riemannianBallOf ((G.flow.base.metric t).restrictOpen ((H.stage (Fin.last H.eventCount)).componentOpen c)) x
              (1000 / Real.sqrt (metricScalarAt
                ((G.flow.base.metric t).restrictOpen ((H.stage (Fin.last H.eventCount)).componentOpen c)) x)) ⊆ interior K.carrier) →
      ∃ (Qout : OrientedThreeStage.{u}) (E : MetricCutCapEvent D.stage Qout D.startTime D.endTime)
        (hOld : E.old = E.transition.trace.retainedCore)
        (K : RetainedCoreHistory.{u}) (initialK : InitialIdentification P₀ g₀ K.toHistory)
        (i : Fin K.eventCount) (parameters : CutoffParameters)
        (n : ℕ) (δOriginal : Fin n → ℝ) (kOriginal : Fin n → ℕ)
        (NOriginal : ∀ j, NormalizedNeck (K.toHistory.event i).terminal.metric
          (δOriginal j) (kOriginal j))
        (hδOriginal : ∀ j, δOriginal j ≤ δ)
        (rotation : Fin n → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
        (hmark : ∀ j, DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (rotation j)
          spherePoint = (NOriginal j).sphereMark)
        (side : Fin n → Bool)
        (horder : ∀ j, max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4) ≤ kOriginal j)
        (hδ1 : δ < 1)
        (Nrecord : (K.toHistory.event i).transition.trace.tubes.Index →
          NormalizedNeck (K.toHistory.event i).terminal.metric δ
            (max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)))
        (eOriginal : Fin n ≃ (K.toHistory.event i).transition.trace.tubes.Index),
        0 < Q ∧ E.incoming = D.slab ∧ HEq E.terminal D.terminal ∧
        E.transition.boundaryFrameReversing ∧
        initial.IsPrefixOf initialK ∧ K.horizon = D.endTime ∧ K.eventCount = H.eventCount + 1 ∧
        K.time (Fin.last K.eventCount) = D.endTime ∧ K.stage (Fin.last K.eventCount) = Qout ∧
        HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
        i.val = H.eventCount ∧ K.stage i.castSucc = D.stage ∧ K.time i.castSucc = D.startTime ∧
        K.stage i.succ = Qout ∧ K.time i.succ = D.endTime ∧
        HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
        (∃ (Eappend : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Qout
            (H.time (Fin.last H.eventCount)) D.endTime)
          (hOldAppend : Eappend.old = Eappend.transition.trace.retainedCore)
          (hInitial : Eappend.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount)),
          HEq Eappend E ∧ K = H.appendEvent Eappend.incoming.lt
            (Eappend.toRetainedCoreEvent hOldAppend) hInitial) ∧
        parameters.delta = (fun _ => δ) ∧ parameters.protectedRadius = (fun _ => P.coreRadius) ∧
        parameters.neckRadius = (fun _ => D.parameters.neckRadius D.endTime) ∧
        parameters.fixed = fixed ∧ parameters.recenterConstant = recenterConstant ∧
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧ parameters.modelAccuracy = accuracy ∧
        (∀ x : E.incoming.terminalRegularOpen,
          metricScalarAt E.terminal.metric x ≤ ((parameters.protectedRadius D.endTime) ^ 2)⁻¹ →
          x.val ∈ interior (Subtype.val '' E.old)) ∧
        (∀ c : ConnectedComponents E.transition.trace.tubes.core,
          (∃ x : E.transition.trace.tubes.core,
            ConnectedComponents.mk x = c ∧ x ∈ E.transition.trace.retainedCore) →
          ∃ x : E.incoming.terminalRegularOpen,
            ∃ hx : x.val ∈ E.transition.trace.tubes.core,
              ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt E.terminal.metric x ≤
                ((parameters.protectedRadius D.endTime) ^ 2)⁻¹) ∧
        (∀ j, (NOriginal j).scale = Q) ∧
        (∀ j, δOriginal j ≤ 2 * ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
        (∀ j, Nrecord (eOriginal j) =
          (((NOriginal j).monoDelta (hδOriginal j) hδ1).rotatedDatum
            (rotation j) (hmark j) (side j)).oriented.toNormalizedNeck.lowerOrder (horder j)) ∧
        (∀ j (z : TubeDomain) (hz : (z.1, z.2.val) ∈ neckBuffer δ),
          (K.toHistory.event i).transition.trace.tubes.tube j z =
            ((Nrecord j).chart ⟨(z.1, z.2.val), hz⟩).val) ∧
        (∃ Record : GeometricCutoffRecord K.toHistory i parameters,
          Record.delta = (fun _ => δ) ∧
          Record.order = (fun _ => max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)) ∧
          HEq Record.neck Nrecord ∧ (∀ j, (Record.neck j).scale = Q) ∧
          (∀ b, (Record.static b).hasCanonicalWindow)) ∧
        E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, hfactory⟩ :=
    exists_horn_cutoff_with_uniform_volume_decrease_above_scale_of_core_radius_lower_bound
      P₀ g₀
  obtain ⟨εold, δold, hεold, hδold, hfactory⟩ :=
    hfactory Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  obtain ⟨epsSpatial, hSpatial, htopology⟩ :=
    MetricCutCapEvent.exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods.{u}
  refine ⟨fixed, c, hc, εold, δold, epsSpatial, hεold, hδold, hSpatial, ?_⟩
  intro m accuracy haccuracy ηrecord hηrecord q0 hq0
  obtain ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, hmake⟩ :=
    hfactory m accuracy haccuracy (min ηrecord epsSpatial) (lt_min hηrecord hSpatial)
  have hQmin : 0 < Λq * max q0 1 :=
    mul_pos hΛq (zero_lt_one.trans_le (le_max_right _ _))
  have hmake := hmake q0 hq0
  refine ⟨δ, ε₀, Λq * max q0 1, hδ, hδ1, hδη.trans (min_le_left _ _), hε₀, hQmin, ?_⟩
  intro Λmax coreFloor Cscalar hΛmax hcoreFloor hCscalar Qlower
  obtain ⟨Q, v, hQ, hv, hQmin, hQlower, hvQ, hproduce⟩ :=
    hmake Λmax coreFloor hΛmax hcoreFloor (max Qlower (Cscalar * (coreFloor ^ 2)⁻¹))
  refine ⟨Q, v, hQ, hv, hQmin, (le_max_left _ _).trans_lt hQlower, hvQ, ?_⟩
  intro p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing stepParameters hinit D
    hderiv hfinal ε Λ P hε hΛ hcore qcan hqcan hspatial hcomponents
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotected, hretained, hNscale, hsource, hNrecord, hTube,
    hrecord, hvol, hcap⟩ :=
    hproduce p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing stepParameters hinit
      hderiv hfinal P hε hΛ hcore
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩ := hrecord
  have hcoreInv : (P.coreRadius ^ 2)⁻¹ ≤ (coreFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hcoreFloor) ((sq_le_sq₀ hcoreFloor.le P.coreRadius_pos.le).mpr hcore)
  have htopscale : Cscalar * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_left hcoreInv hCscalar).trans_lt
      ((le_max_right _ _).trans_lt hQlower)
  have hprotectedRecord : qcan < ((parameters.protectedRadius (K.time i.succ)) ^ 2)⁻¹ := by
    rw [hpR]
    exact hqcan
  have hscaleRecord (j : (K.toHistory.event i).transition.trace.tubes.Index) :
      Cscalar * ((parameters.protectedRadius (K.time i.succ)) ^ 2)⁻¹ < (Record.neck j).scale := by
    rw [hpR, hRecordScale]
    exact htopscale
  obtain ⟨hstdE, hstdK⟩ := htopology epsSpatial le_rfl E
    hsrc hout hsrcTime houtTime hOld hEvent hBoundary parameters Record Cscalar q0 qcan Ctime
    hCscalar hq0 hprotectedRecord hscaleRecord
    (by intro j; rw [hRecordDelta]; exact hδη.trans (min_le_right _ _))
    (by rw [hG]; exact hfinal)
    (by rw [hG]; exact hspatial)
    (by rw [hG]; exact hcomponents)
  exact ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotected, hretained, hNscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩,
    hstdE, hstdK, hvol, hcap⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
