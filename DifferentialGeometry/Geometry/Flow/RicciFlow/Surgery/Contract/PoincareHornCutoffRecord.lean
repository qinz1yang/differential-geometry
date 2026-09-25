import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornCutoffRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentClassification

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
private theorem incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq
    {P₀ P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory P₀} {i : Fin H.eventCount}
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
      (H : RetainedCoreHistory P₀) (initial : InitialIdentification P₀ g₀ H.toHistory),
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
        (K : RetainedCoreHistory P₀) (initialK : InitialIdentification P₀ g₀ K.toHistory)
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
    {P Q : OrientedThreeStage.{u}} (H K : RetainedCoreHistory P) {s : ℝ}
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
      (H : RetainedCoreHistory P₀) (initial : InitialIdentification P₀ g₀ H.toHistory),
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
        (K : RetainedCoreHistory P₀) (initialK : InitialIdentification P₀ g₀ K.toHistory)
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
