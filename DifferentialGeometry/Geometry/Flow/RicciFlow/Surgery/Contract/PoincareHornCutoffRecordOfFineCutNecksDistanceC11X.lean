import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutoffRecordDistanceC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.DeepCutoffProducerC12X

/-!
# PoincareHornCutoffRecordOfFineCutNecksDistanceC11X

S-CH11-FIX7；extension of 已跟踪 `Contract/PoincareHornCutoffRecordOfFineCutNecks`。

EXT1 的 `PoincareHornCutoffRecordOfFineCutNecksC11X` 当时因 `Topology.FiniteOutputDistanceScalar` 未落地，
只能放 distance-free 的 at-scale producer（`…_C11X`，由 donor 的 `…_with_distance_scalars` 证明体删去
distance 相关 4 处得到）。`FiniteOutputDistanceScalar` 已由 S-CH11-FIX7 落地，本文件把 donor 的

* 私有 `exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_with_distance_scalars`
  （donor `PoincareHornCutoffRecordOfFineCutNecks` L31–260）

按 donor 原文逐字补回（它调用 `HornFineCutoffRecordDistanceC11X` 里的 distance 版 history extension）。
下游 `UniformFineCutoffScaffold` 用 `open private … from` 取它。
-/

open private nonempty_incomingBackwardNeck_record_of_selected_restrictions from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PreparedHistoryCutoff

open private incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq
  RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecord

set_option autoImplicit false

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)


private theorem exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
    (4 ≤ recenterConstant ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (Dtrace r tol a₀ : ℝ) (Ctime : ℝ≥0), 0 < a₀ → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ Dcap : ℝ, 0 < Dcap → StandardCap.transitionEnd < Dcap + 1 →
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy →
    ∀ ηrecord : ℝ, 0 < ηrecord →
    ∀ a : ℝ, 0 < a →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∀ q0 : ℝ, 0 < q0 →
    ∀ {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
      (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters)
      (_ : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)),
    a ≤ s →
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
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount,
      GeometricCutoffRecord H.toHistory j parameters),
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ j b, (records j).delta b ≤ δold) → parameters.modelAccuracy ≤ εold →
    Dtrace + 1 ≤ parameters.modelRadius → ⌈tol⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    (∀ j : Fin H.eventCount, ∀ y : (H.stage j.castSucc).Carrier,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q0 < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, q0 < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
      (Ico (H.time j.castSucc) (H.time j.succ)) phi) →
    Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
    (∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
      ((records j).static b).neck.scale / 2 ≤ metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap z)) →
    ∀ (center : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        (H.toHistory.event j).incoming.terminalRegularOpen)
      (precision : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℝ)
      (order : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex → ℕ)
      (d : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        normalizedDatum (H.toHistory.event j).terminal.metric (center j b) (precision j b)
          (order j b))
      (w : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
        StandardCap.CanonicalStaticInsertionWitness (d j b)
          parameters.fixed.collarLength parameters.fixed.collar_pos parameters.modelRadius
          parameters.modelOrder parameters.modelAccuracy)
      (Jbig : ∀ j : Fin H.eventCount, (H.toHistory.event j).RetainedBoundaryIndex →
        standardCapWindow parameters.modelRadius → (H.stage j.succ).Carrier),
    (∀ j b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j b)) →
    (∀ j b y (v z : TangentSpace ThreeModel y), (w j b).windowMetric.inner y v z =
      ((records j).static b).neck.scale * (H.initialMetric j.succ).inner (Jbig j b y)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y v)
        (mfderiv ThreeModel ThreeModel (Jbig j b) y z)) →
    (∀ j b z, ∃ u : standardCapWindow parameters.modelRadius,
      ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      Jbig j b u = ((records j).static b).inclusion (((records j).static b).witness.cap z)) →
      ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc Qc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Qc →
      ∀ Q : ℝ, 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q →
      (((δ ^ 2 * D.parameters.neckRadius D.endTime) ^ 2)⁻¹) < Q → Λq * max q0 1 ≤ Q → Qc ≤ Q →
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
        parameters.modelOrder = m ∧ parameters.modelRadius = Dcap ∧
        parameters.modelAccuracy = accuracy ∧
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
        (∀ j, δOriginal j ≤ 2 * εc ∧ ⌊εc⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (parameters.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ parameters.modelRadius →
          E.HasUniformDistanceScalar Cdist ∧
          (K.toHistory.event i).HasUniformDistanceScalar Cdist) := by
  obtain ⟨Cdist, hCdist, fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks_with_radial_coordinates_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, c, hc, εcoarse, hεcoarse, ?_⟩
  intro Dtrace r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  obtain ⟨εold, δold, hεold, hδold, hthreshold⟩ :=
    exists_uniform_selected_neck_retained_append_backwardDeep_C12X Dtrace r tol a₀ Ctime ha₀ htol
      htolsmall hr hfit (θ := 5 / 4) (by norm_num) (by norm_num)
  refine ⟨εold, δold, hεold, hδold, ?_⟩
  intro Dcap hDcap hDfit m accuracy haccuracy ηrecord hηrecord a ha phi hphi
  obtain ⟨δ, εfactory, hδ, hδ1, hδη, hεfactory, hmake⟩ :=
    hfactory Dcap hDcap hDfit m accuracy haccuracy ηrecord hηrecord
  let k := max (m + 6) (2 * ⌊δ⁻¹⌋₊ + 4)
  obtain ⟨ηstar, mstar, Λq, hηδ, hkm, hηstar, hΛq, hback⟩ :=
    hthreshold hδ hδ1 k a ha phi hphi
  let ε₀ := min εfactory (min (ηstar / 2) (((mstar : ℝ) + 1)⁻¹))
  have hε₀ : 0 < ε₀ := lt_min hεfactory (lt_min (half_pos hηstar) (by positivity))
  refine ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, ?_⟩
  intro q0 hq0 P₀ g₀ H initial htime s G L hsing stepParameters hinit hsa D
    pold records hfixed hlower hdelta hacc hmargin hm hderiv hfinal hpinch hpinchFinal hcap
    center precision order d w Jbig hJbig hzero hmark ε Λ P hε εc Qc hεc hεcε hεc₀ hfine
    Q hQscale hQnominal hQlarge hQc
  have hεfactory' : εc ≤ εfactory := hεc₀.trans (min_le_left _ _)
  have hεη : 2 * εc ≤ ηstar := by
    have hh := hεc₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hεm : (mstar : ℝ) + 1 ≤ εc⁻¹ := by
    have hh : εc ≤ ((mstar : ℝ) + 1)⁻¹ :=
      hεc₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [inv_inv] using inv_anti₀ hεc hh
  have hmFloor : mstar ≤ ⌊εc⁻¹⌋₊ + 1 :=
    (Nat.le_floor (by linarith : (mstar : ℝ) ≤ εc⁻¹)).trans (Nat.le_succ _)
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmarkN, side, horderN, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD,
    hpAcc,
    hprotected, hretained, hscale, hsource, hNrecord, hTube, hrecord, hvol, hcapNew, hDistance⟩ :=
    hmake H initial htime D rfl rfl (heq_of_eq hinit) P hε hεc hεcε hεfactory' hfine Q hQscale
      hQnominal hQc
  have hBdeep : ∀ j, Nonempty (IncomingBackwardNeckDeep_C12X K.toHistory i
      (((NOriginal j).monoDelta (hδOriginal j) hδ1').lowerOrder (horderN j)) (Real.sqrt Q⁻¹)
      (5 / 4)) := by
    obtain ⟨Eappend, hOldAppend, hInitial, hEappend, hK⟩ := happend
    have hEqE : Eappend = E := eq_of_heq hEappend
    subst Eappend
    subst K
    have hlasti : i = Fin.last H.eventCount := Fin.ext hi
    subst i
    intro j
    have hηj : δOriginal j ≤ ηstar := (hsource j).1.trans hεη
    have hmj : mstar ≤ kOriginal j := hmFloor.trans (hsource j).2
    have hQj : Λq * max q0 1 ≤ (NOriginal j).scale := hQlarge.trans_eq (hscale j).symm
    have hfinalE : ∀ y, ∀ t ∈ Set.Ioo (H.time (Fin.last H.eventCount)) s,
        q0 < E.incoming.flow.scalar t y →
        |derivWithin (fun v => E.incoming.flow.scalar v y) (Set.Iic t) t| ≤
          Ctime * E.incoming.flow.scalar t y ^ 2 := by
      have hGE : E.incoming = G := hG
      rw [hGE]
      exact hfinal
    have hpinchE : Perelman.PhiAlmostNonnegative E.incoming.flow
        (Set.Ico (H.time (Fin.last H.eventCount)) s) phi := by
      have hGE : E.incoming = G := hG
      rw [hGE]
      exact hpinchFinal
    have hb := hback q0 hq0 H s Qout E hOldAppend hInitial hsa pold records hfixed hlower hdelta
      hacc hmargin hm hderiv hfinalE hpinch hpinchE hcap center precision order d w Jbig hJbig hzero
      hmark
      (δOriginal j) (kOriginal j) (NOriginal j) hηj hmj hQj
    have hsc : (((NOriginal j).monoDelta (hδOriginal j) hδ1').lowerOrder (horderN j)).scale = Q :=
      hscale j
    simpa only [hsc] using hb
  have hB := fun j => (hBdeep j).map IncomingBackwardNeckDeep_C12X.toIncomingBackwardNeck
  have hBrecord := nonempty_incomingBackwardNeck_record_of_selected_restrictions
    NOriginal hδOriginal hδ1' horderN rotation hmarkN side Nrecord eOriginal hNrecord hB
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows, hRecordCoordinates⟩ :=
    hrecord hBrecord
  have hRecordDeep : Record.DeepNecks_C12X (5 / 4) :=
    GeometricCutoffRecord.deepNecks_of_selected_restrictions_C12X NOriginal hδOriginal hδ1' horderN
      rotation hmarkN side Nrecord eOriginal hNrecord hBdeep Record hRecordDelta hRecordOrder
      hRecordNeck hRecordScale
  exact ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmarkN, side, horderN, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD,
    hpAcc,
    hprotected, hretained, hscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows,
      hRecordCoordinates, hRecordDeep⟩, hvol, hcapNew, hDistance⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
