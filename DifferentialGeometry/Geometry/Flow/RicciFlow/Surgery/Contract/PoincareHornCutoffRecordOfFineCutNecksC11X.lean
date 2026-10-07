import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutoffRecordC11X

/-!
# PoincareHornCutoffRecordOfFineCutNecksC11X（S-CH11-EXT1）

extension of 已跟踪 `Contract/PoincareHornCutoffRecordOfFineCutNecks`。

宿主（W8，796 行）不变；本文件放 donor 新增 / 加强的 radial-coordinate 版本：

* `exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_C11X`
  （宿主私有同名定理的 SIG 加强，结论多 `HasRadialCoordinates`；改名 `_C11X`）；
* `exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks_`
  `with_radial_coordinates`（donor 新增，私有；名字在此处折行）；
* `exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks_`
  `with_radial_coordinates`（donor 新增，public；名字在此处折行）。

**偏差**：donor 的 at-scale 加强版是由 `…_with_distance_scalars` 版 forget 得到的，而后者依赖未落地的
`Topology.FiniteOutputDistanceScalar`（`C11-B1-LANDED.txt` 里 `SKIP`）；这里取 donor
`…_with_distance_scalars` 的证明体，删去 distance 相关的 4 处（`Cdist`、`hDistance` 及合取项），其余逐字，
statement 与 donor 的 at-scale 版逐字相同（脚本比对）。`…_with_distance_scalars` 本身记 reference-only。
-/

open private exists_uniform_selected_neck_retained_append_backward
  nonempty_incomingBackwardNeck_record_of_selected_restrictions from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PreparedHistoryCutoff

open private incoming_terminal_and_poincareStandardDiscarded_of_retainedEvent_heq
  RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecord

open private spatiallyCanonicalBefore_of_incoming_heq derivativeBoundBefore_of_incoming_heq
  exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks


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


private theorem exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_C11X :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
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
          (∀ b, (Record.static b).hasCanonicalWindow) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * Q ^ (-3 / 2 : ℝ)) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks_with_radial_coordinates.{u}
  refine ⟨fixed, c, hc, εcoarse, hεcoarse, ?_⟩
  intro Dtrace r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  obtain ⟨εold, δold, hεold, hδold, hthreshold⟩ :=
    exists_uniform_selected_neck_retained_append_backward Dtrace r tol a₀ Ctime ha₀ htol htolsmall
      hr hfit
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
    hprotected, hretained, hscale, hsource, hNrecord, hTube, hrecord, hvol, hcapNew⟩ :=
    hmake H initial htime D rfl rfl (heq_of_eq hinit) P hε hεc hεcε hεfactory' hfine Q hQscale
      hQnominal hQc
  have hB : ∀ j, Nonempty (IncomingBackwardNeck K.toHistory i
      (((NOriginal j).monoDelta (hδOriginal j) hδ1').lowerOrder (horderN j)) (Real.sqrt Q⁻¹)) := by
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
  have hBrecord := nonempty_incomingBackwardNeck_record_of_selected_restrictions
    NOriginal hδOriginal hδ1' horderN rotation hmarkN side Nrecord eOriginal hNrecord hB
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows, hRecordCoordinates⟩ :=
    hrecord hBrecord
  exact ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmarkN, side, horderN, hδ1', Nrecord, eOriginal,
    hQ, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC, hpM, hpD,
    hpAcc,
    hprotected, hretained, hscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows, hRecordCoordinates⟩, hvol, hcapNew⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set Function Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance {Q : OrientedThreeStage.{u}} {a s : ℝ} (G : Q.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)



private theorem exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks_with_radial_coordinates
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ ε₀ Λq : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < ε₀ ∧ 0 < Λq ∧
    ∀ q0 : ℝ, 0 < q0 →
    ∀ Λmax coreFloor : ℝ, 1 ≤ Λmax → 0 < coreFloor → ∀ Qlower : ℝ,
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ Λq * max q0 1 ≤ Q ∧ Qlower < Q ∧
      v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
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
    ∀ {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ εcoarse →
      ∀ {εc : ℝ}, 0 < εc → εc ≤ ε → εc ≤ ε₀ → P.FineCutNecks εc Q →
      Λ ≤ Λmax → coreFloor ≤ P.coreRadius →
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
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
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
          (∀ b, (Record.static b).hasCanonicalWindow) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  classical
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  obtain ⟨a, ha, htimeFloor⟩ :=
    exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  obtain ⟨fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_C11X.{u}
  refine ⟨fixed, c, hc, εcoarse, hεcoarse, ?_⟩
  intro Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  obtain ⟨εback, δold, hεback, hδold, hfactory⟩ :=
    hfactory Dtrace r tol a₀ Ctime ha₀ htol htolsmall hr hfit
  have hDbig : StandardCap.transitionEnd < Dbig := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr htol
    linarith
  obtain ⟨εscalar, hεscalar, hscalar⟩ :=
    exists_presented_cap_scalar_lower_bound_of_canonical_window Dbig hDbig
  refine ⟨min εback εscalar, δold, lt_min hεback hεscalar, hδold, ?_⟩
  intro m accuracy haccuracy ηrecord hηrecord
  obtain ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, hmake⟩ :=
    hfactory Dbig (StandardCap.transitionEnd_pos.trans hDbig) (by linarith) m accuracy haccuracy
      ηrecord hηrecord a ha Phi hPhi
  refine ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, ?_⟩
  intro q0 hq0 Λmax coreFloor hΛmax hcoreFloor Qlower
  let coreBound := 2 * Λmax * (coreFloor ^ 2)⁻¹
  let neckBound := ((δ ^ 2 * coreFloor) ^ 2)⁻¹
  let Q := max (max (Λq * max q0 1) Qlower) (max coreBound neckBound) + 1
  let v := Q ^ (-3 / 2 : ℝ)
  have hQlarge : Λq * max q0 1 < Q :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans_lt (lt_add_one _)
  have hQlower : Qlower < Q :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans_lt (lt_add_one _)
  have hQ : 0 < Q := (mul_pos hΛq (lt_max_of_lt_right one_pos)).trans hQlarge
  have hcoreBound : coreBound < Q :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (lt_add_one _)
  have hneckBound : neckBound < Q :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (lt_add_one _)
  refine ⟨Q, v, hQ, Real.rpow_pos_of_pos hQ _, hQlarge.le, hQlower, rfl, ?_⟩
  intro p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing stepParameters hinit D
    hderiv hfinal ε Λ P hε εc hεc hεcε hεc₀ hfine hΛ hcore
  have hs0 : 0 ≤ D.endTime := D.startTime_nonneg.trans D.startTime_lt_endTime.le
  have hneck : coreFloor ≤ D.parameters.neckRadius D.endTime := by
    have hdelta_lt := D.parameters.delta_lt_one D.endTime hs0
    have hneckpos := D.parameters.neckRadius_pos D.endTime hs0
    refine hcore.trans ?_
    rw [P.coreRadius_eq]
    exact mul_le_of_le_one_left hneckpos.le hdelta_lt.le
  have hcoreInv : (P.coreRadius ^ 2)⁻¹ ≤ (coreFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hcoreFloor) (pow_le_pow_left₀ hcoreFloor.le hcore 2)
  have hbase : 2 * Λ * (P.coreRadius ^ 2)⁻¹ < Q := by
    apply lt_of_le_of_lt ?_ hcoreBound
    apply mul_le_mul (by linarith : 2 * Λ ≤ 2 * Λmax) hcoreInv
    · exact inv_nonneg.mpr (sq_nonneg _)
    · linarith
  have hproduct : 0 < δ ^ 2 * coreFloor := mul_pos (sq_pos_of_pos hδ) hcoreFloor
  have hproduct_le : δ ^ 2 * coreFloor ≤ δ ^ 2 * D.parameters.neckRadius D.endTime :=
    mul_le_mul_of_nonneg_left hneck (sq_nonneg δ)
  have hnominal : ((δ ^ 2 * D.parameters.neckRadius D.endTime) ^ 2)⁻¹ < Q := by
    apply lt_of_le_of_lt ?_ hneckBound
    exact inv_anti₀ (sq_pos_of_pos hproduct) (pow_le_pow_left₀ hproduct.le hproduct_le 2)
  obtain ⟨p, _, hmodel, horder, haccuracyOld, _, records, hcanonical, hδpast, _⟩ := hInv
  have hstart := hinitial H.toHistory initial
  have hs := htimeFloor H.toHistory initial (fun j => (records j).singular)
    (Fin.last H.eventCount) s G hinit hsing
  have hcap : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (z : ThreeBall), ((records j).static b).neck.scale / 2 ≤
        metricScalarAt ((records j).static b).witness.metric
          (((records j).static b).witness.cap z) := by
    intro j b z
    have hh := hscalar (H.toHistory.event j) (fixed := p.fixed) (m := p.modelOrder)
      (ε := p.modelAccuracy)
    rw [← hpD, ← hmodel] at hh
    exact hh (haccuracyOld.trans_le (hpε.trans (min_le_right _ _))) (by omega)
      ((records j).static b) (hcanonical j b) z
  choose center precision order datum w hdatum hmetric hmark using hcanonical
  have hzero (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (y : standardCapWindow p.modelRadius) (v z : TangentSpace ThreeModel y) :
      (w j b).windowMetric.inner y v z = ((records j).static b).neck.scale *
        (H.initialMetric j.succ).inner (((records j).static b).window y)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window y z) := by
    have he : (H.toHistory.event j).outputMetric = H.initialMetric j.succ := H.event_output j
    have hh := hmetric j b y v z
    rw [he] at hh
    exact hh
  exact hmake q0 hq0 H initial htime s G L hsing stepParameters hinit hs
    p records hstart.1 hstart.2 (fun j b => ((records j).delta_le b).trans (hδpast j))
    (haccuracyOld.trans_le (hpε.trans (min_le_left _ _)))
    (by rw [hmodel, hpD]; exact hmargin) (by omega) hderiv hfinal
    (fun j => hpinch H.toHistory initial p records j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j))
    (hpinch H.toHistory initial p records (Fin.last H.eventCount) s G hinit)
    hcap center precision order datum w (fun j b => ((records j).static b).window)
    (fun j b => ((records j).static b).window_smooth) hzero hmark P hε hεc hεcε hεc₀ hfine
    Q hbase hnominal hQlarge.le le_rfl


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

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

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open OneStepIncoming in
theorem exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks_with_radial_coordinates
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εP εbar : ℝ, 0 < εP ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
    ∀ (Dtrace Dbig r tol : ℝ) (Ctime : ℝ≥0), Dtrace + 1 ≤ Dbig → 0 < tol → tol ≤ 1 / 1000 →
      StandardCap.transitionEnd + tol⁻¹ + 1 < r → 64 * (r + tol⁻¹) < Dtrace →
    ∃ εold δold : ℝ, 0 < εold ∧ 0 < δold ∧
    ∀ m : ℕ, ∀ accuracy : ℝ, 0 < accuracy → ∀ ηrecord : ℝ, 0 < ηrecord →
    ∃ δ εcut : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ηrecord ∧ 0 < εcut ∧ εcut ≤ εP ∧
    ∀ C1 C2 : ℝ, 1 ≤ C2 →
    ∃ C Λ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧
    ∀ qcan originalCoreFloor protectedFloor Kfine : ℝ,
      0 < qcan → 0 < originalCoreFloor → 0 < protectedFloor → 0 ≤ Kfine →
    ∃ Q v : ℝ, 0 < Q ∧ 0 < v ∧ v = Q ^ (-3 / 2 : ℝ) ∧
    ∀ (p₀ : CutoffParameters), p₀.modelRadius = Dbig →
      ⌈tol⁻¹⌉₊ + 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ εold →
    ∀ (H : RetainedCoreHistory.{u}) (initial : InitialIdentification P₀ g₀ H.toHistory),
      H.time (Fin.last H.eventCount) = H.horizon →
    ∀ ρold : ℝ, H.hasCanonicalCutoffRecords p₀ δold ρold →
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint)
      (stepParameters : CutoffParameters),
    G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) →
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
        qcan < (H.toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y, ∀ t ∈ Ioo (H.time (Fin.last H.eventCount)) s, qcan < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2) →
    originalCoreFloor ≤ D.parameters.delta D.endTime * D.parameters.neckRadius D.endTime →
    protectedFloor ≤ D.parameters.protectedRadius D.endTime →
    G.SpatiallyCanonicalBefore εbar C1 C2 qcan s →
    (∀ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t)
      (P : TerminalCorePresentation (D.withNeckRadius ρ hρ) εP Λ),
      Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q → P.FineCutNecks εcut Q) →
    ∃ (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ t → 0 < ρ t),
      (∀ t, 0 ≤ t → ρ t ≤ D.parameters.neckRadius t) ∧
      (Antitone D.parameters.neckRadius → Antitone ρ) ∧
      (AntitoneOn D.parameters.neckRadius (Ici 0) → AntitoneOn ρ (Ici 0)) ∧
      (HasRecenterConstants.{u} D.parameters →
        HasRecenterConstants.{u} (D.withNeckRadius ρ hρ).parameters) ∧
      D.parameters.delta D.endTime * ρ D.endTime ≤ D.parameters.protectedRadius D.endTime ∧
      let D' := D.withNeckRadius ρ hρ
      ∃ P : TerminalCorePresentation D' εP Λ,
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
      ∃ (Qout : OrientedThreeStage.{u})
        (E : MetricCutCapEvent D'.stage Qout D'.startTime D'.endTime)
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
        parameters.modelOrder = m ∧ parameters.modelRadius = Dbig ∧
        parameters.modelAccuracy = accuracy ∧
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
        (∀ j, δOriginal j ≤ 2 * εcut ∧ ⌊εcut⁻¹⌋₊ + 1 ≤ kOriginal j) ∧
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
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          E.poincareStandardDiscarded ∧ (K.toHistory.event i).poincareStandardDiscarded ∧
          (p₀.fixed = fixed → p₀.recenterConstant = recenterConstant →
            p₀.modelOrder = m → p₀.modelAccuracy = accuracy → ηrecord ≤ δold →
            D.parameters.neckRadius D.endTime ≤ ρold →
              K.hasCanonicalCutoffRecords p₀ δold ρold)) ∧
        (∃ Kvol : Set D'.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D'.slab.terminalRegularOpen D'.terminal.metric
            Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks_with_radial_coordinates P₀ g₀
  obtain ⟨eta, heta, htopology⟩ :=
    exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical.{u}
  have hεP : 0 < min εcoarse eta := lt_min hεcoarse heta
  obtain ⟨εbar, hεbar, hεbarSmall, hεbarP, hgeometry⟩ :=
    exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_spatiallyCanonical.{u}
      hεP
  have hεbarTop : εbar ≤ eta := by
    have hPeta : min εcoarse eta ≤ eta := min_le_right _ _
    linarith
  refine ⟨fixed, c, hc, min εcoarse eta, εbar, hεP, hεbar, hεbarSmall, ?_⟩
  intro Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  obtain ⟨εold, δold, hεold, hδold, hfactory⟩ :=
    hfactory Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  refine ⟨εold, δold, hεold, hδold, ?_⟩
  intro m accuracy haccuracy ηrecord hηrecord
  obtain ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, hmake⟩ :=
    hfactory m accuracy haccuracy (min ηrecord εbar) (lt_min hηrecord hεbar)
  have hδrecord : δ ≤ ηrecord := hδη.trans (min_le_left _ _)
  have hδbar : δ ≤ εbar := hδη.trans (min_le_right _ _)
  have hεcut : 0 < min (min εcoarse eta) ε₀ := lt_min hεP hε₀
  refine ⟨δ, min (min εcoarse eta) ε₀, hδ, hδ1, hδrecord, hεcut, min_le_left _ _, ?_⟩
  intro C1 C2 hC2
  obtain ⟨C, Λ, hC, hΛ, hgeometry⟩ := hgeometry C1 C2 hC2
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro qcan originalCoreFloor protectedFloor Kfine hqcan hcoreFloor hprotectedFloor hKfine
  obtain ⟨radiusFloor, hradiusFloor, hgeometry⟩ :=
    hgeometry (C * qcan) originalCoreFloor protectedFloor
      (mul_pos (zero_lt_one.trans_le hC) hqcan) hcoreFloor hprotectedFloor
  obtain ⟨Q, v, hQ, hv, -, hQlower, hvQ, hmake⟩ :=
    hmake qcan hqcan Λ radiusFloor hΛ hradiusFloor
      (max (C2 ^ 2 * (radiusFloor ^ 2)⁻¹) (Kfine * max (Λ * (radiusFloor ^ 2)⁻¹) (max qcan 1)))
  refine ⟨Q, v, hQ, hv, hvQ, ?_⟩
  intro p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing stepParameters hinit D
    hderiv hfinal hcore hprotected hcanonical hfine
  have hgeo : D.slab.SpatiallyCanonicalBefore εbar C1 C2 (C * qcan) D.endTime := by
    intro y t ht hy
    exact hcanonical y t ht ((le_mul_of_one_le_left hqcan.le hC).trans_lt hy)
  obtain ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hfloor, _, hscale, hupper, hlow, hbase⟩ := hgeometry D hcore hprotected hgeo
  have hqcore : qcan < (P.coreRadius ^ 2)⁻¹ :=
    (mul_lt_mul_iff_right₀ (zero_lt_one.trans_le hC)).mp hscale
  have hinvle : (P.coreRadius ^ 2)⁻¹ ≤ (radiusFloor ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hradiusFloor)
      ((sq_le_sq₀ hradiusFloor.le P.coreRadius_pos.le).mpr hfloor)
  have hQtop : C2 ^ 2 * (P.coreRadius ^ 2)⁻¹ < Q :=
    (mul_le_mul_of_nonneg_left hinvle (sq_nonneg C2)).trans_lt
      ((le_max_left _ _).trans_lt hQlower)
  have hfineP : Kfine * max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q := by
    have hmax : max (Λ * (P.coreRadius ^ 2)⁻¹) (max qcan 1) ≤
        max (Λ * (radiusFloor ^ 2)⁻¹) (max qcan 1) :=
      max_le_max (mul_le_mul_of_nonneg_left hinvle (zero_le_one.trans hΛ)) le_rfl
    exact (mul_le_mul_of_nonneg_left hmax hKfine).trans
      ((le_max_right _ _).trans_lt hQlower).le
  refine ⟨ρ, hρ, hρle, hmono, hmonoOn, hrecenter, hprotect, P, hradius,
    hqcore, hupper, hlow, hbase, ?_⟩
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotectedNew, hretained, hNscale, hsource, hNrecord, hTube,
    hrecord, hvol, hcap⟩ :=
    hmake p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing
      (stepParameters.withNeckRadius ρ hρ) hinit hderiv hfinal P (min_le_left _ _) hεcut
      (min_le_left _ _) (min_le_right _ _) (hfine ρ hρ P hfineP) le_rfl hfloor
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows, hRecordCoordinates⟩ :=
    hrecord
  have hcanE : E.incoming.SpatiallyCanonicalBefore εbar C1 C2 qcan D.endTime := by
    rw [hG]
    exact hcanonical
  have hderivE : E.incoming.DerivativeBoundBefore Ctime qcan D.endTime := by
    rw [hG]
    exact hfinal
  obtain ⟨hstdE, hstdK⟩ := htopology εbar hεbarTop E
    hsrc hout hsrcTime houtTime hOld hEvent hBoundary parameters Record C1 C2 qcan
    (P.coreRadius ^ 2)⁻¹ Q hC2 hqcan hqcore hQtop
    (by rw [hpR]) (by intro j; rw [hRecordDelta]; exact hδbar) hRecordScale hcanE Ctime hderivE
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal,
    hδOriginal, rotation, hmark, side, horder, hδ1', Nrecord, eOriginal,
    hQpos, hG, hL, hBoundary, hprefix, hhor, hcount, hlasttime, hlaststage, hlastmetric,
    hi, hsrc, hsrcTime, hout, houtTime, hEvent, happend, hpδ, hpR, hpρ, hpFixed, hpC,
    hpM, hpDnew, hpAcc, hprotectedNew, hretained, hNscale, hsource, hNrecord, hTube,
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows, hRecordCoordinates,
      hstdE, hstdK, ?_⟩, hvol, hcap⟩
  intro hfixed hrecenter hmodelOrder hmodelAccuracy hηold hρold
  obtain ⟨Eappend, hOldAppend, hInitial, _, hK⟩ := happend
  apply RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq H K Eappend hOldAppend
    hInitial hK i hi hInv Record (hpFixed.trans hfixed.symm) (hpDnew.trans hpD.symm)
    (hpM.trans hmodelOrder.symm) (hpAcc.trans hmodelAccuracy.symm)
    (hpC.trans hrecenter.symm) hRecordWindows
  · rw [hpδ]
    exact hδrecord.trans hηold
  · rw [hpρ]
    exact (hρle D.endTime (D.startTime_nonneg.trans D.startTime_lt_endTime.le)).trans hρold


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
