import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecksLongSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.CanonicalNeighborhood.UniformEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingToSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricExistence

open private RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecord

open private exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks
  exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open OneStepIncoming in
private theorem exists_horn_cutoff_record_of_fineCutNecks_of_le
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ) (hη : 0 < η) :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εP εbar : ℝ, 0 < εP ∧ εP ≤ η ∧ 0 < εbar ∧ εbar < 1 / 11 ∧
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
    exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks P₀ g₀
  obtain ⟨eta, heta, htopology⟩ :=
    exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical.{u}
  have hεP : 0 < min (min εcoarse eta) η := lt_min (lt_min hεcoarse heta) hη
  obtain ⟨εbar, hεbar, hεbarSmall, hεbarP, hgeometry⟩ :=
    exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_spatiallyCanonical.{u}
      hεP
  have hεbarTop : εbar ≤ eta := by
    have hPeta : min (min εcoarse eta) η ≤ eta :=
      (min_le_left _ _).trans (min_le_right _ _)
    linarith
  refine ⟨fixed, c, hc, min (min εcoarse eta) η, εbar, hεP, min_le_right _ _, hεbar,
    hεbarSmall, ?_⟩
  intro Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  obtain ⟨εold, δold, hεold, hδold, hfactory⟩ :=
    hfactory Dtrace Dbig r tol Ctime hmargin htol htolsmall hr hfit
  refine ⟨εold, δold, hεold, hδold, ?_⟩
  intro m accuracy haccuracy ηrecord hηrecord
  obtain ⟨δ, ε₀, Λq, hδ, hδ1, hδη, hε₀, hΛq, hmake⟩ :=
    hfactory m accuracy haccuracy (min ηrecord εbar) (lt_min hηrecord hεbar)
  have hδrecord : δ ≤ ηrecord := hδη.trans (min_le_left _ _)
  have hδbar : δ ≤ εbar := hδη.trans (min_le_right _ _)
  have hεcut : 0 < min (min (min εcoarse eta) η) ε₀ := lt_min hεP hε₀
  refine ⟨δ, min (min (min εcoarse eta) η) ε₀, hδ, hδ1, hδrecord, hεcut, min_le_left _ _, ?_⟩
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
      (stepParameters.withNeckRadius ρ hρ) hinit hderiv hfinal P
      ((min_le_left _ _).trans (min_le_left _ _)) hεcut
      (min_le_left _ _) (min_le_right _ _) (hfine ρ hρ P hfineP) le_rfl hfloor
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows⟩ :=
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
    ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows,
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

private theorem fineCutNecks_of_le {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    {P : TerminalCorePresentation D ε Λ} {εc εc' Qc : ℝ} (hεc : 0 < εc) (hle : εc ≤ εc')
    (hP : P.FineCutNecks εc Qc) : P.FineCutNecks εc' Qc := by
  intro c e x hx hQ
  obtain ⟨δ, k, N, hN, hδ, hk⟩ := hP c e x hx hQ
  exact ⟨δ, k, N, hN, hδ.trans hle,
    (Nat.add_le_add_right (Nat.floor_le_floor (inv_anti₀ hεc hle)) 1).trans hk⟩

private theorem hasCanonicalCutoffRecords_of_le
    {H : RetainedCoreHistory.{u}} {p₀ : CutoffParameters} {δ δ' ρ ρ' : ℝ} (hδ : δ ≤ δ')
    (hρ : ρ ≤ ρ') (hH : H.hasCanonicalCutoffRecords p₀ δ ρ) :
    H.hasCanonicalCutoffRecords p₀ δ' ρ' := by
  obtain ⟨p, h1, h2, h3, h4, h5, records, hw, hd, hn⟩ := hH
  exact ⟨p, h1, h2, h3, h4, h5, records, hw, fun i => (hd i).trans hδ, fun i => (hn i).trans hρ⟩

private theorem exists_compact_volume_debit_of_incoming_eq {P Q : OrientedThreeStage.{u}}
    {a s : ℝ} (E : MetricCutCapEvent P Q a s) (G : P.IncomingSlab a s)
    (L : G.TerminalLimitMetric) (hG : E.incoming = G) (hL : HEq E.terminal L) (X : ℝ≥0∞)
    (h : ∃ F : Set G.terminalRegularOpen, IsCompact F ∧
      X ≤ riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric F) :
    ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
      X ≤ riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
        E.terminal.metric F := by
  subst hG
  cases eq_of_heq hL
  exact h

theorem uniformDebitSurgeryStepStrong_of_long_slabs
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    (hlong : ∀ B θ : ℝ, 0 < B → 0 < θ → ∃ Qθ : ℝ,
      ∀ H : RetainedCoreHistory.{u}, InitialIdentification P₀ g₀ H.toHistory → H.horizon < B →
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s),
        s ≤ B → G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
        ∀ Qc : ℝ, Qθ ≤ Qc → 2 * θ ≤ Qc * (s - H.time (Fin.last H.eventCount))) :
    UniformDebitSurgeryStepStrong P₀ g₀ := by
  obtain ⟨eta, εcone, heta, hεcone, hB12⟩ :=
    TerminalCorePresentation.exists_fineCutNecks_of_long_terminal_slab.{u}
  obtain ⟨fixed, c, hc, εP, εF, hεP, hεPη, hεF, hεF11, hF⟩ :=
    exists_horn_cutoff_record_of_fineCutNecks_of_le P₀ g₀ eta heta
  obtain ⟨Φ, hΦ, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  intro B εbar hB hεbar
  refine ⟨c, by linarith, ?_⟩
  intro Ctime
  have hε : 0 < min εbar (min εF εcone) := lt_min hεbar (lt_min hεF hεcone)
  have hεεF : min εbar (min εF εcone) ≤ εF := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min εbar (min εF εcone), hε, hεεF.trans_lt hεF11, min_le_left _ _, ?_⟩
  intro C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Cgrad κ a₀ _ _ _ hC2s hqcan _
    hδmax hρmax hεcap hDcap hκ _
  obtain ⟨r, hr⟩ : ∃ r : ℝ, StandardCap.transitionEnd + (1 / 1000 : ℝ)⁻¹ + 1 < r :=
    ⟨_, lt_add_one _⟩
  obtain ⟨Dtrace, hDtrace⟩ : ∃ Dtrace : ℝ, 64 * (r + (1 / 1000 : ℝ)⁻¹) < Dtrace :=
    ⟨_, lt_add_one _⟩
  obtain ⟨εold, δold, hεold, hδold, hF⟩ := hF Dtrace (max Dcap (Dtrace + 1)) r (1 / 1000)
    Ctime (le_max_right _ _) (by norm_num) le_rfl hr hDtrace
  obtain ⟨δ, εcut, -, -, hδη, hεcut, -, hF⟩ :=
    hF (max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)) (min εold εcap) (lt_min hεold hεcap)
      (min δold δmax) (lt_min hδold hδmax)
  have hεc : 0 < min εcut (1 / 4) := lt_min hεcut (by norm_num)
  obtain ⟨K, θ, hK, hθ, hfineK⟩ := hB12 hκ hε C1s C2s Ctime Cgrad hΦ (min εbar (min εF εcone))
    ((min_le_right _ _).trans (min_le_right _ _)) hεc
    ((min_le_right _ _).trans_lt (by norm_num))
  obtain ⟨Qθ, hQθ⟩ := hlong B θ hB hθ
  obtain ⟨C, Λ, -, -, hF⟩ := hF C1s C2s hC2s
  have hρb : 0 < min ρmax 1 := lt_min hρmax one_pos
  have hKfine : 0 ≤ max K Qθ := le_max_of_le_left (zero_le_one.trans hK)
  obtain ⟨Q, v, -, hv, -, hF⟩ := hF qcan (1 / 2 * min ρmax 1) 1 (max K Qθ) hqcan
    (by positivity) one_pos hKfine
  obtain ⟨p₀, hpf, hpD, hpm, hpa, hpc, hpδ, hpρ, hpp⟩ : ∃ p₀ : CutoffParameters,
      p₀.fixed = fixed ∧ p₀.modelRadius = max Dcap (Dtrace + 1) ∧
      p₀.modelOrder = max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2) ∧
      p₀.modelAccuracy = min εold εcap ∧ p₀.recenterConstant = c ∧
      p₀.delta = (fun _ => 1 / 2) ∧ p₀.neckRadius = (fun _ => min ρmax 1) ∧
      p₀.protectedRadius = (fun _ => 1) :=
    ⟨{ delta := fun _ => 1 / 2
       neckRadius := fun _ => min ρmax 1
       protectedRadius := fun _ => 1
       delta_pos := fun _ _ => by norm_num
       delta_lt_one := fun _ _ => by norm_num
       neckRadius_pos := fun _ _ => hρb
       protectedRadius_pos := fun _ _ => one_pos
       fixed := fixed
       modelRadius := max Dcap (Dtrace + 1)
       modelRadius_pos := lt_max_of_lt_left hDcap
       modelOrder := max mcap (⌈(1 / 1000 : ℝ)⁻¹⌉₊ + 2)
       modelAccuracy := min εold εcap
       modelAccuracy_pos := lt_min hεold hεcap
       recenterConstant := c
       recenterConstant_ge_four := hc }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨p₀, min δold δmax, min ρmax 1, v, hpa ▸ min_le_right _ _, hpD ▸ le_max_left _ _,
    hpm ▸ le_max_left _ _, lt_min hδold hδmax, min_le_right _ _, hρb, min_le_left _ _,
    hpc.le, hv, ?_⟩
  intro H initial hend hhor hclass hderH _ _ _ _ _ s G hs hG hsing hderG hgradG _ hspatG hncG
  obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
  have hclassF : H.hasCanonicalCutoffRecords p₀ δold (min ρmax 1) :=
    hasCanonicalCutoffRecords_of_le (min_le_left _ _) le_rfl hclass
  have hspatF : G.SpatiallyCanonicalBefore εF C1s C2s qcan s :=
    G.spatiallyCanonicalBefore_mono_eps hεεF hεF11 hspatG
  have hpin : Perelman.PhiAlmostNonnegative G.flow
      (Ico (H.time (Fin.last H.eventCount)) s) Φ ∧ H.EventSlabsPinched Φ := by
    obtain ⟨p', -, -, -, -, -, records, -⟩ := hclass
    exact ⟨hpinch H.toHistory initial p' records (Fin.last H.eventCount) s G hG,
      fun j => hpinch H.toHistory initial p' records j.castSucc (H.time j.succ) _
        (H.event_initial j)⟩
  have hderEv : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) :=
    fun j _ y t ht hy => hderH j y t ht hy
  have hs0 : 0 ≤ s := (H.toHistory.time_nonneg _).trans G.lt.le
  obtain ⟨ρ, hρ, hρle, -, -, -, -, P, -, -, -, -, -, Qout, E, hOld, K', initialK, i, parameters,
      n, δO, kO, NO, hδO, rot, hmark, side, hord, hδ1, Nrec, eO, -, hEG, hEL, hbfr, -, -, -, -,
      -, -, hi, -, -, -, -, -, happend, hpδ', -, hpρ', hpf', hpc', hpm', hpD', hpa', -, -, -,
      -, -, -, hrecord, hvol, -⟩ :=
    hF p₀ hpD (by rw [hpm]; exact le_max_right _ _) (by rw [hpa]; exact min_le_left _ _) H
      initial hend (min ρmax 1) hclassF s G L hsing p₀ hG hderH hderG
      (by change _ ≤ p₀.delta s * p₀.neckRadius s; rw [hpδ, hpρ])
      (by change _ ≤ p₀.protectedRadius s; rw [hpp]) hspatF
      (fun ρ' hρ' P' hKQ => by
        have hM : 1 ≤ max (Λ * (P'.coreRadius ^ 2)⁻¹) (max qcan 1) :=
          (le_max_right _ _).trans (le_max_right _ _)
        have hKQ' : K * max (Λ * (P'.coreRadius ^ 2)⁻¹) (max qcan 1) ≤ Q :=
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hM)).trans hKQ
        have hQθQ : Qθ ≤ Q :=
          (le_max_right K Qθ).trans ((le_mul_of_one_le_right hKfine hM).trans hKQ)
        exact fineCutNecks_of_le hεc (min_le_left _ _)
          (hfineK H hend G L hsing (p₀.withNeckRadius ρ' hρ') hG qcan hderEv
            (fun y t ht hy => hderG y t ht hy) hgradG hpin.2 hpin.1 hspatG hncG P' hεPη Q hKQ'
            (hQθ H initial hhor s G hs hG hsing Q hQθQ)))
  obtain ⟨Record, -, -, -, -, hwin, hstdE, -, -⟩ := hrecord
  obtain ⟨Eappend, hOldAppend, hInitial, hHEq, hK⟩ := happend
  have hEE := eq_of_heq hHEq
  subst hEE
  subst hK
  have hi' : i = Fin.last H.eventCount := Fin.ext hi
  subst hi'
  refine ⟨Qout, Eappend.toRetainedCoreEvent hOldAppend, hInitial, parameters, hEG, ?_,
    hpf'.trans hpf.symm, hpD'.trans hpD.symm, hpm'.trans hpm.symm, hpa'.trans hpa.symm,
    hpc'.trans hpc.symm, ⟨Record⟩, hbfr, hstdE, ?_⟩
  · exact H.hasCanonicalCutoffRecords_appendEvent _ (Eappend.toRetainedCoreEvent hOldAppend)
      hInitial hclass Record (hpf'.trans hpf.symm) (hpD'.trans hpD.symm) (hpm'.trans hpm.symm)
      (hpa'.trans hpa.symm) (hpc'.trans hpc.symm) hwin ((congrFun hpδ' s).le.trans hδη)
      ((congrFun hpρ' s).le.trans ((hρle s hs0).trans (congrFun hpρ s).le))
  · exact exists_compact_volume_debit_of_incoming_eq Eappend G L hEG hEL _ hvol

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
