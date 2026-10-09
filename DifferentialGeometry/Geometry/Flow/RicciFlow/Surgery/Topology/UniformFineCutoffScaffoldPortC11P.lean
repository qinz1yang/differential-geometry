import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFactory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksDistanceC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates

/-!
# S-CH11-FIX7 port of astra `UniformFineCutoffScaffold`（`PortC11P`）

来源：donor `UniformFineCutoffScaffold.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败；本 port 只做 elaboration 层面修补
（no statement / definition / proof idea altered）：
* 新增 import：`PoincareHornCutoffRecordOfFineCutNecksDistanceC11X`（S-CH11-FIX7 补回的 donor
  `…_with_distance_scalars` 私有声明，见该文件）、`Topology.EventDistanceScalar`
  （`MetricCutCapEvent.HasUniformDistanceScalar`）、`Topology.StaticCapCoordinates`
  （`StaticCapWitness.HasRadialCoordinates`）：donor 里它们经被替换的宿主传递 import，本树里宿主是
  extension 的底座，需要显式 import。
* `open private … from …PoincareHornCutoffRecordOfFineCutNecks` 一条拆成两条：distance 版取自
  extension 文件，`exists_poincareStandardDiscarded_…` 仍取自宿主；donor 同一条里列出的非 distance
  `exists_horn_cutoff_record_at_scale_…_fineCutNecks` 在本文件里从未使用，删去。
* `dsimp only at radialProjectionh68 ⊢` 与 `dsimp only at distanceProjectionh68 ⊢`（donor 两个投影定理里
  各一处）在本树 `dsimp made no progress`，写成 `try`。
原路径 `UniformFineCutoffScaffold` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open private
  exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_with_distance_scalars from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecksDistanceC11X

open private
  exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecordOfFineCutNecks

open private RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareHornCutoffRecord

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- One scaffold and recenter constant serve every initial metric. The actual
initial curvature, pinching and singular-time choices remain inside the
metric-dependent callback; the selected record and volume debit are retained. -/
theorem exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
    (4 ≤ recenterConstant ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (parameters.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ parameters.modelRadius →
          E.HasUniformDistanceScalar Cdist ∧
          (K.toHistory.event i).HasUniformDistanceScalar Cdist) := by
  classical
  obtain ⟨Cdist, hCdist, fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, c, hc, εcoarse, hεcoarse, ?_⟩
  intro P₀ g₀
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  obtain ⟨a, ha, htimeFloor⟩ :=
    exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
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

/-- Forget the distance certificate from the same producer result. -/
theorem exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  obtain ⟨_, _, distanceProjectionSource⟩ :=
    exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates_with_distance_scalars.{u}
  obtain ⟨fixed, recenterConstant, distanceProjectionh1⟩ := distanceProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2.1, ?_⟩
  obtain ⟨εcoarse, distanceProjectionh4⟩ := distanceProjectionh3
  refine ⟨εcoarse, ?_⟩
  obtain ⟨distanceProjectionfield5, distanceProjectionh6⟩ := distanceProjectionh4
  refine ⟨distanceProjectionfield5, ?_⟩
  intro P₀ g₀ Dtrace Dbig r tol Ctime distanceProjectionx7 distanceProjectionx8 distanceProjectionx9
    distanceProjectionx10 distanceProjectionx11
  have distanceProjectionh12 := @distanceProjectionh6 P₀ g₀ Dtrace Dbig r tol Ctime
    distanceProjectionx7 distanceProjectionx8 distanceProjectionx9 distanceProjectionx10
    distanceProjectionx11
  obtain ⟨εold, δold, distanceProjectionh13⟩ := distanceProjectionh12
  refine ⟨εold, δold, ?_⟩
  obtain ⟨distanceProjectionfield14, distanceProjectionfield15, distanceProjectionh16⟩ :=
    distanceProjectionh13
  refine ⟨distanceProjectionfield14, distanceProjectionfield15, ?_⟩
  intro m accuracy distanceProjectionx17 ηrecord distanceProjectionx18
  have distanceProjectionh19 := @distanceProjectionh16 m accuracy distanceProjectionx17 ηrecord
    distanceProjectionx18
  obtain ⟨δ, ε₀, Λq, distanceProjectionh20⟩ := distanceProjectionh19
  refine ⟨δ, ε₀, Λq, ?_⟩
  obtain ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
    distanceProjectionfield24, distanceProjectionfield25, distanceProjectionh26⟩ :=
    distanceProjectionh20
  refine ⟨distanceProjectionfield21, distanceProjectionfield22, distanceProjectionfield23,
    distanceProjectionfield24, distanceProjectionfield25, ?_⟩
  intro q0 distanceProjectionx27 Λmax coreFloor distanceProjectionx28 distanceProjectionx29 Qlower
  have distanceProjectionh30 := @distanceProjectionh26 q0 distanceProjectionx27 Λmax coreFloor
    distanceProjectionx28 distanceProjectionx29 Qlower
  obtain ⟨Q, v, distanceProjectionh31⟩ := distanceProjectionh30
  refine ⟨Q, v, ?_⟩
  obtain ⟨distanceProjectionfield32, distanceProjectionfield33, distanceProjectionfield34,
    distanceProjectionfield35, distanceProjectionfield36, distanceProjectionh37⟩ :=
    distanceProjectionh31
  refine ⟨distanceProjectionfield32, distanceProjectionfield33, distanceProjectionfield34,
    distanceProjectionfield35, distanceProjectionfield36, ?_⟩
  intro p₀ distanceProjectionx38 distanceProjectionx39 distanceProjectionx40 H initial
    distanceProjectionx41 ρold distanceProjectionx42 s G L hsing stepParameters
    distanceProjectionx43
  have distanceProjectionh44 := @distanceProjectionh37 p₀ distanceProjectionx38
    distanceProjectionx39 distanceProjectionx40 H initial distanceProjectionx41 ρold
    distanceProjectionx42 s G L hsing stepParameters distanceProjectionx43
  dsimp only at distanceProjectionh44 ⊢
  intro distanceProjectionx45 distanceProjectionx46 ε Λ P distanceProjectionx47 εc
    distanceProjectionx48 distanceProjectionx49 distanceProjectionx50 distanceProjectionx51
    distanceProjectionx52 distanceProjectionx53
  have distanceProjectionh54 := @distanceProjectionh44 distanceProjectionx45 distanceProjectionx46 ε
    Λ P distanceProjectionx47 εc distanceProjectionx48 distanceProjectionx49 distanceProjectionx50
    distanceProjectionx51 distanceProjectionx52 distanceProjectionx53
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, distanceProjectionh55⟩ :=
    distanceProjectionh54
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨distanceProjectionfield56, distanceProjectionfield57, distanceProjectionfield58,
    distanceProjectionfield59, distanceProjectionfield60, distanceProjectionfield61,
    distanceProjectionfield62, distanceProjectionfield63, distanceProjectionfield64,
    distanceProjectionfield65, distanceProjectionfield66, distanceProjectionfield67,
    distanceProjectionfield68, distanceProjectionfield69, distanceProjectionfield70,
    distanceProjectionfield71, distanceProjectionfield72, distanceProjectionfield73,
    distanceProjectionfield74, distanceProjectionfield75, distanceProjectionfield76,
    distanceProjectionfield77, distanceProjectionfield78, distanceProjectionfield79,
    distanceProjectionfield80, distanceProjectionfield81, distanceProjectionfield82,
    distanceProjectionfield83, distanceProjectionfield84, distanceProjectionfield85,
    distanceProjectionfield86, distanceProjectionfield87, distanceProjectionfield88,
    distanceProjectionh89⟩ := distanceProjectionh55
  refine ⟨distanceProjectionfield56, distanceProjectionfield57, distanceProjectionfield58,
    distanceProjectionfield59, distanceProjectionfield60, distanceProjectionfield61,
    distanceProjectionfield62, distanceProjectionfield63, distanceProjectionfield64,
    distanceProjectionfield65, distanceProjectionfield66, distanceProjectionfield67,
    distanceProjectionfield68, distanceProjectionfield69, distanceProjectionfield70,
    distanceProjectionfield71, distanceProjectionfield72, distanceProjectionfield73,
    distanceProjectionfield74, distanceProjectionfield75, distanceProjectionfield76,
    distanceProjectionfield77, distanceProjectionfield78, distanceProjectionfield79,
    distanceProjectionfield80, distanceProjectionfield81, distanceProjectionfield82,
    distanceProjectionfield83, distanceProjectionfield84, distanceProjectionfield85,
    distanceProjectionfield86, distanceProjectionfield87, distanceProjectionfield88, ?_⟩
  exact distanceProjectionh89.1

open OneStepIncoming in
/-- The same common scaffold supports every positive requested presentation
accuracy. This replays the actual radius selection and fine-neck construction;
all returned record data and the canonical-family callback are unchanged. -/
theorem exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates_with_distance_scalars :
    ∃ Cdist : ℝ≥0, 1 ≤ Cdist ∧
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ),
    (4 ≤ recenterConstant ∧ ∃ (A : ℝ) (hA : 0 < A),
      fixed = StaticCapScaffold.ofCollarLength A hA ∧
      StandardCap.StaticCollarAdmits.{0, 0, u} A hA) ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4) ∧
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
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) ∧
        (parameters.modelAccuracy ≤ 1 / 2 → standardCapL + 1 ≤ parameters.modelRadius →
          E.HasUniformDistanceScalar Cdist ∧
          (K.toHistory.event i).HasUniformDistanceScalar Cdist) := by
  obtain ⟨Cdist, hCdist, fixed, c, hc, εcoarse, hεcoarse, hfactory⟩ :=
    exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates_with_distance_scalars.{u}
  refine ⟨Cdist, hCdist, fixed, c, hc, ?_⟩
  intro P₀ g₀ η hη
  have hfactory := hfactory P₀ g₀
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
  refine ⟨min (min εcoarse eta) η, εbar, hεP, min_le_right _ _, hεbar,
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
    hrecord, hvol, hcap, hDistance⟩ :=
    hmake p₀ hpD hpm hpε H initial htime ρold hInv s G L hsing
      (stepParameters.withNeckRadius ρ hρ) hinit hderiv hfinal P
      ((min_le_left _ _).trans (min_le_left _ _)) hεcut
      (min_le_left _ _) (min_le_right _ _) (hfine ρ hρ P hfineP) le_rfl hfloor
  obtain ⟨Record, hRecordDelta, hRecordOrder, hRecordNeck, hRecordScale, hRecordWindows,
    hRecordCoordinates, hRecordDeep⟩ := hrecord
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
      hRecordCoordinates, hRecordDeep, hstdE, hstdK, ?_⟩, hvol, hcap, hDistance⟩
  intro hfixed hrecenter hmodelOrder hmodelAccuracy hηold hρold
  obtain ⟨Eappend, hOldAppend, hInitial, _, hK⟩ := happend
  apply RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq H K Eappend hOldAppend
    hInitial hK i hi hInv Record (hpFixed.trans hfixed.symm) (hpDnew.trans hpD.symm)
    (hpM.trans hmodelOrder.symm) (hpAcc.trans hmodelAccuracy.symm)
    (hpC.trans hrecenter.symm) (fun b => (hRecordWindows b).hasCanonicalWindow)
  · rw [hpδ]
    exact hδrecord.trans hηold
  · rw [hpρ]
    exact (hρle D.endTime (D.startTime_nonneg.trans D.startTime_lt_endTime.le)).trans hρold

open OneStepIncoming in
/-- Forget the distance certificate from the same producer result. -/
theorem exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
          (∀ b, (Record.static b).witness.HasRadialCoordinates) ∧
          Record.DeepNecks_C12X (5 / 4) ∧
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
  obtain ⟨_, _, distanceProjectionSource⟩ :=
    exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates_with_distance_scalars.{u}
  obtain ⟨fixed, recenterConstant, distanceProjectionh1⟩ := distanceProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨distanceProjectionfield2, distanceProjectionh3⟩ := distanceProjectionh1
  refine ⟨distanceProjectionfield2.1, ?_⟩
  intro P₀ g₀ η distanceProjectionx4
  have distanceProjectionh5 := @distanceProjectionh3 P₀ g₀ η distanceProjectionx4
  obtain ⟨εP, εbar, distanceProjectionh6⟩ := distanceProjectionh5
  refine ⟨εP, εbar, ?_⟩
  obtain ⟨distanceProjectionfield7, distanceProjectionfield8, distanceProjectionfield9,
    distanceProjectionfield10, distanceProjectionh11⟩ := distanceProjectionh6
  refine ⟨distanceProjectionfield7, distanceProjectionfield8, distanceProjectionfield9,
    distanceProjectionfield10, ?_⟩
  intro Dtrace Dbig r tol Ctime distanceProjectionx12 distanceProjectionx13 distanceProjectionx14
    distanceProjectionx15 distanceProjectionx16
  have distanceProjectionh17 := @distanceProjectionh11 Dtrace Dbig r tol Ctime distanceProjectionx12
    distanceProjectionx13 distanceProjectionx14 distanceProjectionx15 distanceProjectionx16
  obtain ⟨εold, δold, distanceProjectionh18⟩ := distanceProjectionh17
  refine ⟨εold, δold, ?_⟩
  obtain ⟨distanceProjectionfield19, distanceProjectionfield20, distanceProjectionh21⟩ :=
    distanceProjectionh18
  refine ⟨distanceProjectionfield19, distanceProjectionfield20, ?_⟩
  intro m accuracy distanceProjectionx22 ηrecord distanceProjectionx23
  have distanceProjectionh24 := @distanceProjectionh21 m accuracy distanceProjectionx22 ηrecord
    distanceProjectionx23
  obtain ⟨δ, εcut, distanceProjectionh25⟩ := distanceProjectionh24
  refine ⟨δ, εcut, ?_⟩
  obtain ⟨distanceProjectionfield26, distanceProjectionfield27, distanceProjectionfield28,
    distanceProjectionfield29, distanceProjectionfield30, distanceProjectionh31⟩ :=
    distanceProjectionh25
  refine ⟨distanceProjectionfield26, distanceProjectionfield27, distanceProjectionfield28,
    distanceProjectionfield29, distanceProjectionfield30, ?_⟩
  intro C1 C2 distanceProjectionx32
  have distanceProjectionh33 := @distanceProjectionh31 C1 C2 distanceProjectionx32
  obtain ⟨C, Λ, distanceProjectionh34⟩ := distanceProjectionh33
  refine ⟨C, Λ, ?_⟩
  obtain ⟨distanceProjectionfield35, distanceProjectionfield36, distanceProjectionh37⟩ :=
    distanceProjectionh34
  refine ⟨distanceProjectionfield35, distanceProjectionfield36, ?_⟩
  intro qcan originalCoreFloor protectedFloor Kfine distanceProjectionx38 distanceProjectionx39
    distanceProjectionx40 distanceProjectionx41
  have distanceProjectionh42 := @distanceProjectionh37 qcan originalCoreFloor protectedFloor Kfine
    distanceProjectionx38 distanceProjectionx39 distanceProjectionx40 distanceProjectionx41
  obtain ⟨Q, v, distanceProjectionh43⟩ := distanceProjectionh42
  refine ⟨Q, v, ?_⟩
  obtain ⟨distanceProjectionfield44, distanceProjectionfield45, distanceProjectionfield46,
    distanceProjectionh47⟩ := distanceProjectionh43
  refine ⟨distanceProjectionfield44, distanceProjectionfield45, distanceProjectionfield46, ?_⟩
  intro p₀ distanceProjectionx48 distanceProjectionx49 distanceProjectionx50 H initial
    distanceProjectionx51 ρold distanceProjectionx52 s G L hsing stepParameters
    distanceProjectionx53
  have distanceProjectionh54 := @distanceProjectionh47 p₀ distanceProjectionx48
    distanceProjectionx49 distanceProjectionx50 H initial distanceProjectionx51 ρold
    distanceProjectionx52 s G L hsing stepParameters distanceProjectionx53
  dsimp only at distanceProjectionh54 ⊢
  intro distanceProjectionx55 distanceProjectionx56 distanceProjectionx57 distanceProjectionx58
    distanceProjectionx59 distanceProjectionx60
  have distanceProjectionh61 := @distanceProjectionh54 distanceProjectionx55 distanceProjectionx56
    distanceProjectionx57 distanceProjectionx58 distanceProjectionx59 distanceProjectionx60
  obtain ⟨ρ, hρ, distanceProjectionh62⟩ := distanceProjectionh61
  refine ⟨ρ, hρ, ?_⟩
  obtain ⟨distanceProjectionfield63, distanceProjectionfield64, distanceProjectionfield65,
    distanceProjectionfield66, distanceProjectionfield67, distanceProjectionh68⟩ :=
    distanceProjectionh62
  refine ⟨distanceProjectionfield63, distanceProjectionfield64, distanceProjectionfield65,
    distanceProjectionfield66, distanceProjectionfield67, ?_⟩
  try dsimp only at distanceProjectionh68 ⊢
  obtain ⟨P, distanceProjectionh69⟩ := distanceProjectionh68
  refine ⟨P, ?_⟩
  obtain ⟨distanceProjectionfield70, distanceProjectionfield71, distanceProjectionfield72,
    distanceProjectionfield73, distanceProjectionfield74, distanceProjectionh75⟩ :=
    distanceProjectionh69
  refine ⟨distanceProjectionfield70, distanceProjectionfield71, distanceProjectionfield72,
    distanceProjectionfield73, distanceProjectionfield74, ?_⟩
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, distanceProjectionh76⟩ :=
    distanceProjectionh75
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨distanceProjectionfield77, distanceProjectionfield78, distanceProjectionfield79,
    distanceProjectionfield80, distanceProjectionfield81, distanceProjectionfield82,
    distanceProjectionfield83, distanceProjectionfield84, distanceProjectionfield85,
    distanceProjectionfield86, distanceProjectionfield87, distanceProjectionfield88,
    distanceProjectionfield89, distanceProjectionfield90, distanceProjectionfield91,
    distanceProjectionfield92, distanceProjectionfield93, distanceProjectionfield94,
    distanceProjectionfield95, distanceProjectionfield96, distanceProjectionfield97,
    distanceProjectionfield98, distanceProjectionfield99, distanceProjectionfield100,
    distanceProjectionfield101, distanceProjectionfield102, distanceProjectionfield103,
    distanceProjectionfield104, distanceProjectionfield105, distanceProjectionfield106,
    distanceProjectionfield107, distanceProjectionfield108, distanceProjectionfield109,
    distanceProjectionh110⟩ := distanceProjectionh76
  refine ⟨distanceProjectionfield77, distanceProjectionfield78, distanceProjectionfield79,
    distanceProjectionfield80, distanceProjectionfield81, distanceProjectionfield82,
    distanceProjectionfield83, distanceProjectionfield84, distanceProjectionfield85,
    distanceProjectionfield86, distanceProjectionfield87, distanceProjectionfield88,
    distanceProjectionfield89, distanceProjectionfield90, distanceProjectionfield91,
    distanceProjectionfield92, distanceProjectionfield93, distanceProjectionfield94,
    distanceProjectionfield95, distanceProjectionfield96, distanceProjectionfield97,
    distanceProjectionfield98, distanceProjectionfield99, distanceProjectionfield100,
    distanceProjectionfield101, distanceProjectionfield102, distanceProjectionfield103,
    distanceProjectionfield104, distanceProjectionfield105, distanceProjectionfield106,
    distanceProjectionfield107, distanceProjectionfield108, distanceProjectionfield109, ?_⟩
  exact distanceProjectionh110.1

/-- Forget the radial certificate from the same stronger producer result. -/
theorem exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∃ εcoarse : ℝ, 0 < εcoarse ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X)) ∧
        (∃ Kvol : Set D.slab.terminalRegularOpen, IsCompact Kvol ∧
          riemannianVolumeMeasure ThreeModel Qout.Carrier E.outputMetric univ + ENNReal.ofReal
            ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel D.slab.terminalRegularOpen D.terminal.metric Kvol) ∧
        (∀ q ∈ E.capRegion, Q / 4 ≤ metricScalarAt E.outputMetric q) := by
  have radialProjectionSource :=
    exists_uniform_horn_cutoff_record_with_volume_debit_of_fineCutNecks_with_radial_coordinates.{u}
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  obtain ⟨εcoarse, radialProjectionh4⟩ := radialProjectionh3
  refine ⟨εcoarse, ?_⟩
  obtain ⟨radialProjectionfield5, radialProjectionh6⟩ := radialProjectionh4
  refine ⟨radialProjectionfield5, ?_⟩
  intro P₀ g₀ Dtrace Dbig r tol Ctime radialProjectionx7 radialProjectionx8 radialProjectionx9
    radialProjectionx10 radialProjectionx11
  have radialProjectionh12 := @radialProjectionh6 P₀ g₀ Dtrace Dbig r tol Ctime radialProjectionx7
    radialProjectionx8 radialProjectionx9 radialProjectionx10 radialProjectionx11
  obtain ⟨εold, δold, radialProjectionh13⟩ := radialProjectionh12
  refine ⟨εold, δold, ?_⟩
  obtain ⟨radialProjectionfield14, radialProjectionfield15, radialProjectionh16⟩ :=
    radialProjectionh13
  refine ⟨radialProjectionfield14, radialProjectionfield15, ?_⟩
  intro m accuracy radialProjectionx17 ηrecord radialProjectionx18
  have radialProjectionh19 := @radialProjectionh16 m accuracy radialProjectionx17 ηrecord
    radialProjectionx18
  obtain ⟨δ, ε₀, Λq, radialProjectionh20⟩ := radialProjectionh19
  refine ⟨δ, ε₀, Λq, ?_⟩
  obtain ⟨radialProjectionfield21, radialProjectionfield22, radialProjectionfield23,
    radialProjectionfield24, radialProjectionfield25, radialProjectionh26⟩ := radialProjectionh20
  refine ⟨radialProjectionfield21, radialProjectionfield22, radialProjectionfield23,
    radialProjectionfield24, radialProjectionfield25, ?_⟩
  intro q0 radialProjectionx27 Λmax coreFloor radialProjectionx28 radialProjectionx29 Qlower
  have radialProjectionh30 := @radialProjectionh26 q0 radialProjectionx27 Λmax coreFloor
    radialProjectionx28 radialProjectionx29 Qlower
  obtain ⟨Q, v, radialProjectionh31⟩ := radialProjectionh30
  refine ⟨Q, v, ?_⟩
  obtain ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, radialProjectionh37⟩ := radialProjectionh31
  refine ⟨radialProjectionfield32, radialProjectionfield33, radialProjectionfield34,
    radialProjectionfield35, radialProjectionfield36, ?_⟩
  intro p₀ radialProjectionx38 radialProjectionx39 radialProjectionx40 H initial radialProjectionx41
    ρold radialProjectionx42 s G L hsing stepParameters radialProjectionx43
  have radialProjectionh44 := @radialProjectionh37 p₀ radialProjectionx38 radialProjectionx39
    radialProjectionx40 H initial radialProjectionx41 ρold radialProjectionx42 s G L hsing
    stepParameters radialProjectionx43
  dsimp only at radialProjectionh44 ⊢
  intro radialProjectionx45 radialProjectionx46 ε Λ P radialProjectionx47 εc radialProjectionx48
    radialProjectionx49 radialProjectionx50 radialProjectionx51 radialProjectionx52
    radialProjectionx53
  have radialProjectionh54 := @radialProjectionh44 radialProjectionx45 radialProjectionx46 ε Λ P
    radialProjectionx47 εc radialProjectionx48 radialProjectionx49 radialProjectionx50
    radialProjectionx51 radialProjectionx52 radialProjectionx53
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, radialProjectionh55⟩ :=
    radialProjectionh54
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionfield63, radialProjectionfield64,
    radialProjectionfield65, radialProjectionfield66, radialProjectionfield67,
    radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, radialProjectionfield72, radialProjectionfield73,
    radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionh87⟩ := radialProjectionh55
  refine ⟨radialProjectionfield56, radialProjectionfield57, radialProjectionfield58,
    radialProjectionfield59, radialProjectionfield60, radialProjectionfield61,
    radialProjectionfield62, radialProjectionfield63, radialProjectionfield64,
    radialProjectionfield65, radialProjectionfield66, radialProjectionfield67,
    radialProjectionfield68, radialProjectionfield69, radialProjectionfield70,
    radialProjectionfield71, radialProjectionfield72, radialProjectionfield73,
    radialProjectionfield74, radialProjectionfield75, radialProjectionfield76,
    radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, ?_⟩
  refine ⟨?_, radialProjectionh87.2⟩
  have radialProjectionh88 := radialProjectionh87.1
  obtain ⟨Record, radialProjectionh89⟩ := radialProjectionh88
  refine ⟨Record, ?_⟩
  obtain ⟨radialProjectionfield90, radialProjectionfield91, radialProjectionfield92,
    radialProjectionfield93, radialProjectionh94⟩ := radialProjectionh89
  refine ⟨radialProjectionfield90, radialProjectionfield91, radialProjectionfield92,
    radialProjectionfield93, ?_⟩
  exact radialProjectionh94.1


open OneStepIncoming in
/-- Forget the radial certificate from the same stronger producer result. -/
theorem exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le :
    ∃ (fixed : StaticCapScaffold) (recenterConstant : ℝ), 4 ≤ recenterConstant ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (η : ℝ), 0 < η →
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
          (∀ b, (Record.static b).hasLinkedCanonicalWindow_C12X) ∧
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
  have radialProjectionSource :=
    exists_uniform_horn_cutoff_record_of_fineCutNecks_of_le_with_radial_coordinates.{u}
  obtain ⟨fixed, recenterConstant, radialProjectionh1⟩ := radialProjectionSource
  refine ⟨fixed, recenterConstant, ?_⟩
  obtain ⟨radialProjectionfield2, radialProjectionh3⟩ := radialProjectionh1
  refine ⟨radialProjectionfield2, ?_⟩
  intro P₀ g₀ η radialProjectionx4
  have radialProjectionh5 := @radialProjectionh3 P₀ g₀ η radialProjectionx4
  obtain ⟨εP, εbar, radialProjectionh6⟩ := radialProjectionh5
  refine ⟨εP, εbar, ?_⟩
  obtain ⟨radialProjectionfield7, radialProjectionfield8, radialProjectionfield9,
    radialProjectionfield10, radialProjectionh11⟩ := radialProjectionh6
  refine ⟨radialProjectionfield7, radialProjectionfield8, radialProjectionfield9,
    radialProjectionfield10, ?_⟩
  intro Dtrace Dbig r tol Ctime radialProjectionx12 radialProjectionx13 radialProjectionx14
    radialProjectionx15 radialProjectionx16
  have radialProjectionh17 := @radialProjectionh11 Dtrace Dbig r tol Ctime radialProjectionx12
    radialProjectionx13 radialProjectionx14 radialProjectionx15 radialProjectionx16
  obtain ⟨εold, δold, radialProjectionh18⟩ := radialProjectionh17
  refine ⟨εold, δold, ?_⟩
  obtain ⟨radialProjectionfield19, radialProjectionfield20, radialProjectionh21⟩ :=
    radialProjectionh18
  refine ⟨radialProjectionfield19, radialProjectionfield20, ?_⟩
  intro m accuracy radialProjectionx22 ηrecord radialProjectionx23
  have radialProjectionh24 := @radialProjectionh21 m accuracy radialProjectionx22 ηrecord
    radialProjectionx23
  obtain ⟨δ, εcut, radialProjectionh25⟩ := radialProjectionh24
  refine ⟨δ, εcut, ?_⟩
  obtain ⟨radialProjectionfield26, radialProjectionfield27, radialProjectionfield28,
    radialProjectionfield29, radialProjectionfield30, radialProjectionh31⟩ := radialProjectionh25
  refine ⟨radialProjectionfield26, radialProjectionfield27, radialProjectionfield28,
    radialProjectionfield29, radialProjectionfield30, ?_⟩
  intro C1 C2 radialProjectionx32
  have radialProjectionh33 := @radialProjectionh31 C1 C2 radialProjectionx32
  obtain ⟨C, Λ, radialProjectionh34⟩ := radialProjectionh33
  refine ⟨C, Λ, ?_⟩
  obtain ⟨radialProjectionfield35, radialProjectionfield36, radialProjectionh37⟩ :=
    radialProjectionh34
  refine ⟨radialProjectionfield35, radialProjectionfield36, ?_⟩
  intro qcan originalCoreFloor protectedFloor Kfine radialProjectionx38 radialProjectionx39
    radialProjectionx40 radialProjectionx41
  have radialProjectionh42 := @radialProjectionh37 qcan originalCoreFloor protectedFloor Kfine
    radialProjectionx38 radialProjectionx39 radialProjectionx40 radialProjectionx41
  obtain ⟨Q, v, radialProjectionh43⟩ := radialProjectionh42
  refine ⟨Q, v, ?_⟩
  obtain ⟨radialProjectionfield44, radialProjectionfield45, radialProjectionfield46,
    radialProjectionh47⟩ := radialProjectionh43
  refine ⟨radialProjectionfield44, radialProjectionfield45, radialProjectionfield46, ?_⟩
  intro p₀ radialProjectionx48 radialProjectionx49 radialProjectionx50 H initial radialProjectionx51
    ρold radialProjectionx52 s G L hsing stepParameters radialProjectionx53
  have radialProjectionh54 := @radialProjectionh47 p₀ radialProjectionx48 radialProjectionx49
    radialProjectionx50 H initial radialProjectionx51 ρold radialProjectionx52 s G L hsing
    stepParameters radialProjectionx53
  dsimp only at radialProjectionh54 ⊢
  intro radialProjectionx55 radialProjectionx56 radialProjectionx57 radialProjectionx58
    radialProjectionx59 radialProjectionx60
  have radialProjectionh61 := @radialProjectionh54 radialProjectionx55 radialProjectionx56
    radialProjectionx57 radialProjectionx58 radialProjectionx59 radialProjectionx60
  obtain ⟨ρ, hρ, radialProjectionh62⟩ := radialProjectionh61
  refine ⟨ρ, hρ, ?_⟩
  obtain ⟨radialProjectionfield63, radialProjectionfield64, radialProjectionfield65,
    radialProjectionfield66, radialProjectionfield67, radialProjectionh68⟩ := radialProjectionh62
  refine ⟨radialProjectionfield63, radialProjectionfield64, radialProjectionfield65,
    radialProjectionfield66, radialProjectionfield67, ?_⟩
  try dsimp only at radialProjectionh68 ⊢
  obtain ⟨P, radialProjectionh69⟩ := radialProjectionh68
  refine ⟨P, ?_⟩
  obtain ⟨radialProjectionfield70, radialProjectionfield71, radialProjectionfield72,
    radialProjectionfield73, radialProjectionfield74, radialProjectionh75⟩ := radialProjectionh69
  refine ⟨radialProjectionfield70, radialProjectionfield71, radialProjectionfield72,
    radialProjectionfield73, radialProjectionfield74, ?_⟩
  obtain ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, radialProjectionh76⟩ :=
    radialProjectionh75
  refine ⟨Qout, E, hOld, K, initialK, i, parameters, n, δOriginal, kOriginal, NOriginal, hδOriginal,
    rotation, hmark, side, horder, hδ1, Nrecord, eOriginal, ?_⟩
  obtain ⟨radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionfield87, radialProjectionfield88,
    radialProjectionfield89, radialProjectionfield90, radialProjectionfield91,
    radialProjectionfield92, radialProjectionfield93, radialProjectionfield94,
    radialProjectionfield95, radialProjectionfield96, radialProjectionfield97,
    radialProjectionfield98, radialProjectionfield99, radialProjectionfield100,
    radialProjectionfield101, radialProjectionfield102, radialProjectionfield103,
    radialProjectionfield104, radialProjectionfield105, radialProjectionfield106,
    radialProjectionfield107, radialProjectionh108⟩ := radialProjectionh76
  refine ⟨radialProjectionfield77, radialProjectionfield78, radialProjectionfield79,
    radialProjectionfield80, radialProjectionfield81, radialProjectionfield82,
    radialProjectionfield83, radialProjectionfield84, radialProjectionfield85,
    radialProjectionfield86, radialProjectionfield87, radialProjectionfield88,
    radialProjectionfield89, radialProjectionfield90, radialProjectionfield91,
    radialProjectionfield92, radialProjectionfield93, radialProjectionfield94,
    radialProjectionfield95, radialProjectionfield96, radialProjectionfield97,
    radialProjectionfield98, radialProjectionfield99, radialProjectionfield100,
    radialProjectionfield101, radialProjectionfield102, radialProjectionfield103,
    radialProjectionfield104, radialProjectionfield105, radialProjectionfield106,
    radialProjectionfield107, ?_⟩
  refine ⟨?_, radialProjectionh108.2⟩
  have radialProjectionh109 := radialProjectionh108.1
  obtain ⟨Record, radialProjectionh110⟩ := radialProjectionh109
  refine ⟨Record, ?_⟩
  obtain ⟨radialProjectionfield111, radialProjectionfield112, radialProjectionfield113,
    radialProjectionfield114, radialProjectionfield115, radialProjectionh116⟩ :=
    radialProjectionh110
  refine ⟨radialProjectionfield111, radialProjectionfield112, radialProjectionfield113,
    radialProjectionfield114, radialProjectionfield115, ?_⟩
  exact radialProjectionh116.2.2


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
