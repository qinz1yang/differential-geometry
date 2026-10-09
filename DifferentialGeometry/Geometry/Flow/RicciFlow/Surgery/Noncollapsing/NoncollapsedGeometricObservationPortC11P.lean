import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.RegularObservationNoncollapse

/-!
# S-CH11-FIX8 port of astra `NoncollapsedGeometricObservation`（`PortC11P`）

来源：donor `NoncollapsedGeometricObservation.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败（2 个 error）。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `hδnew` / `hρnew`：`simpa only [htime] using hδ (Fin.last H.eventCount)` 的 simp 之后两个类型只差
  `htime` 的改写位置；`rw [htime] at h` 又找不到模式（`h` 里 appendEvent 的证明项与 `htime` 不同形）。
  改为先把 `h` 用 `have h' : <显式类型> := h`（defeq 转型）再 `rw [htime] at h'; exact h'`。
* 一处陈述里未引用的 binder `(A : InitialIdentification P g H.toHistory)`（`∀ (H …)` 内）改成 `_A`
  （alpha-重命名，同一命题；消 unused-variable warning）。

原路径 `NoncollapsedGeometricObservation` 是只 import 本文件的 re-export shim。
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

open private observation_initial_budget_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricObservationExtension

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem joint_observation_step
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B)
    (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ)
    (hδcut : 0 < δcut) (hρcut : 0 < ρcut) (hεcut : 0 < εcut) (hDcut : 0 < Dcut) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound v ε κR : ℝ),
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < v ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κR ∧
      (∀ (H : RetainedCoreHistory.{u}) (_A : InitialIdentification P g H.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        H.NoncollapsedBefore κR ε H.horizon) ∧
      ∀ (H : RetainedCoreHistory.{u})
        (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
        (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        H.horizon < B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound old →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
              H.initialMetric (Fin.last H.eventCount))
            (A' : InitialIdentification P g (H.appendEvent E.incoming.lt E hinit).toHistory)
            (q : CutoffParameters)
            (new : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q)
            (records : ∀ i : Fin (H.appendEvent E.incoming.lt E hinit).eventCount,
              GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory i
                (p.spliceAfter q H.horizon)),
            E.incoming = G ∧ H.horizon < s ∧ A.IsPrefixOf A' ∧
            (q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
              q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
              q.recenterConstant = p₀.recenterConstant) ∧
            q.delta s ≤ δbound ∧ q.neckRadius s ≤ ρbound ∧
            (∀ b, (new.static b).hasCanonicalWindow) ∧
            (H.appendEvent E.incoming.lt E hinit).IsCanonicalCutoffRecordFamily
              p₀ δbound ρbound records ∧
            (∀ i : Fin H.eventCount,
              HEq (records i.castSucc).nominalRadius (old i).nominalRadius ∧
              HEq (records i.castSucc).delta (old i).delta ∧
              HEq (records i.castSucc).order (old i).order ∧
              HEq (records i.castSucc).neck (old i).neck ∧
              HEq (records i.castSucc).static (old i).static) ∧
            HEq (records (Fin.last H.eventCount)).nominalRadius new.nominalRadius ∧
            HEq (records (Fin.last H.eventCount)).delta new.delta ∧
            HEq (records (Fin.last H.eventCount)).order new.order ∧
            HEq (records (Fin.last H.eventCount)).neck new.neck ∧
            HEq (records (Fin.last H.eventCount)).static new.static ∧
            E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F := by
  obtain ⟨εcanbar, hεcanbar, hcn⟩ := general_strong_canonical P g
  obtain ⟨εregbar, hεregbar, hregular⟩ := exists_regular_observation_noncollapsed P g
  let εbar : ℝ := min εcanbar εregbar
  have hεbar : 0 < εbar := lt_min hεcanbar hεregbar
  obtain ⟨Λ, hΛ, hstepB⟩ := uniform_debit_surgery_step P g B εbar hB hεbar
  obtain ⟨_, _, _, _, q₀, _, δ₀, ρ₀, ε₀, D₀, m₀, Ctime, _, _, _, -, -, -, -, hq₀, -, hδ₀, hρ₀,
    hε₀, _, -, -, hcl₀⟩ := hcn B (min (1 / 22) εbar) Λ hB (lt_min (by norm_num) hεbar)
      ((min_le_left _ _).trans_lt (by norm_num))
      ((min_le_right _ _).trans (min_le_left _ _)) hΛ
  obtain ⟨ε, hε, hε', hεbarε, hstepε⟩ := hstepB Ctime
  obtain ⟨C1, C2, C1s, C2s, q₁, τmin, δ₁, ρ₁, ε₁, D₁, m₁, _, Cgrad, κ, a₀, hC1, hC2, hC1s, hC2s,
    -, hτ, hδ₁, hρ₁, hε₁, -, hκ, ha₀, hcl₁⟩ := hcn B ε Λ hB hε hε'
      (hεbarε.trans (min_le_left _ _)) hΛ
  obtain ⟨δR, ρR, εR, DR, mR, κR, hδR, hρR, hεR, _, hκR, hNCR⟩ :=
    hregular (B + 1) ε Λ (by linarith) hε hε'
      (hεbarε.trans (min_le_right _ _)) hΛ
  obtain ⟨p₀, δbound, ρbound, v, hacc, hD, hm, hδbound, hδle, hρbound, hρle, hΛle, hv, hnext⟩ :=
    hstepε C1 C2 C1s C2s (max q₀ q₁) τmin
      (min (min (min δ₀ δ₁) δR) (min δcut (2 * Λ)⁻¹))
      (min (min (min ρ₀ ρ₁) ρR) ρcut) (min (min (min ε₀ ε₁) εR) εcut)
      (max (max (max D₀ D₁) DR) Dcut) (max (max (max m₀ m₁) mR) mcut) Cgrad κ a₀
      hC1 hC2 hC1s hC2s (lt_max_of_lt_left hq₀) hτ
      (lt_min (lt_min (lt_min hδ₀ hδ₁) hδR) (lt_min hδcut (by positivity)))
      (lt_min (lt_min (lt_min hρ₀ hρ₁) hρR) hρcut)
      (lt_min (lt_min (lt_min hε₀ hε₁) hεR) hεcut) (lt_max_of_lt_right hDcut) hκ ha₀
  obtain ⟨hacc, haccRequest⟩ := le_min_iff.mp hacc
  obtain ⟨hD, hDRequest⟩ := max_le_iff.mp hD
  obtain ⟨hm, hmRequest⟩ := max_le_iff.mp hm
  obtain ⟨hδle, hδRequest⟩ := le_min_iff.mp hδle
  obtain ⟨hρle, hρRequest⟩ := le_min_iff.mp hρle
  obtain ⟨hδRequest, hδΛ⟩ := le_min_iff.mp hδRequest
  have hrec : p₀.recenterConstant * δbound ≤ 1 / 2 := by
    have hprod : δbound * (2 * Λ) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 2 * Λ)).mp (by simpa only [one_div] using hδΛ)
    have hle := mul_le_mul_of_nonneg_right hΛle hδbound.le
    nlinarith
  obtain ⟨hacc, haccR⟩ := le_min_iff.mp hacc
  obtain ⟨hD, hDR⟩ := max_le_iff.mp hD
  obtain ⟨hm, hmR⟩ := max_le_iff.mp hm
  obtain ⟨hδle, hδRle⟩ := le_min_iff.mp hδle
  obtain ⟨hρle, hρRle⟩ := le_min_iff.mp hρle
  rw [le_min_iff] at hacc hδle hρle
  rw [max_le_iff] at hD hm
  have hnoncollapse : ∀ (H : RetainedCoreHistory.{u})
      (A : InitialIdentification P g H.toHistory) (p : CutoffParameters)
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.horizon ≤ B → H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.NoncollapsedBefore κR ε H.horizon := by
    intro H A p records hHB hfamily
    exact hNCR p₀ δbound ρbound haccR hDR hmR hδRle hρRle hΛle
      H A p records (by linarith) hfamily
  refine ⟨p₀, δbound, ρbound, v, ε, κR, haccRequest, hDRequest, hmRequest,
    hδRequest, hρRequest, hrec, hδbound, hρbound, hv, hε, hε', hκR,
    hnoncollapse, ?_⟩
  intro H A p old hhor hold s G hs hinit hsing
  let J := H.prefixAt (Fin.last H.eventCount)
  let initial : InitialIdentification P g J.toHistory := A.ofStageZero rfl HEq.rfl
  have hJhor : J.horizon < B := H.time_le_horizon.trans_lt hhor
  have hInv : J.hasCanonicalCutoffRecords p₀ δbound ρbound :=
    (J.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mpr
      ⟨p, H.prefixRecords (Fin.last H.eventCount) old,
        H.isCanonicalCutoffRecordFamily_prefixAt (Fin.last H.eventCount) hold⟩
  obtain ⟨hderiv, -, -, -, -, -, hslab₀⟩ :=
    hcl₀ p₀ δbound ρbound hacc.1 hD.1 hm.1 hδle.1 hρle.1 hΛle J initial rfl hJhor hInv
  obtain ⟨-, hgrad, hcan, hspat, hpinch, hnc, hslab₁⟩ :=
    hcl₁ p₀ δbound ρbound hacc.2 hD.2 hm.2 hδle.2 hρle.2 hΛle J initial rfl hJhor hInv
  obtain ⟨hderivG, -⟩ := hslab₀ s G hs hinit hsing
  obtain ⟨-, hgradG, hcanG, hspatG, hncG⟩ := hslab₁ s G hs hinit hsing
  obtain ⟨Q, E, hinitE, _, hEG, hInvK, -, -, -, -, -, -, hbfr, hctrl, hdebit⟩ :=
    hnext J initial rfl hJhor hInv
      (fun j y t ht hR => hderiv j y t ht ((le_max_left _ _).trans_lt hR))
      (fun j => (J.toHistory.event j).incoming.gradientBoundBefore_of_threshold_le
        (le_max_right _ _) (hgrad j))
      (fun j => (J.toHistory.event j).incoming.canonicalBefore_of_threshold_le
        (le_max_right _ _) (hcan j))
      (fun j => (J.toHistory.event j).incoming.spatiallyCanonicalBefore_of_threshold_le
        (le_max_right _ _) (hspat j))
      hpinch hnc s G hs hinit hsing
      (fun y t ht hR => hderivG y t ht ((le_max_left _ _).trans_lt hR))
      (G.gradientBoundBefore_of_threshold_le (le_max_right _ _) hgradG)
      (fun y t ht hR hτ => hcanG y t ht ((le_max_right _ _).trans_lt hR) hτ)
      (G.spatiallyCanonicalBefore_of_threshold_le (le_max_right _ _) hspatG) hncG
  change (H.appendEvent E.incoming.lt E hinitE).hasCanonicalCutoffRecords
    p₀ δbound ρbound at hInvK
  obtain ⟨q, hqf, hqD, hqm, hqε, hqc, fine, hwin, hδ, hρ⟩ := hInvK
  let new : GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinitE).toHistory
      (Fin.last H.eventCount) q := fine (Fin.last H.eventCount)
  have hwinNew : ∀ b, (new.static b).hasCanonicalWindow := hwin (Fin.last H.eventCount)
  have htime : (H.appendEvent E.incoming.lt E hinitE).time
      (Fin.last H.eventCount).succ = s := H.appendEvent_time_last E.incoming.lt E hinitE
  have hδnew : q.delta s ≤ δbound := by
    have h : q.delta ((H.appendEvent E.incoming.lt E hinitE).time
        (Fin.last H.eventCount).succ) ≤ δbound := hδ (Fin.last H.eventCount)
    rw [htime] at h
    exact h
  have hρnew : q.neckRadius s ≤ ρbound := by
    have h : q.neckRadius ((H.appendEvent E.incoming.lt E hinitE).time
        (Fin.last H.eventCount).succ) ≤ ρbound := hρ (Fin.last H.eventCount)
    rw [htime] at h
    exact h
  have hsingE : E.incoming.SingularEndpoint := hEG.symm ▸ hsing
  have hfuture : H.horizon < s := actual_singular_event_after_horizon H E hinitE hsingE
  obtain ⟨A', hA⟩ := marked_singular_event_extension H A E hinitE hsingE
  obtain ⟨records, hfamily, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck, hNewStatic⟩ :=
    H.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter E.incoming.lt E hinitE
      hfuture old hold new ⟨hqf, hqD, hqm, hqε, hqc⟩ hwinNew hδnew hρnew
  exact ⟨Q, E, hinitE, A', q, new, records, hEG, hfuture, hA, ⟨hqf, hqD, hqm, hqε, hqc⟩,
    hδnew, hρnew, hwinNew, hfamily, hOld, hNewNominal, hNewDelta, hNewOrder, hNewNeck,
    hNewStatic, hbfr, hctrl, hdebit⟩

/-- Construct a fresh observation meeting prescribed positive cutoff and model
quality budgets. The same selected family supplies noncollapse through the
closed endpoint. All requested bounds precede the parameters and volume debit. -/
theorem exists_noncollapsed_geometric_observation_with_quality
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B)
    (δcut ρcut εcut Dcut : ℝ) (mcut : ℕ)
    (hδcut : 0 < δcut) (hρcut : 0 < ρcut) (hεcut : 0 < εcut) (hDcut : 0 < Dcut) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      p₀.modelAccuracy ≤ εcut ∧ Dcut ≤ p₀.modelRadius ∧ mcut ≤ p₀.modelOrder ∧
      δbound ≤ δcut ∧ ρbound ≤ ρcut ∧ p₀.recenterConstant * δbound ≤ 1 / 2 ∧
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  classical
  obtain ⟨p₀, δbound, ρbound, v, ε, κ, hacc, hD, hm, hδRequest, hρRequest, hrec,
    hδ, hρ, hv, hε, hε', hκ, hnc, step⟩ :=
    joint_observation_step P g B hB δcut ρcut εcut Dcut mcut hδcut hρcut hεcut hDcut
  obtain ⟨a, ha, hfixed, hlower⟩ :=
    exists_pos_inFixedHamiltonIveyRegion_and_scalar_lower_bound g
  refine ⟨p₀, δbound, ρbound, ε, κ, v, hacc, hD, hm, hδRequest, hρRequest, hrec,
    hδ, hρ, hε, hε', hκ, hv, ?_⟩
  let H₀ := RetainedCoreHistory.atZero P g
  let A₀ := InitialIdentification.atZero P g
  let S : Set (RetainedCoreHistory.{u}) := {K | K.horizon ≤ B ∧
    ∃ (A : InitialIdentification P g K.toHistory), A₀.IsPrefixOf A ∧
    ∃ (p : CutoffParameters)
      (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
      HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
      ∀ i : Fin K.eventCount,
        ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
              (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F}
  have hzero : H₀ ∈ S := by
    refine ⟨hB.le, A₀, InitialIdentification.IsPrefixOf.refl A₀, p₀,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), ?_, (fun i => Fin.elim0 i)⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hprefix : ∀ K ∈ S, H₀.toHistory.IsPrefixOf K.toHistory := by
    rintro K ⟨_, A, hA, _⟩
    exact hA.1
  let budget : ℝ := Nat.card (ConnectedComponents (H₀.stage 0).Carrier) +
    2 * (Real.exp ((3 / a) * B) *
      (riemannianVolumeMeasure ThreeModel (H₀.stage 0).Carrier
        (H₀.initialMetric 0) univ).toReal / v)
  have hcount : ∀ K ∈ S, K.eventCount ≤ ⌈budget⌉₊ := by
    intro K hK
    obtain ⟨hKB, A, hA, p, records, _, _, hdebit⟩ := hK
    obtain ⟨hfixedK, hlowerK⟩ := A.fixedHamiltonIveyRegion_and_scalar_lower_bound hfixed hlower
    have hb := K.toHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
      records ha hfixedK hlowerK hv hKB hdebit
    rw [observation_initial_budget_eq hA.1 v (3 / a) B] at hb
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
    obtain ⟨_, A, hA, p, records, hcontrol, hclass, hdebit⟩ := hK
    obtain ⟨Q, E, hi, A', q, _, records', hEG, _, hAA', _, _, _, _, hclass',
      _, _, _, _, _, _, hbfr, hdiscard, hdebitE⟩ :=
      step K A p records hKB hclass s G hs hG hsing
    have hcontrolE : SurgeryEventControl E := ⟨hEG.symm ▸ hsing, hbfr, hdiscard⟩
    refine ⟨Q, E, hi, hEG, hs, A', hA.trans hAA', p.spliceAfter q K.horizon, records',
      history_control_append K hcontrol E hi hcontrolE, hclass', ?_⟩
    exact K.appendEvent_compact_volume_debit E.incoming.lt E hi v hdebit hdebitE
  obtain ⟨J, hJ, heq | hclosed⟩ :=
    H₀.exists_closedSlab_extension_of_eventCount_bounded S hzero hprefix
      (fun K hK => hK.1) hcount hproduce
  · obtain ⟨hJB, A, hA, p, records, hcontrol, hclass, hdebit⟩ := hJ
    have hncJ := hnc J A p records hJB hclass
    rw [heq] at hncJ
    exact ⟨J, A, p, records, heq, hA, hcontrol, hclass, hncJ, hdebit⟩
  · obtain ⟨hJB, G, hG, _⟩ := hclosed
    obtain ⟨_, A, hA, p, records, hcontrol, hclass, hdebit⟩ := hJ
    obtain ⟨A', hAA'⟩ := marked_closed_extension J A hJB G hG
    let K := J.extendHorizon B hJB G hG
    let records' : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p :=
      fun i => GeometricCutoffRecord.extendHorizon B hJB G hG (records i)
    have hclass' : K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records' := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hclass
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨K, A', p, records', rfl, hA.trans hAA',
      history_control_extend J hcontrol hJB G hG, hclass',
      hnc K A' p records' le_rfl hclass', hdebit⟩

/-- Construct one actual finite observation with its selected canonical cutoff
family, event control, compact volume debits and closed-endpoint noncollapse. -/
theorem exists_noncollapsed_geometric_observation
    (P : OrientedThreeStage.{u}) (g : P.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ (p₀ : CutoffParameters) (δbound ρbound ε κ v : ℝ),
      0 < δbound ∧ 0 < ρbound ∧ 0 < ε ∧ ε < 1 / 11 ∧ 0 < κ ∧ 0 < v ∧
      ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
        (p : CutoffParameters)
        (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p),
        K.horizon = B ∧ (InitialIdentification.atZero P g).IsPrefixOf A ∧
        HistoryEventControl K ∧ K.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records ∧
        K.NoncollapsedBefore κ ε B ∧
        ∀ i : Fin K.eventCount,
          ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
            riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
                (K.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
            riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
              (K.coreEvent i).terminal.metric F := by
  obtain ⟨p₀, δbound, ρbound, ε, κ, v, _, _, _, _, _, _,
    hδ, hρ, hε, hε', hκ, hv, hK⟩ :=
    exists_noncollapsed_geometric_observation_with_quality P g B hB
      1 1 1 1 0 one_pos one_pos one_pos one_pos
  exact ⟨p₀, δbound, ρbound, ε, κ, v, hδ, hρ, hε, hε', hκ, hv, hK⟩

end GC.GeneralFlow
