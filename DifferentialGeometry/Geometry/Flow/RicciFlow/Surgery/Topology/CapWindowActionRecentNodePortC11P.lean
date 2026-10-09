import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowActionC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

/-!
# S-CH11-FIX8 port of astra `CapWindowActionRecentNode`（`PortC11P`）

来源：donor `CapWindowActionRecentNode.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration / parse 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered）：
* 主定理的 `open … in` 与 docstring 的顺序对调（docstring 不能放在 `open … in` 前面）；
* 补 `import …CapWindowActionC11X`：它用的
  `exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall_…`
  （`…_with_window_scale_bound`）在本树是 EXT2 的 extension；
* `obtain … := hcanonical` 会清掉 `hcanonical`（下一行还要用）：改 `:= id hcanonical`。

原路径 `CapWindowActionRecentNode` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

open DifferentialGeometry.Tensor0SBundle in
/-- Fine quality is requested only for the actual cap at this node; later
accuracy and derivative control are used only from its birth to the query.
The selected prepared witness is evaluated in the original birth postmetric. -/
theorem exists_uniform_cap_window_exclusion_of_raw_cap_requests_with_window_scale_bound
    (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ εreq ≤ 1 / 2 ∧ 0 < Rreq ∧ Rbirth < Rreq ∧
      4 ≤ mreq ∧ 0 < δreq ∧
      (∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (event : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ},
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq →
        ∀ {b : event.RetainedBoundaryIndex}
          (raw : event.PresentedStaticCap fixed Dbig m ζ b), raw.hasCanonicalWindow →
          ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → ∀ ell : ℝ,
            ell ^ 4 * normSq0S event.outputMetric (raw.window x) 4
              (metricRm04At event.outputMetric (raw.window x)) ≤ 1 →
            raw.neck.scale * ell ^ 2 ≤ 18) ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth} := by
  classical
  obtain ⟨theta, r, qmin, Cbirth, _htheta, hr, _hqmin, hCbirth, hprepared⟩ :=
    exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall_with_window_scale_bound.{u, 0, 0, u}
      Aact (3 / a₀) E rTerm Cderiv (by positivity) hE hrTerm
  obtain ⟨D, hD, hDroom, R, hDR, m₀, hm₀, ζ₀, δevolve,
      hζ₀, hζhalf, hδevolve, hprepared⟩ :=
    hprepared (I := ThreeModel) Rbirth
  let K : ℝ := max 1 (max qmin (max (qDeriv / Cbirth) (1 / a₀)))
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨δscale, hδscale, hscale⟩ :=
    exists_uniform_static_cap_scale_lower_bound.{u} c ρ K hc hρ hK
  have hRbirthR : Rbirth < R := by
    have hgap := le_max_right (1 : ℝ) (Rbirth + r)
    linarith
  refine ⟨ζ₀, R, m₀, min δevolve δscale, hζ₀, hζhalf,
    (StandardCap.transitionEnd_pos.trans_le hRbirth).trans hRbirthR,
    hRbirthR, hm₀, lt_min hδevolve hδscale, ?_, ?_⟩
  · intro P Q a s event fixed Dbig ζ m hRadius hm hζ b raw hcanonical x hx ell hRm
    obtain ⟨x₀, δ, k, datum, w, _hscalarScale, hmetric, _hcapWindow⟩ := hcanonical
    exact (hprepared w hRadius hm hζ).1 Q event.outputMetric raw.window
      raw.window_smooth raw.neck.scale raw.neck.scale_pos hmetric x hx ell hRm
  intro H parameters records hfixed hscalarInitial t first hle v hv hvE hpast
    pole hball gamma hC1 hInt hterminal hnode hsmall i hf hl hstart hpc hδ hρp
    hlater hderiv b Dbig ζ m S hRadius hm hζ hcanonical hscaleEq
  rintro ⟨xPast, hxPast, hwindowPoint⟩
  have hbirth : H.time i.succ ≤ t.val :=
    (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
  have hcapScale : K < S.neck.scale := by
    rw [hscaleEq]
    exact hscale H i parameters hpc (hδ.trans (min_le_right _ _)) hρp (records i) b
  have hqminq : qmin ≤ S.neck.scale :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hcapScale.le
  have hqquot : qDeriv / Cbirth ≤ S.neck.scale :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hcapScale.le
  have haquot : 1 / a₀ ≤ S.neck.scale :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hcapScale.le
  have hqbirth : qDeriv ≤ Cbirth * S.neck.scale := by
    simpa only [mul_comm] using (div_le_iff₀ hCbirth).mp hqquot
  have haq : 1 ≤ a₀ * S.neck.scale := by
    simpa only [mul_comm] using (div_le_iff₀ ha₀).mp haquot
  obtain ⟨x₀, δ, k, datum, w, _hscalarScale, hmetric, _hcapWindow⟩ := hcanonical
  have hzero : ∀ x (V Z : TangentSpace ThreeModel x), w.windowMetric.inner x V Z =
      S.neck.scale * (H.initialMetric i.succ).inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x V)
        (mfderiv ThreeModel ThreeModel S.window x Z) := by
    intro x V Z
    rw [← H.event_output i]
    exact hmetric x V Z
  have hpreserve :=
    (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial).1
  have hscalar (j : H.StageInterval first (H.activeStage t)) (s : ℝ)
      (hs : s ∈ Ioo (H.regularizedStageStart t.val 0 j.val)
        (H.regularizedStageEnd t.val v j.val)) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (gamma j s) := by
    have hdomain := H.mapsTo_regularizedStage_Ioo t.val 0 v j.val hs
    have htime : 0 ≤ t.val - s ^ 2 := (H.stageDomain_subset j.val hdomain).1
    have hratio : 3 / (a₀ + (t.val - s ^ 2)) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num) ha₀ (le_add_of_nonneg_right htime)
    have hneg : -(3 / a₀) ≤ -3 / (a₀ + (t.val - s ^ 2)) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hneg.trans (hpreserve j.val (t.val - s ^ 2) hdomain (gamma j s)).2
  have haction := (hprepared w hRadius hm hζ).2 H i.succ t hbirth
    S.window S.window_smooth S.neck.scale qDeriv a₀ S.neck.scale_pos hqDeriv hqbirth haq
    hzero parameters records hfixed hscalarInitial
    (fun j hij hjt b => (hlater j hij hjt b).trans (min_le_left _ _))
    hderiv hqminq pole hball first hf v hv hvE hpast hstart
    gamma hC1 hInt hscalar hterminal hnode xPast hxPast hwindowPoint.symm
  exact (not_lt_of_ge hsmall) haction

theorem exists_uniform_cap_window_exclusion_of_raw_cap_requests
    (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ εreq ≤ 1 / 2 ∧ 0 < Rreq ∧ Rbirth < Rreq ∧
      4 ≤ mreq ∧ 0 < δreq ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.succ) (hl : i.succ ≤ H.activeStage t),
      t.val - v ^ 2 ≤ H.time i.succ →
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (Dbig ζ : ℝ) (m : ℕ)
        (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
        Rreq ≤ Dbig → mreq ≤ m → ζ ≤ εreq → S.hasCanonicalWindow →
        S.neck.scale = ((records i).static b).neck.scale →
        gamma ⟨i.succ, hf, hl⟩ (Real.sqrt (t.val - H.time i.succ)) ∉
          S.window '' {z : standardCapWindow Dbig | ‖z.val‖ ≤ Rbirth} := by
  obtain ⟨εreq, Rreq, mreq, δreq, hεreq, hεhalf, hRreq, hRbirthReq, hmreq,
      hδreq, _hwindowScale, hwindow⟩ :=
    exists_uniform_cap_window_exclusion_of_raw_cap_requests_with_window_scale_bound.{u}
      Aact E rTerm qDeriv a₀ ρ c Rbirth Cderiv hE hrTerm hqDeriv ha₀ hρ hc hRbirth
  exact ⟨εreq, Rreq, mreq, δreq, hεreq, hεhalf, hRreq, hRbirthReq, hmreq,
    hδreq, hwindow⟩

theorem exists_uniform_regularCrossing_at_node_of_raw_cap_requests
    (Aact E rTerm qDeriv a₀ ρ c Rbirth : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hρ : 0 < ρ) (hc : 0 < c)
    (hRbirth : StandardCap.transitionEnd ≤ Rbirth) :
    ∃ (εreq Rreq : ℝ) (mreq : ℕ) (δreq : ℝ),
      0 < εreq ∧ 0 < Rreq ∧ 0 < δreq ∧
    ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters)
      (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    ∀ (t : Icc (0 : ℝ) H.horizon)
      (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
    ∀ (pole : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t pole rTerm →
    ∀ gamma : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t.val (gamma j)) volume
        (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) →
      gamma ⟨H.activeStage t, hle, le_rfl⟩ 0 = pole →
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = gamma ⟨j.castSucc, hf, j.castSucc_le_succ.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = gamma ⟨j.succ, hf.trans j.castSucc_le_succ, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t.val (gamma j)
          (H.regularizedStageStart t.val 0 j.val) (H.regularizedStageEnd t.val v j.val)) ≤ Aact →
    ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      parameters.recenterConstant ≤ c →
      parameters.delta (H.time i.succ) ≤ δreq →
      parameters.neckRadius (H.time i.succ) ≤ ρ →
      (∀ j : Fin H.eventCount, i.succ ≤ j.castSucc → j.succ ≤ H.activeStage t →
        ∀ b, (records j).delta b ≤ δreq) →
      (∀ j : Fin (H.eventCount + 1), i.succ ≤ j → j ≤ H.activeStage t →
        ∀ y : (H.stage j).Carrier, ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s ≤ t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun u => metricScalarAt (H.stageMetric j u) y) (Iic s) s| ≤
            Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ b : (H.event i).RetainedBoundaryIndex,
        ∃ (Dbig ζ : ℝ) (m : ℕ)
          (S : (H.event i).PresentedStaticCap parameters.fixed Dbig m ζ b),
          Rreq ≤ Dbig ∧ mreq ≤ m ∧ ζ ≤ εreq ∧ S.hasCanonicalWindow ∧
          S.neck.scale = ((records i).static b).neck.scale) →
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
  classical
  obtain ⟨εreq, Rreq, mreq, δreq, hεreq, _hεhalf, hRreq, _hRbirthR,
      _hmreq, hδreq, hwindow⟩ :=
    exists_uniform_cap_window_exclusion_of_raw_cap_requests.{u}
      Aact E rTerm qDeriv a₀ ρ c Rbirth Cderiv hE hrTerm hqDeriv ha₀ hρ hc hRbirth
  refine ⟨εreq, Rreq, mreq, δreq, hεreq, hRreq, hδreq, ?_⟩
  intro H parameters records hfixed hscalarInitial t first hle v hv hvE hpast
    pole hball gamma hC1 hInt hterminal hnode hsmall i hf hl hpc hδ hρp hlater hderiv hraw
  by_contra hbad
  obtain ⟨b, z, hcap⟩ :=
    ((H.event i).regularCrossing_or_cap_of_admissible_node
      (records i).old_eq_retained (hnode i hf hl)).resolve_left hbad
  obtain ⟨Dbig, ζ, m, S, hRadius, hm, hζ, hcanonical, hscaleEq⟩ := hraw b
  have hpoint : gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
      (Real.sqrt (t.val - H.time i.succ)) = S.inclusion (S.witness.cap z) :=
    Sum.inl_injective (hcap.symm.trans (S.cap_eq z))
  have hstart : t.val - v ^ 2 < H.time i.succ := by
    let start : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - v ^ 2, H.stageDomain_subset first hpast⟩
    have hactive : H.activeStage start = first := (H.mem_stageDomain_iff start first).mp hpast
    by_contra hn
    have hi : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
  obtain ⟨_, _, _, _, _, _, _, hcapWindow⟩ := id hcanonical
  obtain ⟨xPast, hxPast, hwindowPoint⟩ := hcapWindow z
  exact hwindow H parameters records hfixed hscalarInitial t first hle v hv hvE hpast
    pole hball gamma hC1 hInt hterminal hnode hsmall i (hf.trans i.castSucc_le_succ) hl
    hstart.le hpc hδ hρp hlater hderiv b Dbig ζ m S hRadius hm hζ hcanonical hscaleEq
    ⟨xPast, hxPast.trans hRbirth, hwindowPoint.trans hpoint.symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
