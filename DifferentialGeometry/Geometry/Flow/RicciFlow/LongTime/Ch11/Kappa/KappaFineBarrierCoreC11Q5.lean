import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBarrierWindowCoreC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineCapContractsC11Q5

/-!
# fine-cap 窗口屏障链（O-CH11-FINECAP G2 核心，后缀 `_C11Q5`）

KAPPA2 的窗口屏障链（`KappaBarrierWindowCoreC11Q2`）的 **fine 版**（R-C11-4 D-2 (b′)）：
树内屏障只在最内层 `exists_uniform_canonical_cap_birth_action_lower_bound`（`CapWindowAction:1537`）
消费 model tuple——它把 `hasCanonicalWindow`（`D, m, ε` = `parameters` 的 model tuple）的 witness 喂给
`exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall`（:1327），
而 :1327 吃的是**独立** witness（`R ≤ Dbig`、`m₀ ≤ m`、`ζ ≤ ζ₀`）+ 窗口嵌入 + 度量等式。本文件：

* 四个 model 前提（`m₀ ≤ modelOrder`、`R₀ ≤ modelRadius`、`modelAccuracy ≤ ε₀`、`hasCanonicalWindow`）
  换成一个窗口内 fine 前提 `hfine`：`t − W² ≤ time i.succ < t` 的每个 event / retained boundary 有
  `FineCapRealization_C11Q5 _ R₀ m₀ ε₀`；最内层直接调 :1327（`Jbig := J`）。
* **E / W 解耦**：常数只由时钟上界 `E` 选；窗口假设只在 `[t − W², t]`、时钟 `v ≤ W ≤ E`
  （block 常数用，见 `KappaFineScaleC11Q5`）。其余证明与 KAPPA2 Core 逐字相同。
* 导出 `transitionEnd < R₀`（接口 (3) 要 `D' ≥ transitionEnd`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- **fine 形 inserted-cap-birth 下界**：坏 event `i` 的 retained boundary `b` 有请求 `(R₀, m₀, ε₀)`
的 fine realization（代替 model tuple + canonical window）；窗口 `[t − W², t]`，时钟 `v ≤ W ≤ E`。 -/
theorem exists_window_sum_action_gt_of_inserted_cap_birth_C11Q5
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, StandardCap.transitionEnd < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (W : ℝ), W ≤ E →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - W ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
      GC.LongTime.Ch11.FineCapRealization_C11Q5 ((records i).static b) R₀ m₀ ε₀ →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ i.succ)
        (hbirth : H.time i.succ < t.val) (v : ℝ),
      0 ≤ v → v ≤ W → t.val - v ^ 2 ∈ H.stageDomain first →
      t.val - v ^ 2 ≤ H.time i.succ →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (H.le_activeStage t i.succ hbirth.le), le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ z : ThreeBall,
      alpha ⟨i.succ, hfirst, H.le_activeStage t i.succ hbirth.le⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨theta, r, qmin, Cbirth, -, hr, hqmin, hCbirth, hprepared⟩ :=
    exists_uniform_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall.{u,0,0,u}
      A B E rTerm Cderiv hB hE hrTerm
  obtain ⟨D, -, haD, R, hDR, m₀, -, ε₀, δ₀, hε₀, -, hδ₀, hprepared⟩ :=
    hprepared (I := ThreeModel) StandardCap.transitionEnd
  have hR : StandardCap.transitionEnd < R := by
    have hh := le_max_right (1 : ℝ) (StandardCap.transitionEnd + r)
    linarith
  let Qmin := max qmin (max (qDeriv / Cbirth) (1 / a₀))
  have hQmin : 0 < Qmin := (one_div_pos.mpr ha₀).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨δscale, hδscale, hscale⟩ :=
    exists_uniform_static_cap_scale_lower_bound c ρ Qmin hc hρ hQmin
  refine ⟨m₀, R, ε₀, min δ₀ δscale, hR, hε₀, lt_min hδ₀ hδscale, ?_⟩
  intro H parameters hpc records hfixed hscalarInitial t W hWE hδ hρp hderiv
    i b hfine p hball first hfirst hbirth v hv hvW hlower hstart
    alpha halpha hint hscalar hrecent hnode z hpast
  have hvE : v ≤ E := hvW.trans hWE
  have hwin : t.val - W ^ 2 ≤ H.time i.succ := by
    have hv2 : v ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hv hvW 2
    linarith
  let cap := (records i).static b
  let q := cap.neck.scale
  have hcapScale := hscale H i parameters hpc
    ((hδ i hwin hbirth.le).trans (min_le_right _ _)) (hρp i hwin hbirth.le) (records i) b
  have hqminq : qmin ≤ q := (le_max_left _ _).trans hcapScale.le
  have hd : qDeriv / Cbirth ≤ q :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hcapScale.le
  have ha : 1 / a₀ ≤ q :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hcapScale.le
  have hqDerivQ : qDeriv ≤ Cbirth * q := by
    simpa only [mul_comm] using (div_le_iff₀ hCbirth).mp hd
  have haq : 1 ≤ a₀ * q := by simpa only [mul_comm] using (div_le_iff₀ ha₀).mp ha
  obtain ⟨x₀, δ, k, datum, w, J, hJ, -, hmetric, hcap⟩ := hfine
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have hzero : ∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      q * (H.initialMetric i.succ).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z) := by
    intro x v z
    rw [← H.event_output i]
    exact hmetric x v z
  exact hprepared w le_rfl le_rfl le_rfl H i.succ t hbirth.le J hJ q qDeriv a₀
    cap.neck.scale_pos hqDeriv hqDerivQ haq hzero parameters records hfixed hscalarInitial
    (fun j hij hj z => ((records j).delta_le z).trans
      ((hδ j (H.time_succ_mem_window_C11Q2 t i j hwin hij hj).1
        (H.time_succ_mem_window_C11Q2 t i j hwin hij hj).2).trans (min_le_left _ _)))
    (fun j hij _ x s hs hst hq => H.abs_derivWithin_stageScalar_le_of_window_C11Q2 hderiv j
      (hwin.trans (H.time_strictMono.monotone hij)) x s hs hst hq)
    hqminq p hball first hfirst v hv hvE hlower hstart
    alpha halpha hint hscalar hrecent hnode x hx (hpast.trans hpoint.symm)

/-- **fine 形 non-regular node 下界**：窗口内 fine 前提 `hfine`（对所有 `t − W² ≤ time i.succ < t`
的 event）代替逐 event 的 canonical window。 -/
theorem exists_window_sum_action_gt_of_nonregular_node_C11Q5
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, StandardCap.transitionEnd < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (W : ℝ), W ≤ E →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - W ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        t.val - W ^ 2 ≤ H.time i.succ → H.time i.succ < t.val →
        GC.LongTime.Ch11.FineCapRealization_C11Q5 ((records i).static b) R₀ m₀ ε₀) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ W → t.val - v ^ 2 ∈ H.stageDomain first →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      ¬ (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, haction⟩ :=
    exists_window_sum_action_gt_of_inserted_cap_birth_C11Q5.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hpc records hfixed hscalarInitial
    t W hWE hδ hρp hderiv hfine p hball first hle v hv hvW hlower alpha halpha hint hscalar
    hterminal hnode i hf hl hbad
  have hbirth : H.time i.succ < t.val := by
    apply lt_of_le_of_ne ((H.time_strictMono.monotone hl).trans (H.activeStage_time_le t))
    intro he
    have hi : H.activeStage t = i.succ := by
      apply le_antisymm _ hl
      apply H.time_strictMono.le_iff_le.mp
      simpa only [he] using H.activeStage_time_le t
    have hindex :
        (⟨H.activeStage t, hle, le_rfl⟩ : H.StageInterval first (H.activeStage t)) =
        ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ := Subtype.ext hi
    have halphaPoint : HEq (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0) p := by
      have hpair := congrArg
        (fun j : H.StageInterval first (H.activeStage t) =>
          (⟨j, alpha j 0⟩ : Sigma fun j : H.StageInterval first (H.activeStage t) =>
            (H.stage j.val).Carrier)) hindex
      exact (Sigma.mk.inj_iff.mp hpair).2.symm.trans (heq_of_eq hterminal)
    have hpoint : alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0 =
        Eq.rec (motive := fun j _ => (H.stage j).Carrier) p hi :=
      eq_of_heq (halphaPoint.trans (eqRec_heq (φ := fun j => (H.stage j).Carrier) hi p).symm)
    have hclock : Real.sqrt (t.val - H.time i.succ) = 0 := by
      rw [he, sub_self, Real.sqrt_zero]
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    rw [hclock] at hzold hznew hbad
    apply hbad
    rw [← hzold, hpoint]
    exact hball.regularCrossing_of_oldOutput_at_event_time H i he.symm z (hznew.trans hpoint)
  have hstart : t.val - v ^ 2 < H.time i.succ := by
    let start : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - v ^ 2, H.stageDomain_subset first hlower⟩
    have hactive : H.activeStage start = first := (H.mem_stageDomain_iff start first).mp hlower
    by_contra hn
    have hi : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
  have hwin : t.val - W ^ 2 ≤ H.time i.succ := by
    have hv2 : v ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hv hvW 2
    linarith
  obtain ⟨b, z, hbirthLabel⟩ : ∃ (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) := by
    rcases (H.event i).regularCrossing_or_cap_of_admissible_node
        (records i).old_eq_retained (hnode i hf hl) with hregular | ⟨b, z, hcap⟩
    · exact (hbad hregular).elim
    · exact ⟨b, z, Sum.inl_injective (hcap.symm.trans (((records i).static b).cap_eq z))⟩
  exact haction H parameters hpc records hfixed hscalarInitial t W hWE hδ hρp hderiv i b
    (hfine i b hwin hbirth) p hball first (hf.trans i.castSucc_lt_succ.le) hbirth v hv hvW
    hlower hstart.le alpha halpha hint hscalar hterminal hnode z hbirthLabel

open private exists_contMDiff_family_action_lt from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction

/-- **fine 形 regular crossing**：作用量 `< A` ⇒ 每个 event 是 regular crossing。 -/
theorem exists_window_regularCrossing_of_sum_action_lt_C11Q5
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, StandardCap.transitionEnd < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (W : ℝ), W ≤ E →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - W ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        t.val - W ^ 2 ≤ H.time i.succ → H.time i.succ < t.val →
        GC.LongTime.Ch11.FineCapRealization_C11Q5 ((records i).static b) R₀ m₀ ε₀) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ W → t.val - v ^ 2 ∈ H.stageDomain first →
      (∀ j : H.StageInterval first (H.activeStage t),
        ∀ r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        ∀ x : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x) →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_window_sum_action_gt_of_nonregular_node_C11Q5.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hpc records hfixed hscalarInitial
    t W hWE hδ hρp hderiv hfine p hball first hle v hv hvW hpast hscalar alpha halpha hint
    hterminal hnode hsmall
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let S := ∑ j : H.StageInterval first (H.activeStage t),
    H.stageRegularizedAction j.val t (alpha j)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)
  have hepsilon : 0 < (A - S) / 2 := half_pos (sub_pos.mpr hsmall)
  obtain ⟨beta, hbeta, hbetaStart, hbetaEnd, hbetaInt, hbetaAction⟩ :=
    exists_contMDiff_family_action_lt H hle (le_refl 0) hv hupper hpast
      alpha halpha hint hnode hepsilon
  have hbetaSmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (beta j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    change _ < S + (A - S) / 2 at hbetaAction
    linarith only [hbetaAction, hsmall]
  have hbetaTerminal : beta ⟨H.activeStage t, hle, le_rfl⟩ 0 = p := by
    have hs := hbetaStart ⟨H.activeStage t, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc (le_refl 0) hupperIcc] at hs
    exact hs.trans hterminal
  have hbetaNode (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t) :
      ∃ z : (H.event i).old,
        z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)) ∧
        (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ)) := by
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  intro i hf hl
  by_contra hbad
  have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
  rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
  have hlarge := hbarrier H parameters hpc records hfixed hscalarInitial t W hWE hδ hρp hderiv
    hfine p hball first hle v hv hvW hpast beta hbeta hbetaInt
    (fun j r hr => hscalar j r hr (beta j r)) hbetaTerminal hbetaNode i hf hl
    (by simpa only [ho, hn] using hbad)
  exact (not_lt_of_ge hbetaSmall.le) hlarge

/-- **fine 形极小曲线屏障**（KAPPA2 `exists_window_regularCrossing_minimizer_C11Q2` 的 fine 版）：
`regularizedCost < A`、`v ≤ W` ⇒ `q` 是 regular minimizer 端点。 -/
theorem exists_window_regularCrossing_minimizer_C11Q5
    (A E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, StandardCap.transitionEnd < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon) (W : ℝ), W ≤ E →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - W ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - W ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      (∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
        t.val - W ^ 2 ≤ H.time i.succ → H.time i.succ < t.val →
        GC.LongTime.Ch11.FineCapRealization_C11Q5 ((records i).static b) R₀ m₀ ε₀) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      v ≤ W →
      ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
      q ∈ H.regularMinimizerEndpoints first (H.activeStage t) hle t (3 / a₀) v p := by
  have hB : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hregular⟩ :=
    exists_window_regularCrossing_of_sum_action_lt_C11Q5.{u}
      A (3 / a₀) E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hpc records hfixed hscalarInitial
    t W hWE hδ hρp hderiv hfine p hball first hle v hvW q hcost
  have hfinite : H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q ≠ ⊤ := by
    intro htop
    rw [htop] at hcost
    exact not_lt_of_ge le_top hcost
  have hne : (H.regularizedActionValues first (H.activeStage t) hle t (3 / a₀) 0 v p q).Nonempty
      := by
    by_contra hn
    exact hfinite (H.regularizedCost_eq_top_of_no_competitor first (H.activeStage t) hle
      t (3 / a₀) 0 v p q (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hv : 0 ≤ v := hvalue.2.1
  have hpast : t.val - v ^ 2 ∈ H.stageDomain first := hvalue.2.2.2.1
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val))
      (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x := by
    have hdomain := H.mapsTo_regularizedStage_Ioo t 0 v j.val hr
    have htime : 0 ≤ t.val - r ^ 2 := (H.stageDomain_subset j.val hdomain).1
    have hratio : 3 / (a₀ + (t.val - r ^ 2)) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hlower : -(3 / a₀) ≤ -3 / (a₀ + (t.val - r ^ 2)) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlower.trans (hpreserve.1 j.val (t.val - r ^ 2) hdomain x).2
  obtain ⟨gamma, hgamma, hint, hrecent, hold, hnode, hmin⟩ :=
    H.exists_regularizedCost_minimizer_of_ne_top first (H.activeStage t) hle
      t (3 / a₀) 0 v hB hupper hscalar p q hfinite
  have hext := H.regularizedExtendedAction_eq_sum_action first (H.activeStage t)
    (le_refl 0) hv hupperIcc hpast gamma hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hsmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (gamma j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    apply WithTop.coe_lt_coe.mp
    rw [← hext, hmin]
    exact hcost
  refine ⟨gamma, hgamma, hrecent, hold, ?_, hmin⟩
  intro i hf hl
  exact hregular H parameters hpc records hfixed hscalarInitial t W hWE hδ hρp hderiv hfine
    p hball first hle v hv hvW hpast hscalar gamma hgamma hint hrecent hnode hsmall i hf hl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
