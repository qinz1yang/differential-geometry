import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianDistance

/-!
# O-CH11-SPINE-A2 G5：(D4′) buffer no-shortcut 的乘性形（SPINE-B G4b repair (1)，`_C11SP`）

SPINE-B G4b 的 repair (1)：`surgery_no_shortcut_C11D`（`Dist/SurgeryNoShortcutC11D.lean:80`）去掉端点
保护，允许端点落在某 cap `b₀` 的 **buffer**（window 坐标 `transitionEnd < ‖x‖ ≤ transitionEnd + 10`，
retained collar），结论改成**乘性**（SPINE-B 23:3x 要求：huge cap 时加性 `scale^{-1/2}` 误差会大过
footprint）：`d_term(pm, qm) ≤ C_buf · d_out(pp, qp)`，`C_buf = max (1 + 4·Cp/c) Cs ≥ 1` 普适。

证明 = 两情形（SPINE-B 的分法）：
* `d_out ≥ c·scale^{-1/2}`（对每个 buffer 端点）：buffer 端点径向推到受保护点（`hpush`，输出侧
  interior 曲线长 `≤ Cp·scale^{-1/2}`），中段用树内 :846
  `MetricCutCapEvent.oldTerminal_edist_le_of_outside_canonical_cap_windows`，推出段经
  `terminal_distance_le_of_interior_curve`（:773，`open private`）拉回 terminal；加性项 `≤ (4Cp/c)·d_out`。
* `d_out < c·scale^{-1/2}`（某个 buffer 端点）：`hshort` 给 retained 区内（interior (range oldOutput)）
  长 `≤ Cs·d_out` 的光滑曲线，直接拉回 terminal。
两个 binder 都是**单 event、输出侧静态几何**（cap window 的 collar 几何 + 不同 cap window 不相交），
不含时间、terminal 度量、TimeCore、history；是 PROVISIONAL 的 repair target（StandardCap / EventCap 线）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private terminal_distance_le_of_interior_curve edist_le_elength from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapNoShortcut

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- 推出：受保护端点取自身（`L = 0`）；buffer 端点由 `hpush` 推到受保护点（`L = Cp/√scale`）。
两段距离（terminal / output）都 `≤ L`。 -/
theorem exists_protected_push_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) {Cp : ℝ}
    (hCp : 0 ≤ Cp)
    (hpush : ∀ (u : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      ∃ u' : E.old, (∀ b, E.oldOutput u' ∉ (S b).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
          γ 0 = E.oldOutput u ∧ γ 1 = E.oldOutput u' ∧
          MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
          riemannianCurveELength E.outputMetric γ 0 1 ≤
            ENNReal.ofReal (Cp / Real.sqrt (S b₀).neck.scale))
    (u : E.old)
    (hu : (∀ b, E.oldOutput u ∉ (S b).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = E.oldOutput u) :
    ∃ (u' : E.old) (L : ℝ), 0 ≤ L ∧
      (∀ b, E.oldOutput u' ∉ (S b).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal u') ≤
        ENNReal.ofReal L ∧
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput u') ≤ ENNReal.ofReal L ∧
      (L = 0 ∨ ∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = E.oldOutput u ∧ L = Cp / Real.sqrt (S b₀).neck.scale) := by
  rcases hu with hprot | ⟨b₀, x, hx1, hx2, hxu⟩
  · refine ⟨u, 0, le_rfl, hprot, ?_, ?_, Or.inl rfl⟩
    · rw [riemannianEDistOf_self]
      exact bot_le
    · rw [riemannianEDistOf_self]
      exact bot_le
  · obtain ⟨u', hprot', γ, hγ, hγ0, hγ1, hmap, hlen⟩ := hpush u b₀ x hx1 hx2 hxu
    have hL : 0 ≤ Cp / Real.sqrt (S b₀).neck.scale := div_nonneg hCp (Real.sqrt_nonneg _)
    refine ⟨u', Cp / Real.sqrt (S b₀).neck.scale, hL, hprot', ?_, ?_,
      Or.inr ⟨b₀, x, hx1, hx2, hxu, rfl⟩⟩
    · exact (terminal_distance_le_of_interior_curve E u u' γ hγ hγ0 hγ1 hmap).trans hlen
    · have h := edist_le_elength E.outputMetric zero_le_one
        (fun t _ => (hγ.contMDiffAt.of_le (by simp)).contMDiffWithinAt)
      rw [hγ0, hγ1] at h
      exact h.trans hlen

/-- 推出长度在 "`d_out ≥ c/√scale`" 情形下被 `d_out` 线性控制：`L ≤ (Cp/c)·D`。 -/
theorem push_length_le_C11SP {Cp c L D sc : ℝ} (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hL : L = 0 ∨ L = Cp / Real.sqrt sc) (hD : 0 ≤ D)
    (hfar : L = Cp / Real.sqrt sc → c / Real.sqrt sc ≤ D) :
    L ≤ Cp / c * D := by
  rcases hL with h0 | hL
  · rw [h0]
    exact mul_nonneg (div_nonneg hCp hc.le) hD
  · have hid : Cp / Real.sqrt sc = Cp / c * (c / Real.sqrt sc) := by
      rw [div_mul_div_comm, mul_comm Cp c, mul_div_mul_left Cp (Real.sqrt sc) hc.ne']
    rw [hL, hid]
    exact mul_le_mul_of_nonneg_left (hfar hL) (div_nonneg hCp hc.le)

/-- **(D4′) event 层（PROVISIONAL[hpush, hshort]）**：端点各自受保护或在 buffer ⇒
`d_term(oldTerminal u, oldTerminal w) ≤ C_buf · d_out(oldOutput u, oldOutput w)`，
`C_buf = max (1 + 4·Cp/c) Cs`。 -/
theorem oldTerminal_edist_le_mul_of_buffer_C11SP (E : MetricCutCapEvent P Q a s)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : ε ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < D)
    {Cp c Cs : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c)
    (hpush : ∀ (u : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      ∃ u' : E.old, (∀ b, E.oldOutput u' ∉ (S b).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
          γ 0 = E.oldOutput u ∧ γ 1 = E.oldOutput u' ∧
          MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
          riemannianCurveELength E.outputMetric γ 0 1 ≤
            ENNReal.ofReal (Cp / Real.sqrt (S b₀).neck.scale))
    (hshort : ∀ (u w : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) <
        ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale) →
      ∃ γ : ℝ → Q.Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        γ 0 = E.oldOutput u ∧ γ 1 = E.oldOutput w ∧
        MapsTo γ (Icc (0 : ℝ) 1) (interior (range E.oldOutput)) ∧
        riemannianCurveELength E.outputMetric γ 0 1 ≤
          ENNReal.ofReal Cs * riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w))
    (u w : E.old)
    (hu : (∀ b, E.oldOutput u ∉ (S b).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = E.oldOutput u)
    (hw : (∀ b, E.oldOutput w ∉ (S b).window ''
        {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = E.oldOutput w) :
    riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal w) ≤
      ENNReal.ofReal (max (1 + 4 * (Cp / c)) Cs) *
        riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) := by
  classical
  set Cb : ℝ := max (1 + 4 * (Cp / c)) Cs with hCb
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ 4 * (Cp / c) := mul_nonneg (by norm_num) (div_nonneg hCp hc.le)
    exact (by linarith : (1 : ℝ) ≤ 1 + 4 * (Cp / c)).trans (le_max_left _ _)
  set dout := riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) with hdout
  by_cases htop : dout = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hCb1)).ne']
    exact le_top
  -- 短曲线情形
  by_cases hnear : (∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
      (S b₀).window x = E.oldOutput u ∧
      dout < ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale)) ∨
    (∃ (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
      (S b₀).window x = E.oldOutput w ∧
      dout < ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale))
  · have hCsCb : ENNReal.ofReal Cs ≤ ENNReal.ofReal Cb :=
      ENNReal.ofReal_le_ofReal (le_max_right _ _)
    rcases hnear with ⟨b₀, x, hx1, hx2, hxu, hlt⟩ | ⟨b₀, x, hx1, hx2, hxw, hlt⟩
    · obtain ⟨γ, hγ, hγ0, hγ1, hmap, hlen⟩ := hshort u w b₀ x hx1 hx2 hxu hlt
      exact (terminal_distance_le_of_interior_curve E u w γ hγ hγ0 hγ1 hmap).trans
        (hlen.trans (mul_le_mul' hCsCb le_rfl))
    · have hlt' : riemannianEDistOf E.outputMetric (E.oldOutput w) (E.oldOutput u) <
          ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale) := by
        rw [DifferentialGeometry.Toponogov.riemannianEDistOf_comm]
        exact hlt
      obtain ⟨γ, hγ, hγ0, hγ1, hmap, hlen⟩ := hshort w u b₀ x hx1 hx2 hxw hlt'
      have h := (terminal_distance_le_of_interior_curve E w u γ hγ hγ0 hγ1 hmap).trans hlen
      rw [DifferentialGeometry.Toponogov.riemannianEDistOf_comm E.terminal.metric,
        DifferentialGeometry.Toponogov.riemannianEDistOf_comm E.outputMetric] at h
      exact h.trans (mul_le_mul' hCsCb le_rfl)
  -- 远情形：推出 + :846
  simp only [not_or, not_exists, not_and, not_lt] at hnear
  obtain ⟨hfarU, hfarW⟩ := hnear
  set Dr : ℝ := dout.toReal with hDr
  have hDr0 : 0 ≤ Dr := ENNReal.toReal_nonneg
  have hdoutDr : dout = ENNReal.ofReal Dr := (ENNReal.ofReal_toReal htop).symm
  obtain ⟨u', Lu, hLu0, hprotU, htermU, houtU, hLuform⟩ :=
    exists_protected_push_C11SP E S hCp hpush u hu
  obtain ⟨w', Lw, hLw0, hprotW, htermW, houtW, hLwform⟩ :=
    exists_protected_push_C11SP E S hCp hpush w hw
  have hLu : Lu ≤ Cp / c * Dr := by
    rcases hLuform with h0 | ⟨b₀, x, hx1, hx2, hxu, hLeq⟩
    · rw [h0]
      exact mul_nonneg (div_nonneg hCp hc.le) hDr0
    · refine push_length_le_C11SP hc hCp (Or.inr hLeq) hDr0 (fun _ => ?_)
      have h := hfarU b₀ x hx1 hx2 hxu
      rw [hdoutDr] at h
      exact (ENNReal.ofReal_le_ofReal_iff hDr0).mp h
  have hLw : Lw ≤ Cp / c * Dr := by
    rcases hLwform with h0 | ⟨b₀, x, hx1, hx2, hxw, hLeq⟩
    · rw [h0]
      exact mul_nonneg (div_nonneg hCp hc.le) hDr0
    · refine push_length_le_C11SP hc hCp (Or.inr hLeq) hDr0 (fun _ => ?_)
      have h := hfarW b₀ x hx1 hx2 hxw
      rw [hdoutDr] at h
      exact (ENNReal.ofReal_le_ofReal_iff hDr0).mp h
  have hmid := E.oldTerminal_edist_le_of_outside_canonical_cap_windows S hOld hcanonical hε hD
    u' w' hprotU hprotW
  have hout' : riemannianEDistOf E.outputMetric (E.oldOutput u') (E.oldOutput w') ≤
      ENNReal.ofReal (Lu + Dr + Lw) := by
    calc riemannianEDistOf E.outputMetric (E.oldOutput u') (E.oldOutput w')
        ≤ riemannianEDistOf E.outputMetric (E.oldOutput u') (E.oldOutput u) +
            riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w') :=
          DifferentialGeometry.Toponogov.riemannianEDistOf_triangle _ _ _ _
      _ ≤ riemannianEDistOf E.outputMetric (E.oldOutput u') (E.oldOutput u) +
            (riemannianEDistOf E.outputMetric (E.oldOutput u) (E.oldOutput w) +
              riemannianEDistOf E.outputMetric (E.oldOutput w) (E.oldOutput w')) :=
          add_le_add le_rfl (DifferentialGeometry.Toponogov.riemannianEDistOf_triangle _ _ _ _)
      _ ≤ ENNReal.ofReal Lu + (ENNReal.ofReal Dr + ENNReal.ofReal Lw) := by
          refine add_le_add ?_ (add_le_add hdoutDr.le houtW)
          rw [DifferentialGeometry.Toponogov.riemannianEDistOf_comm]
          exact houtU
      _ = ENNReal.ofReal (Lu + Dr + Lw) := by
          rw [← ENNReal.ofReal_add hDr0 hLw0, ← ENNReal.ofReal_add hLu0 (add_nonneg hDr0 hLw0),
            add_assoc]
  have hterm : riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal w) ≤
      ENNReal.ofReal (Lu + (Lu + Dr + Lw) + Lw) := by
    calc riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal w)
        ≤ riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal u') +
            riemannianEDistOf E.terminal.metric (E.oldTerminal u') (E.oldTerminal w) :=
          DifferentialGeometry.Toponogov.riemannianEDistOf_triangle _ _ _ _
      _ ≤ riemannianEDistOf E.terminal.metric (E.oldTerminal u) (E.oldTerminal u') +
            (riemannianEDistOf E.terminal.metric (E.oldTerminal u') (E.oldTerminal w') +
              riemannianEDistOf E.terminal.metric (E.oldTerminal w') (E.oldTerminal w)) :=
          add_le_add le_rfl (DifferentialGeometry.Toponogov.riemannianEDistOf_triangle _ _ _ _)
      _ ≤ ENNReal.ofReal Lu + (ENNReal.ofReal (Lu + Dr + Lw) + ENNReal.ofReal Lw) := by
          refine add_le_add htermU (add_le_add (hmid.trans hout') ?_)
          rw [DifferentialGeometry.Toponogov.riemannianEDistOf_comm]
          exact htermW
      _ = ENNReal.ofReal (Lu + (Lu + Dr + Lw) + Lw) := by
          have h1 : 0 ≤ Lu + Dr + Lw := by linarith
          rw [← ENNReal.ofReal_add h1 hLw0, ← ENNReal.ofReal_add hLu0 (add_nonneg h1 hLw0)]
          congr 1
          ring
  refine hterm.trans ?_
  rw [hdoutDr, ← ENNReal.ofReal_mul (zero_le_one.trans hCb1)]
  apply ENNReal.ofReal_le_ofReal
  have hCbge : 1 + 4 * (Cp / c) ≤ Cb := le_max_left _ _
  have hmul : (1 + 4 * (Cp / c)) * Dr ≤ Cb * Dr := mul_le_mul_of_nonneg_right hCbge hDr0
  nlinarith [hLu, hLw, hmul]

end MetricCutCapEvent

namespace ObservedHistory

/-- **(D4′) history 层（PROVISIONAL[hpush, hshort]；`surgery_no_shortcut_C11D` 的乘性孪生）**：
event `e` 的 regular crossing `pm ↦ pp`、`qm ↦ qp`，端点各自受保护或在某 cap 的 buffer ⇒
`∀ δ > 0, ∀ᶠ t ↑ τ, d_{e⁻,t}(pm, qm) ≤ C_buf · d_{e⁺,τ}(pp, qp) + δ`。 -/
theorem surgery_no_shortcut_buffer_C11SP (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    {Cp c Cs : ℝ} (hCp : 0 ≤ Cp) (hc : 0 < c)
    (hpush : ∀ (u : (H.event e).old) (b₀ : (H.event e).RetainedBoundaryIndex)
      (x : standardCapWindow Dc),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = (H.event e).oldOutput u →
      ∃ u' : (H.event e).old, (∀ b, (H.event e).oldOutput u' ∉ (S b).window ''
          {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
        ∃ γ : ℝ → (H.stage e.succ).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
          γ 0 = (H.event e).oldOutput u ∧ γ 1 = (H.event e).oldOutput u' ∧
          MapsTo γ (Icc (0 : ℝ) 1) (interior (range (H.event e).oldOutput)) ∧
          riemannianCurveELength (H.event e).outputMetric γ 0 1 ≤
            ENNReal.ofReal (Cp / Real.sqrt (S b₀).neck.scale))
    (hshort : ∀ (u w : (H.event e).old) (b₀ : (H.event e).RetainedBoundaryIndex)
      (x : standardCapWindow Dc),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = (H.event e).oldOutput u →
      riemannianEDistOf (H.event e).outputMetric ((H.event e).oldOutput u)
          ((H.event e).oldOutput w) <
        ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale) →
      ∃ γ : ℝ → (H.stage e.succ).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        γ 0 = (H.event e).oldOutput u ∧ γ 1 = (H.event e).oldOutput w ∧
        MapsTo γ (Icc (0 : ℝ) 1) (interior (range (H.event e).oldOutput)) ∧
        riemannianCurveELength (H.event e).outputMetric γ 0 1 ≤
          ENNReal.ofReal Cs * riemannianEDistOf (H.event e).outputMetric
            ((H.event e).oldOutput u) ((H.event e).oldOutput w))
    {pm qm : (H.stage e.castSucc).Carrier} {pp qp : (H.stage e.succ).Carrier}
    (hp : (H.event e).RegularCrossing pm pp) (hq : (H.event e).RegularCrossing qm qp)
    (hpb : (∀ b, pp ∉ (S b).window ''
        {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow Dc),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = pp)
    (hqb : (∀ b, qp ∉ (S b).window ''
        {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
      ∃ (b₀ : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow Dc),
        StandardCap.transitionEnd < ‖x.val‖ ∧ ‖x.val‖ ≤ StandardCap.transitionEnd + 10 ∧
        (S b₀).window x = qp)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[<] H.time e.succ,
      riemannianEDistOf (H.stageMetric e.castSucc t) pm qm ≤
        ENNReal.ofReal (max (1 + 4 * (Cp / c)) Cs) *
          riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp + ENNReal.ofReal δ := by
  obtain ⟨u, -, hu1, hu2⟩ := hp
  obtain ⟨w, -, hw1, hw2⟩ := hq
  subst hu1 hw1 hu2 hw2
  have hD4 := (H.event e).oldTerminal_edist_le_mul_of_buffer_C11SP S hOld hcanonical hε hD
    hCp hc hpush hshort u w hpb hqb
  have hout : H.stageMetric e.succ (H.time e.succ) = (H.event e).outputMetric := by
    rw [H.stageMetric_initial, H.event_output]
  rw [hout]
  filter_upwards [terminal_edist_approx_C11D (H.event e).terminal ((H.event e).oldTerminal u)
    ((H.event e).oldTerminal w) hδ] with t ht
  rw [stageMetric_castSucc_apply]
  rw [(H.event e).oldTerminal_eq u, (H.event e).oldTerminal_eq w] at ht
  exact ht.trans (add_le_add hD4 le_rfl)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
