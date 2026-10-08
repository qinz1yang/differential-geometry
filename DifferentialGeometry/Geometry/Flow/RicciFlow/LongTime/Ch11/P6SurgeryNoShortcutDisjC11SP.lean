import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapPushC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CollarShortCurveC11SP

/-!
# O-CH11-NATIVE-SHORT G2：(D4′) buffer no-shortcut，`hshort′` 孪生 + `hdisj` consumer（`_C11SP`）

A2 G5 的 `hshort` binder 原形为假（`w` = core 边界球点 `boundaryOldPoint`，见 G1 文件头），
故本文件给 G5 的**孪生**（新名字，不改 A2 文件）：`hshort` 换成 `hshort′`（多前件 `hw`；G5 证明里两处
调用点 `hw` / `hu` 都在作用域），结论与 G5 **逐字相同**（同一 `C_buf = max (1 + 4·Cp/c) Cs`）。
consumer `surgery_no_shortcut_buffer_of_disj_C11SP` = 孪生 history 层
+ G6 `hpush_of_disjoint_windows_C11SP`
（`Cp = 22`）+ G1 `hshort_of_collar_history_C11SP`（`c = min (1/(2K)) ((Dc − TE − 10)/K²)`，
`Cs = 4K(TE + 13)`，`K = TE + 11`）⇒ 只剩 `hdisj`（PROVISIONAL[hdisj]）。
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

/-- **G2 event twin（PROVISIONAL[hpush, hshort′]）**：A2 G5 `oldTerminal_edist_le_mul_of_buffer_C11SP`
的孪生，唯一改动 = `hshort` 换成 `hshort′`（多前件 `hw`：`w` 受保护或在某 cap 的 buffer）；
结论逐字同 G5（同一 `C_buf = max (1 + 4·Cp/c) Cs`）。 -/
theorem oldTerminal_edist_le_mul_of_buffer_short_C11SP (E : MetricCutCapEvent P Q a s)
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
    (hshort' : ∀ (u w : E.old) (b₀ : E.RetainedBoundaryIndex) (x : standardCapWindow D),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = E.oldOutput u →
      ((∀ b, E.oldOutput w ∉ (S b).window ''
          {y : standardCapWindow D | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₁ : E.RetainedBoundaryIndex) (x' : standardCapWindow D),
          StandardCap.transitionEnd < ‖x'.val‖ ∧ ‖x'.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          (S b₁).window x' = E.oldOutput w) →
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
    · obtain ⟨γ, hγ, hγ0, hγ1, hmap, hlen⟩ := hshort' u w b₀ x hx1 hx2 hxu hw hlt
      exact (terminal_distance_le_of_interior_curve E u w γ hγ hγ0 hγ1 hmap).trans
        (hlen.trans (mul_le_mul' hCsCb le_rfl))
    · have hlt' : riemannianEDistOf E.outputMetric (E.oldOutput w) (E.oldOutput u) <
          ENNReal.ofReal (c / Real.sqrt (S b₀).neck.scale) := by
        rw [DifferentialGeometry.Toponogov.riemannianEDistOf_comm]
        exact hlt
      obtain ⟨γ, hγ, hγ0, hγ1, hmap, hlen⟩ := hshort' w u b₀ x hx1 hx2 hxw hu hlt'
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

/-- **G2 history twin（PROVISIONAL[hpush, hshort′]）**：A2 G5 `surgery_no_shortcut_buffer_C11SP` 的孪生，
`hshort` 换成 `hshort′`；结论逐字同 G5：
`∀ δ > 0, ∀ᶠ t ↑ τ, d_{e⁻,t}(pm, qm) ≤ C_buf·d_{e⁺,τ}(pp, qp) + δ`。 -/
theorem surgery_no_shortcut_buffer_short_C11SP (H : ObservedHistory.{u}) (e : Fin H.eventCount)
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
    (hshort' : ∀ (u w : (H.event e).old) (b₀ : (H.event e).RetainedBoundaryIndex)
      (x : standardCapWindow Dc),
      StandardCap.transitionEnd < ‖x.val‖ → ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      (S b₀).window x = (H.event e).oldOutput u →
      ((∀ b, (H.event e).oldOutput w ∉ (S b).window ''
          {y : standardCapWindow Dc | ‖y.val‖ ≤ StandardCap.transitionEnd + 10}) ∨
        ∃ (b₁ : (H.event e).RetainedBoundaryIndex) (x' : standardCapWindow Dc),
          StandardCap.transitionEnd < ‖x'.val‖ ∧ ‖x'.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          (S b₁).window x' = (H.event e).oldOutput w) →
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
  have hD4 := (H.event e).oldTerminal_edist_le_mul_of_buffer_short_C11SP S hOld hcanonical hε hD
    hCp hc hpush hshort' u w hpb hqb
  have hout : H.stageMetric e.succ (H.time e.succ) = (H.event e).outputMetric := by
    rw [H.stageMetric_initial, H.event_output]
  rw [hout]
  filter_upwards [terminal_edist_approx_C11D (H.event e).terminal ((H.event e).oldTerminal u)
    ((H.event e).oldTerminal w) hδ] with t ht
  rw [stageMetric_castSucc_apply]
  rw [(H.event e).oldTerminal_eq u, (H.event e).oldTerminal_eq w] at ht
  exact ht.trans (add_le_add hD4 le_rfl)

/-- **G2 consumer（PROVISIONAL[hdisj]）**：(D4′) history 层只剩 `hdisj`——`hpush` 由 G6（`Cp = 22`），
`hshort′` 由 G1（显式 `c`、`Cs`）付清；结论 = G5 结论在 `Cp = 22`、`c`、`Cs` 处的实例。 -/
theorem surgery_no_shortcut_buffer_of_disj_C11SP (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    {fixed : StaticCapScaffold} {Dc εc : ℝ} {mc : ℕ}
    (S : ∀ b : (H.event e).RetainedBoundaryIndex,
      (H.event e).PresentedStaticCap fixed Dc mc εc b)
    (hOld : (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcanonical : ∀ b, (S b).hasCanonicalWindow) (hε : εc ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < Dc)
    (hdisj : ∀ b b' : (H.event e).RetainedBoundaryIndex, b ≠ b' →
      ∀ y z : standardCapWindow Dc, ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        (S b).window y ≠ (S b').window z)
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
        ENNReal.ofReal (max (1 + 4 * (22 / min (1 / (2 * (StandardCap.transitionEnd + 11)))
          ((Dc - (StandardCap.transitionEnd + 10)) / (StandardCap.transitionEnd + 11) ^ 2)))
          (4 * (StandardCap.transitionEnd + 11) * (StandardCap.transitionEnd + 13))) *
          riemannianEDistOf (H.stageMetric e.succ (H.time e.succ)) pp qp + ENNReal.ofReal δ := by
  have hTE := StandardCap.transitionEnd_pos
  have hc : 0 < min (1 / (2 * (StandardCap.transitionEnd + 11)))
      ((Dc - (StandardCap.transitionEnd + 10)) / (StandardCap.transitionEnd + 11) ^ 2) :=
    lt_min (by positivity) (div_pos (by linarith) (by positivity))
  exact surgery_no_shortcut_buffer_short_C11SP H e S hOld hcanonical hε hD (by norm_num) hc
    ((H.event e).hpush_of_disjoint_windows_C11SP S hOld hcanonical hε hD hdisj)
    (hshort_of_collar_history_C11SP H e S hOld hcanonical hε hD hdisj) hp hq hpb hqb hδ

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
