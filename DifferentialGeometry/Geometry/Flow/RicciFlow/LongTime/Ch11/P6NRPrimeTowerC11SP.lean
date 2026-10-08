import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNRSepC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapNonResurgeryPBC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SpineInterfacesC11SP

set_option autoImplicit false

/-!
# NR′ tower 接线：`hNRprime_of_X_C11SP`（O-CH11-NRPRIME-WIRE G1，后缀 `_C11SP`，INTEGRATION）

NATIVE-SEP HANDOVER 清单 1–8：G4a `nonResurgery_pair_of_tube_sep_C11SP`（`Θ := 1/4`）提升到 tower 帧，
得到 `largeCap_crossing_count_of_nonResurgery_PB_C11SP` 的 `hNR′` binder（**逐字**，生成器
`build-logs/scratch/O-CH11-NRPRIME-WIRE/gen/gen_g1.py` 断言 sha）。常数：`D := |TE| + 10`、`ε := η := 1`、
`N := 0` ⇒ `R m₀ ζ₀ δ₀`；`Rmod := R`、`mmod := m₀`、`ε₀ := ζ₀`、`θbar := 1/16`。
结构性付清（树内 PROVED）：HI 初值 ⇐ `exists_initialHI_P6WR`；`1 ≤ a₀·q₁`、`q₁ > 0` ⇐
`exists_uniform_static_cap_scale_lower_bound`（`ρ := q.nr 0`，antitone ⇐
`neckRadius_antitone_of_chainDiagonal_C11SP`）；
晚期性 `a ≥ t − θ/Q ≥ T₁`（`θ/Q < θ·nr(t)² ≤ nr(0)²/(16B)`）+ `Tendsto delta`
⇒ 窗内 `δ ≤ δ₀`、(ii) 与 cap 尺度；
时间 (i) / age ⇐ public `activeStage_time_le` / `le_activeStage`；
trace = `restrictLast` ∘ `restrictFirst`，crossing = `A.crossing e₂`。
**剩余前提 = Xtower**：NR′ 前提前缀逐字（`ε₀ := εX`、`θbar := 1/16`；anchor 的 `∃ b z, …∧…` 柯里化为 `∀ b z, … → …`）
之后接 **已登记合同 X 的逐字实例**（G4a `hW`/`htube`/`hderivW`/`hfinalW` 四子句，binder 形 `∀ W, … →` 写成
`∃ W, … ∧`，代入 `H.toHistory ↦ H`、`records e₁ ↦ records n e₁`、`R ↦ Rmod`、`qcan ↦ Cbirth·q₁`、
`t ↦ H.time e₂.succ`（final 子句取整个 `e₂` slab）；生成器断言空白归一化后 = G4a 原文经此代入）。
Xtower 只在 NR′ 语境（同一 tower / 晚期 / 窗内）要 X，不是对任意 history 的总前提 ⇒ **PROVISIONAL[X]**。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1（PROVISIONAL[X]）**：`Xtower → hNR′(Rmod, mmod)`；`hNR′` 逐字 = PB 定理的 `hNR` binder。 -/
theorem hNRprime_of_X_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ C : ℝ≥0, ∃ (Rmod : ℝ) (mmod : ℕ) (εX : ℝ), 0 < εX ∧
    ((
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ εX → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ 1 / 16 →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (_hf₂ : H.activeStage a ≤ e₂.castSucc)
        (_hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
      ∀ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₁).static b).window z =
          A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ →
        ((records n e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ∃ W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier, (∀ i, IsOpen (W i)) ∧
        (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
          ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H e₁.succ i hf x'),
            A'.point e₁.succ le_rfl hf ∈
              ((records n e₁).static b).window '' {z | ‖z.val‖ < Rmod + 1} →
              x' ∈ W i) ∧
        (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
          ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
          ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
            Cbirth * ((records n e₁).static b).neck.scale < (H.event i).incoming.flow.scalar τ x' →
            |derivWithin (fun v => (H.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
              C * (H.event i).incoming.flow.scalar τ x' ^ 2) ∧
        (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc →
          ∀ τ ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ),
          Cbirth * ((records n e₁).static b).neck.scale < (H.event e₂).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2)) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ θbar : ℝ, 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rmod ≤ pBase.modelRadius → mmod ≤ pBase.modelOrder →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ B : ℝ, 0 < B → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ * B ≤ θbar →
      let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon), T₀ ≤ (t : ℝ) →
      ∀ Q : ℝ, (q.neckRadius t ^ 2)⁻¹ < Q →
      ∀ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (t : ℝ) - a ≤ θ / Q →
      ∀ (y : (H.stageAt t).Carrier)
        (A : BackwardPointTrace H
          (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) y),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) ≤ 2 * B * Q) →
      ∀ (e₁ e₂ : Fin H.eventCount) (hf₁ : H.activeStage a ≤ e₁.castSucc)
        (hl₁ : e₁.succ ≤ H.activeStage t) (hf₂ : H.activeStage a ≤ e₂.castSucc)
        (hl₂ : e₂.succ ≤ H.activeStage t), e₁ < e₂ →
        (∃ (b : (H.event e₁).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
          StandardCap.transitionEnd < ‖z.val‖ ∧ ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
          ((records n e₁).static b).window z =
            A.point e₁.succ (hf₁.trans e₁.castSucc_lt_succ.le) hl₁ ∧
          ((records n e₁).static b).neck.scale ≤ 4 * (B * Q)) →
      ∀ (b : (H.event e₂).RetainedBoundaryIndex) (z : standardCapWindow params.modelRadius),
        StandardCap.transitionEnd < ‖z.val‖ → ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
        ((records n e₂).static b).neck.scale ≤ 4 * (B * Q) →
        ((records n e₂).static b).window z ≠
          A.point e₂.succ (hf₂.trans e₂.castSucc_lt_succ.le) hl₂) := by
  obtain ⟨Csep, hCsep, _Pc, _Creset, Cbirth, _hPc, _hCreset, hCbirth, hG⟩ :=
    RetainedCoreHistory.nonResurgery_pair_of_tube_sep_C11SP.{u} (1 / 4) (by norm_num) (by norm_num)
  refine ⟨Cbirth, hCbirth, fun C => ?_⟩
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hnr⟩ :=
    hG C (|StandardCap.transitionEnd| + 10) 1 1 (by positivity) one_pos one_pos 0
  refine ⟨R, m₀, ζ₀, hζ₀, fun hX => ?_⟩
  refine ⟨ζ₀, hζ₀, 1 / 16, by norm_num, ?_⟩
  intro pBase Γf S F hT q hdiag hacc hrad hord hRm hmm params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  obtain ⟨TX, hTX, hXB⟩ :=
    hX S F hT q hdiag hacc hrad hord hRm hmm params records h1 h2 h3 h4 h5 h6 h7 h8 B hB
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  have hanti := neckRadius_antitone_of_chainDiagonal_C11SP S q hdiag
  have hρ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have hc4 := params.recenterConstant_ge_four
  obtain ⟨δK, hδK, hscaleLB⟩ := exists_uniform_static_cap_scale_lower_bound
    params.recenterConstant (q.neckRadius 0) (1 / a₀) (by linarith) hρ (by positivity)
  have hsq := Real.sqrt_nonneg (5 * Csep)
  have hK₂ : 0 < 8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) + 40000 +
      2 * params.recenterConstant := by
    have : 0 ≤ 8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) := by positivity
    linarith
  have hδs : 0 < min (min δ₀ δK) (1 / (8 * Real.sqrt (5 * Csep) *
      (|StandardCap.transitionEnd| + 10 + 1) + 40000 + 2 * params.recenterConstant)) :=
    lt_min (lt_min hδ₀ hδK) (by positivity)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp (h7.eventually (gt_mem_nhds hδs))
  refine ⟨max TX (T₁ + q.neckRadius 0 ^ 2 / (16 * B) + 1),
    lt_of_lt_of_le hTX (le_max_left _ _), ?_⟩
  intro n θ hθ hθB H t ht Q hQ a hat hwin y A hRA e₁ e₂ hf₁ hl₁ hf₂ hl₂ hlt hex b₂ z₂ hz₂a hz₂b
    hs₂
  obtain ⟨b, z, hz1, hz2, hanc, hsc⟩ := hex
  obtain ⟨W, hW, htube, hderivW, hfinalW⟩ :=
    hXB n θ hθ hθB t ((le_max_left _ _).trans ht) Q hQ a hat hwin y A hRA e₁ e₂ hf₁ hl₁ hf₂ hl₂
      hlt b z hz1 hz2 hanc hsc
  have hl : e₁.succ ≤ e₂.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
  have hta : (a : ℝ) < H.time e₁.succ := by
    by_contra hcon
    have h1' := H.le_activeStage a e₁.succ (not_lt.mp hcon)
    exact lt_irrefl _ ((h1'.trans hf₁).trans_lt Fin.castSucc_lt_succ)
  have hte₂ : H.time e₂.succ ≤ (t : ℝ) :=
    (H.time_strictMono.monotone hl₂).trans (H.activeStage_time_le t)
  have hQpos : 0 < Q := lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hQ
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have hnrt : 0 < q.neckRadius t := q.neckRadius_pos _ ht0
  have hnr_le : q.neckRadius t ≤ q.neckRadius 0 :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
  have hinvQ : Q⁻¹ < q.neckRadius t ^ 2 := inv_lt_of_inv_lt₀ (by positivity) hQ
  have hθQ : θ / Q ≤ q.neckRadius 0 ^ 2 / (16 * B) := by
    have hsq2 : q.neckRadius t ^ 2 ≤ q.neckRadius 0 ^ 2 := pow_le_pow_left₀ hnrt.le hnr_le 2
    have h1' : θ / Q ≤ θ * q.neckRadius 0 ^ 2 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (hinvQ.le.trans hsq2) hθ.le
    have h2' : θ * q.neckRadius 0 ^ 2 ≤ q.neckRadius 0 ^ 2 / (16 * B) := by
      rw [le_div_iff₀ (by positivity)]
      calc θ * q.neckRadius 0 ^ 2 * (16 * B) = q.neckRadius 0 ^ 2 * (16 * (θ * B)) := by ring
        _ ≤ q.neckRadius 0 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ = q.neckRadius 0 ^ 2 := by ring
    exact h1'.trans h2'
  have ha_late : T₁ ≤ (a : ℝ) := by
    have := le_max_right TX (T₁ + q.neckRadius 0 ^ 2 / (16 * B) + 1)
    linarith
  have hlate : ∀ s : ℝ, (a : ℝ) ≤ s → params.delta s < min (min δ₀ δK)
      (1 / (8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) + 40000 +
        2 * params.recenterConstant)) := fun s hs => hT₁ s (ha_late.trans hs)
  have hδloc : ∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      params.delta (H.time i.succ) ≤ δ₀ := by
    intro i hi _
    have hti : H.time e₁.succ ≤ H.time i.succ :=
      H.time_strictMono.monotone (hi.trans Fin.castSucc_lt_succ.le)
    exact (hlate _ (hta.le.trans hti)).le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have he2late : (a : ℝ) ≤ H.time e₂.succ :=
    hta.le.trans (H.time_strictMono.monotone (hl.trans Fin.castSucc_lt_succ.le))
  have hT2 : H.time e₂.succ - H.time e₁.succ ≤ θ / Q := by linarith
  have hδ2 : ∀ α, (records n e₂).delta α *
      (8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) + 40000 +
        2 * params.recenterConstant) ≤ 1 := by
    intro α
    have hd := ((records n e₂).delta_le α).trans (hlate _ he2late).le
    have hd' := hd.trans (min_le_right _ _)
    have hm := mul_le_mul_of_nonneg_right hd' hK₂.le
    rwa [one_div_mul_cancel hK₂.ne'] at hm
  have h0e₁ : 0 ≤ H.time e₁.succ := H.time_nonneg _
  have hρe₁ : params.neckRadius (H.time e₁.succ) ≤ q.neckRadius 0 := by
    rw [(h4 _ h0e₁).2]
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h0e₁) h0e₁
  have hδe₁ : params.delta (H.time e₁.succ) ≤ δK :=
    (hlate _ hta.le).le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hKlt := hscaleLB H e₁ params le_rfl hδe₁ hρe₁ (records n e₁) b
  have hq₁ : 0 < ((records n e₁).static b).neck.scale :=
    lt_trans (by positivity) hKlt
  have haq : 1 ≤ a₀ * ((records n e₁).static b).neck.scale := by
    have h' := (div_lt_iff₀ ha₀).mp hKlt
    linarith [mul_comm a₀ ((records n e₁).static b).neck.scale]
  have hlt₂ : H.time e₂.castSucc < H.time e₂.succ := H.time_strictMono Fin.castSucc_lt_succ
  have ht' : (H.time e₂.castSucc + H.time e₂.succ) / 2 ∈
      Ioo (H.time e₂.castSucc) (H.time e₂.succ) := ⟨by linarith, by linarith⟩
  have hage : (H.time e₂.castSucc + H.time e₂.succ) / 2 - H.time e₁.succ ≤ θ / Q := by
    linarith
  have hxD : ‖z.val‖ < |StandardCap.transitionEnd| + 10 + 1 := by
    have := le_abs_self StandardCap.transitionEnd
    linarith
  have hBθ : 4 * (B * θ) ≤ 1 / 4 := by
    have := mul_comm B θ
    linarith
  have hB16 : 16 * (B * θ) ≤ 1 := by
    have := mul_comm B θ
    linarith
  have hc₂ : e₂.castSucc ≤ H.activeStage t := Fin.castSucc_lt_succ.le.trans hl₂
  have hs₁ : H.activeStage a ≤ e₁.succ := hf₁.trans Fin.castSucc_lt_succ.le
  have hmain := hnr (F.tower.history n) (records n) (fun i b' => h5 n i b')
    (hRm.trans h1.ge) (hmm.trans h2.ge) (h3.le.trans hacc)
    (Cbirth * ((records n e₁).static b).neck.scale) a₀ B Q θ (by positivity) hQpos hθ.le hBθ hB16
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) e₁ e₂ hl
    ((H.time e₂.castSucc + H.time e₂.succ) / 2) ht' (A.point e₂.castSucc hf₂ hc₂)
    ((A.restrictLast hf₂ hc₂).restrictFirst hs₁ hl) b z hanc.symm hage hsc hxD le_rfl haq hδloc
    hT2 hδ2 W hW htube hderivW
    (fun x' hx' τ hτ hR => hfinalW x' hx' τ ⟨hτ.1, hτ.2.trans ht'.2⟩ hR)
  exact hmain (A.point e₂.succ (hf₂.trans Fin.castSucc_lt_succ.le) hl₂) (A.crossing e₂ hf₂ hl₂)
    b₂ z₂ hz₂a hz₂b hs₂

/-- **consumer（接口对接见证）**：G1 输出的 `hNR′(Rmod, mmod)` 在类型层直接被
`largeCap_crossing_count_of_nonResurgery_PB_C11SP P g Rmod mmod` 接受（elaboration 即逐字对接检查）；
命名合成见 G2 `CCprime_of_X_C11SP`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (C : ℝ≥0) : True := by
  obtain ⟨_Cbirth, _, h⟩ := hNRprime_of_X_C11SP P g
  obtain ⟨Rmod, mmod, _εX, _, hXN⟩ := h C
  have _hCC := fun hX => largeCap_crossing_count_of_nonResurgery_PB_C11SP P g Rmod mmod (hXN hX)
  trivial

end GC.LongTime.Ch11
