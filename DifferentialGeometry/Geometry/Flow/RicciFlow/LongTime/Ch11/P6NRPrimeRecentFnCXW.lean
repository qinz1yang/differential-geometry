import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NRPrimeTowerC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6XtowerOfSepRhoP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LargeCapNonResurgeryPBFnP6XS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepSeqOfRecentCXW

set_option autoImplicit false

/-!
# X0 的 actual recent producer / NR-prime from actual recent data

保留原 X0 的 hNR 输出接口。删除未生产的全球 SEPseq 前提，在 actual params/records
已引入后使用 `sepSeq_of_recent_CXW`。精度取 `min(旧阈值,1/2)`，与 A、queries 无关。
profile equality 只在 eventual nonnegative query times 上把 params 的 ceiling 搬到 q。
不要求 recenter constants 相等；uniform birth scale 来自实际 finite-history volumes。
-/

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow GC.GeneralFlow
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- 实例 SEPseq 推出 NR ceiling / Sequence separation gives the NR ceiling. -/
theorem sepRhoNR_of_sepRhoPlus_CXW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q params : CutoffParameters}
    {records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory e params}
    (hseq : ∀ (ν : ℕ → ℕ) (t : ℕ → ℝ), Tendsto t atTop atTop → ∀ m : ℕ,
      ∀ᶠ k in atTop, ∀ (i : Fin (F.tower.history (ν k)).eventCount)
          (b : ((F.tower.history (ν k)).toHistory.event i).RetainedBoundaryIndex),
        (F.tower.history (ν k)).time i.succ ≤ t k →
        t k - (F.tower.history (ν k)).time i.succ ≤
          1 / 4 * (((records (ν k) i).static b).neck.scale)⁻¹ →
        ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius (t k) ^ 2)⁻¹ ≤
          ((records (ν k) i).static b).neck.scale)
    (Cbirth : ℝ) (hC : 0 < Cbirth) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ (n : ℕ) (t : ℝ), T₀ ≤ t →
      ∀ (e : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex),
        (F.tower.history n).time e.succ ≤ t →
        t - (F.tower.history n).time e.succ ≤ 1 / 4 * (((records n e).static b).neck.scale)⁻¹ →
        (q.neckRadius t ^ 2)⁻¹ ≤ Cbirth * ((records n e).static b).neck.scale := by
  by_contra hcon
  have hbad : ∀ k : ℕ, ∃ (n : ℕ) (t : ℝ) (e : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex),
      (k : ℝ) + 1 ≤ t ∧ (F.tower.history n).time e.succ ≤ t ∧
      t - (F.tower.history n).time e.succ ≤ 1 / 4 * (((records n e).static b).neck.scale)⁻¹ ∧
      Cbirth * ((records n e).static b).neck.scale < (q.neckRadius t ^ 2)⁻¹ := by
    intro k
    by_contra hk
    apply hcon
    refine ⟨(k : ℝ) + 1, by positivity, fun n t ht e b h1 h2 => ?_⟩
    by_contra h3
    exact hk ⟨n, t, e, b, ht, h1, h2, lt_of_not_ge h3⟩
  choose ν t e b hb using hbad
  have htend : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith [(hb k).1]) tendsto_natCast_atTop_atTop
  obtain ⟨m, hm⟩ := exists_nat_ge Cbirth⁻¹
  obtain ⟨k, hk⟩ := (hseq ν t htend m).exists
  obtain ⟨_, h2, h3, h4⟩ := hb k
  have hs := hk (e k) (b k) h2 h3
  have hinv0 : 0 ≤ (q.neckRadius (t k) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hm1 : 1 ≤ Cbirth * ((m : ℝ) + 1) := by
    have h' : Cbirth⁻¹ ≤ (m : ℝ) + 1 := by linarith
    calc (1 : ℝ) = Cbirth * Cbirth⁻¹ := (mul_inv_cancel₀ hC.ne').symm
      _ ≤ Cbirth * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left h' hC.le
  have hmx : ((m : ℝ) + 1) * (q.neckRadius (t k) ^ 2)⁻¹ ≤
      ((m : ℝ) + 1) * max ((m : ℝ) + 1) (q.neckRadius (t k) ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hfin : (q.neckRadius (t k) ^ 2)⁻¹ ≤
      Cbirth * ((records (ν k) (e k)).static (b k)).neck.scale := by
    calc (q.neckRadius (t k) ^ 2)⁻¹
        ≤ Cbirth * ((m : ℝ) + 1) * (q.neckRadius (t k) ^ 2)⁻¹ := le_mul_of_one_le_left hinv0 hm1
      _ = Cbirth * (((m : ℝ) + 1) * (q.neckRadius (t k) ^ 2)⁻¹) := by ring
      _ ≤ Cbirth * ((records (ν k) (e k)).static (b k)).neck.scale :=
          mul_le_mul_of_nonneg_left (hmx.trans hs) hC.le
  linarith

/-- 原 X0 输出由 actual recent 闭合 / Original hNR interface with no SEPseq hypothesis. -/
theorem hNRprime_of_recent_supply_CXW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ),
    ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧ ∃ θbar : ℝ, 0 < θbar ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g),
        F.tower = S.tower → ∀ q : CutoffParameters,
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
        pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        Rn Γf ≤ pBase.modelRadius → mn Γf ≤ pBase.modelOrder →
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
          A.point e₂.succ (hf₂.trans e₂.castSucc_lt_succ.le) hl₂ := by
  obtain ⟨Csep, hCsep, _Pc, _Creset, Cbirth, _hPc, _hCreset, hCbirth, hG⟩ :=
    RetainedCoreHistory.nonResurgery_pair_of_tube_sep_C11SP.{u} (1 / 4) (by norm_num) (by norm_num)
  choose R _hDR m₀ _hm₀ ζ₀ δ₀ hζ₀ _hζhalf hδ₀ hnr using fun C : ℝ≥0 =>
    hG C (|StandardCap.transitionEnd| + 10) 1 1 (by positivity) one_pos one_pos 0
  refine ⟨fun Γf => R Γf.Ctime, fun Γf => m₀ Γf.Ctime, ?_⟩
  refine ⟨fun Γf => min (ζ₀ Γf.Ctime) (1 / 2),
    fun Γf => lt_min (hζ₀ Γf.Ctime) (by norm_num), 1 / 16, by norm_num, ?_⟩
  intro pBase Γf S F hT q hdiag hSUP haccSmall hrad hord hRm hmm params records
    h1 h2 h3 h4 h5 h6 h7 h8 B hB
  have hacc : pBase.modelAccuracy ≤ ζ₀ Γf.Ctime :=
    haccSmall.trans (min_le_left _ _)
  have hhalf : params.modelAccuracy ≤ 1 / 2 :=
    h3.le.trans (haccSmall.trans (min_le_right _ _))
  have hanti := neckRadius_antitone_of_chainDiagonal_C11SP S q hdiag
  have hparamsAnti : AntitoneOn params.neckRadius (Ici 0) := by
    intro s hs t ht hst
    rw [(h4 s hs).2, (h4 t ht).2]
    exact hanti hs ht hst
  have hseq := sepSeq_of_recent_CXW F params records h5 hhalf hparamsAnti h7 h8
  obtain ⟨TX, hTX, hsepX⟩ := sepRhoNR_of_sepRhoPlus_CXW (q := q)
    (fun ν t ht m => by
      filter_upwards [hseq ν t ht m, ht.eventually_ge_atTop 0] with k hk htk
      simpa only [(h4 (t k) htk).2] using hk) Cbirth hCbirth
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  have hρ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have hc4 := params.recenterConstant_ge_four
  obtain ⟨δK, hδK, hscaleLB⟩ := exists_uniform_static_cap_scale_lower_bound
    params.recenterConstant (q.neckRadius 0) (1 / a₀) (by linarith) hρ (by positivity)
  have hsq := Real.sqrt_nonneg (5 * Csep)
  have hK₂ : 0 < 8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) + 40000 +
      2 * params.recenterConstant := by
    have : 0 ≤ 8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) := by positivity
    linarith
  have hδs : 0 < min (min (δ₀ Γf.Ctime) δK) (1 / (8 * Real.sqrt (5 * Csep) *
      (|StandardCap.transitionEnd| + 10 + 1) + 40000 + 2 * params.recenterConstant)) :=
    lt_min (lt_min (hδ₀ Γf.Ctime) hδK) (by positivity)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp (h7.eventually (gt_mem_nhds hδs))
  refine ⟨max TX (T₁ + q.neckRadius 0 ^ 2 / (16 * B) + 1),
    lt_of_lt_of_le hTX (le_max_left _ _), ?_⟩
  intro n θ hθ hθB H t ht Q hQ a hat hwin y A hRA e₁ e₂ hf₁ hl₁ hf₂ hl₂ hlt hex b₂ z₂ hz₂a hz₂b
    hs₂
  obtain ⟨b, z, hz1, hz2, hanc, hsc⟩ := hex
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
  have hlate : ∀ s : ℝ, (a : ℝ) ≤ s → params.delta s < min (min (δ₀ Γf.Ctime) δK)
      (1 / (8 * Real.sqrt (5 * Csep) * (|StandardCap.transitionEnd| + 10 + 1) + 40000 +
        2 * params.recenterConstant)) := fun s hs => hT₁ s (ha_late.trans hs)
  have hδloc : ∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      params.delta (H.time i.succ) ≤ (δ₀ Γf.Ctime) := by
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
  have he₁t : H.time e₁.succ ≤ (t : ℝ) :=
    (H.time_strictMono.monotone hl₁).trans (H.activeStage_time_le t)
  have hθq : θ * ((records n e₁).static b).neck.scale ≤ Q / 4 := by
    have h1' : θ * ((records n e₁).static b).neck.scale ≤ θ * (4 * (B * Q)) :=
      mul_le_mul_of_nonneg_left hsc hθ.le
    have h2' : θ * (4 * (B * Q)) = 4 * (θ * B) * Q := by ring
    have h3' : 4 * (θ * B) * Q ≤ 4 * (1 / 16) * Q :=
      mul_le_mul_of_nonneg_right (by linarith) hQpos.le
    linarith
  have hage₁ : (t : ℝ) - H.time e₁.succ ≤ 1 / 4 * (((records n e₁).static b).neck.scale)⁻¹ := by
    have hθQ' : θ / Q ≤ 1 / 4 * (((records n e₁).static b).neck.scale)⁻¹ := by
      rw [div_le_iff₀ hQpos]
      have hq := ((records n e₁).static b).neck.scale_pos
      calc θ = θ * ((records n e₁).static b).neck.scale * (((records n e₁).static b).neck.scale)⁻¹
        := by
            field_simp
        _ ≤ Q / 4 * (((records n e₁).static b).neck.scale)⁻¹ :=
            mul_le_mul_of_nonneg_right hθq (inv_nonneg.mpr hq.le)
        _ = 1 / 4 * (((records n e₁).static b).neck.scale)⁻¹ * Q := by ring
    linarith
  have hsepI := hsepX n t ((le_max_left _ _).trans ht) e₁ b he₁t hage₁
  obtain ⟨W, hW, htube, hderivW, hfinalW⟩ := xclauses_of_supply_sep_P6XS F q params Γf.Ctime hSUP
    hanti records Cbirth (R Γf.Ctime) n t e₁ e₂ b hte₂ hsepI
  have hmain := hnr Γf.Ctime (F.tower.history n) (records n) (fun i b' => h5 n i b')
    (hRm.trans h1.ge) (hmm.trans h2.ge) (h3.le.trans hacc)
    (Cbirth * ((records n e₁).static b).neck.scale) a₀ B Q θ (by positivity) hQpos hθ.le hBθ hB16
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) e₁ e₂ hl
    ((H.time e₂.castSucc + H.time e₂.succ) / 2) ht' (A.point e₂.castSucc hf₂ hc₂)
    ((A.restrictLast hf₂ hc₂).restrictFirst hs₁ hl) b z hanc.symm hage hsc hxD le_rfl haq hδloc
    hT2 hδ2 W hW htube hderivW
    (fun x' hx' τ hτ hR => hfinalW x' hx' τ ⟨hτ.1, hτ.2.trans ht'.2⟩ hR)
  exact hmain (A.point e₂.succ (hf₂.trans Fin.castSucc_lt_succ.le) hl₂) (A.crossing e₂ hf₂ hl₂)
    b₂ z₂ hz₂a hz₂b hs₂

end GC.LongTime.Ch11
