import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedRecenterPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KRouteBridgeP6JA

/-!
# J10GEN2A G5：R1 修复——合同 seed 的 `hsmall@Tn` ⇒ E 帧 `hsmall@σ`（O-CH11-J10GEN2A，后缀 `_P6JA`）

R1：E 帧 horizon = `ts` 迫使 `Tn^E = ts`，J10WIRE (B) 族的 `hsmall` / `hclock` 落在选点 σ；合同只给
`hsmall@(Tn, pT, 1)`、`aSeed = Tn − 1`、`Tn − 1/2 ≤ σ`。本文件（lead 23:4x 裁定方案 (a)）：
* `GC.LongTime.hasSmallParabolicCurvature_shift_P6JA`（PROVED）：`hsmall@(T, p, r)` + seed clock
  `aSeed = T − r²` + seedTrace ⇒ 对 `v ∈ [T − r²/2, T]`，`hsmall@(v, seedTrace 点@v, r/100)`。证明 = 树内
  `hasSmallParabolicCurvature.earlier_seed_on_half_depth`（`ParabolicSeedRecenterPortC11P`）的
  hsmall 半逐字
  （不需要其 `hvolume` / `htime` / `1 < A`；trace 位移界由私有
  `exists_past_seed_core_traces_of_metric_distortion` 的度量畸变 `exp(2·(3/r²)·(r²/2)) ≤ 10²` 给出）；
* `hsmall_of_eventPrefix_P6JA`（PROVED）：K 层 `hsmall@(τ', p', r)` ⇒ event 帧 E 层 `hsmall@(τ, p, r)`
  （K trace 按 `Fin.castLE` 限制到 E，`isRmControlled` 两部分逐指标搬运）；
* `exists_seed_hsmall_eventPrefix_P6JA`（PROVED）：合同 seed（`hsmall@(Tn, pT, r)`、`aSeed = Tn − r²`、
  `Tn − r²/2 ≤ σ ≤ Tn`）⇒ **∃** 兼容 E seed（`Tn^E := ts`、起点 `aE := σ − (r/100)²`）满足 G1 的 `haa` /
  `hseed` **且** (B) 族 `hsmall@(ts, pT^E, r/100)` / `hclock : aE = ts − (r/100)²`。常数：`rX := r/100`
  （合同 `r = 1` ⇒ `rX = 1/100 ≤ 1/√2`）；
* final 截断帧孪生 `hsmall_final_P6JA` / `exists_seed_hsmall_final_P6JA`（`gen_h.py` 由 event 段变换）；
* 序列形 `exists_seedSeq_hsmall_{eventPrefix,final}_P6JA`（`choose`）：G2 twins / 合成 driver 的
  `haa` / `hseedC` / `hsmall` / `hclock` 四个 binder 由合同 seed 付清（`Tn^E := ts`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold NNReal Topology ContDiff ENNReal

open private ObservedHistory.exists_past_seed_core_traces_of_metric_distortion from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicSeedRicciPortC11P

namespace GC.LongTime

universe u

/-- **G5-1（`_P6JA`，PROVED）**：强 seed `hsmall@(T, p, r)`（clock `aSeed = T − r²`）沿 seedTrace 平移到
后半深度任一时刻 `v ∈ [T − r²/2, T]`：`hsmall@(v, seedTrace 点@v, r/100)`。
`hasSmallParabolicCurvature.earlier_seed_on_half_depth` 的 hsmall 半逐字（去掉体积 / `htime` / `A`）。 -/
theorem hasSmallParabolicCurvature_shift_P6JA
    {H : ObservedHistory.{u}} {T aSeed : Icc (0 : ℝ) H.horizon}
    (haT : aSeed ≤ T) (p : (H.stageAt T).Carrier) (r : ℝ)
    (hclock : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (hseed : hasSmallParabolicCurvature H T p r)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
    (hv : (T : ℝ) - r ^ 2 / 2 ≤ (v : ℝ)) :
    hasSmallParabolicCurvature H v
      (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvT))
      (r / 100) := by
  classical
  have hr : 0 < r := hseed.1
  have hR : 0 < r / 100 := by positivity
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  have hball : H.isParabolicallyRmControlledBall T p r := by
    obtain ⟨_hr, a, hat, ha, htraces⟩ := hseed
    refine ⟨hr, a, hat, ha, ?_⟩
    intro x hx
    obtain ⟨A, hA⟩ := htraces x hx
    have hpow : r ^ 4 ≤ (Real.sqrt 3 * r) ^ 4 := pow_le_pow_left₀ hr.le hrr 4
    refine ⟨A, ?_, ?_⟩
    · intro u hau hut
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hA.1 u hau hut)
    · intro i hi hl
      exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans
        (hA.2 i hi hl)
  let clock : ℝ := Real.sqrt ((T : ℝ) - v)
  have hclockNonneg : 0 ≤ clock := Real.sqrt_nonneg _
  have hclockSq : clock ^ 2 = (T : ℝ) - v := Real.sq_sqrt (sub_nonneg.mpr hvT)
  have hclockLe : clock ≤ r := (sq_le_sq₀ hclockNonneg hr.le).mp (by
    rw [hclockSq]
    nlinarith [sq_nonneg r])
  have hclockEq : (v : ℝ) = (T : ℝ) - clock ^ 2 := by rw [hclockSq]; ring
  have hratio : clock ^ 2 / r ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hclockSq]
    linarith
  have hdistortion : Real.exp (2 * (3 / r ^ 2) * clock ^ 2) ≤ (10 : ℝ) ^ 2 := by
    have hcoef : 2 * (3 / r ^ 2) * clock ^ 2 ≤ 3 := by
      calc
        _ = 6 * (clock ^ 2 / r ^ 2) := by ring
        _ ≤ 6 * (1 / 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 3 := by norm_num
    have heq : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = (1 + 1) + 1 by norm_num, Real.exp_add, Real.exp_add]
      ring
    have he2 : (Real.exp 1) ^ 2 < 9 := by
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have he3 : (Real.exp 1) ^ 3 < 27 := by
      have hmul := mul_lt_mul_of_pos_right he2 (Real.exp_pos 1)
      have hnine := mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num : (0 : ℝ) < 9)
      nlinarith only [hmul, hnine]
    refine le_of_lt ?_
    calc
      _ ≤ Real.exp 3 := Real.exp_le_exp.mpr hcoef
      _ < 27 := by rwa [heq]
      _ ≤ (10 : ℝ) ^ 2 := by norm_num
  have hmargin : r / 100 < (3 * r / 4) / (10 : ℝ) := by linarith
  obtain ⟨b0, hb0v, hb0, htraces⟩ :=
    ObservedHistory.exists_past_seed_core_traces_of_metric_distortion H T v hvT p r clock
      hball hclockNonneg hclockLe hclockEq
      (seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT))
      (r / 100) 10 (by norm_num) hdistortion hmargin
  have hb0a : b0 = aSeed := Subtype.ext (hb0.trans hclock.symm)
  subst b0
  have hstart : (aSeed : ℝ) ≤ (v : ℝ) - (r / 100) ^ 2 := by
    rw [hclock]
    nlinarith [sq_nonneg r]
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(v : ℝ) - (r / 100) ^ 2, aSeed.property.1.trans hstart,
      (sub_le_self _ (sq_nonneg (r / 100))).trans v.property.2⟩
  have hab : aSeed ≤ b := hstart
  have hbv : b ≤ v := sub_le_self _ (sq_nonneg (r / 100))
  have hstrongScale : Real.sqrt 3 * (r / 100) ≤ r := by
    have hsqrtLe : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right hsqrtLe hr.le]
  refine ⟨hR, b, hbv, rfl, ?_⟩
  intro y hy
  have hphysical : riemannianEDistOf
      (H.stageMetric (H.activeStage v) ((T : ℝ) - clock ^ 2))
      ((seedTrace.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvT)).point
        (H.activeStage v) le_rfl (H.activeStage_mono hvT)) y < ENNReal.ofReal (r / 100) := by
    rw [← hclockEq]
    exact hy
  obtain ⟨A, hA⟩ := htraces y hphysical
  exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbv),
    hA.restrictFirst A (by positivity) hstrongScale hab hbv⟩

end GC.LongTime

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **G5-2（`_P6JA`，PROVED）**：K 层 `hsmall@(τ', p', r)` ⇒ event 帧 E 层 `hsmall@(τ, p, r)`（同实时刻、
`HEq` 点）：K 的 controlled trace 按 `Fin.castLE` 限制到 E（端点 = 原点），`isRmControlled` 的 slab 部分经
`eventPrefix_stageMetric` + 指标 `subst` 搬运，seam 部分定义等。 -/
theorem hsmall_of_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {r : ℝ}
    (h : GC.LongTime.hasSmallParabolicCurvature K.toHistory τ' p' r) :
    GC.LongTime.hasSmallParabolicCurvature E τ p r := by
  subst hE
  obtain ⟨hr, a', hat', ha', htr⟩ := h
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  have haH : (a' : ℝ) ≤ (K.eventPrefix j T hjT hTj).toHistory.horizon := by
    have h0 : (a' : ℝ) ≤ τ' := hat'
    have h1 : (τ' : ℝ) ≤ (K.eventPrefix j T hjT hTj).toHistory.horizon := by
      rw [← hττ]
      exact τ.2.2
    exact h0.trans h1
  let a : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon := ⟨a', a'.2.1, haH⟩
  have hat : a ≤ τ := show (a' : ℝ) ≤ τ from by rw [hττ]; exact hat'
  have hva : (K.toHistory.activeStage a').val =
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage a).val :=
    (K.eventPrefix_activeStage_val j hjT hTj a a' rfl).symm
  have hvt : (K.toHistory.activeStage τ').val =
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val :=
    (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ).symm
  have hidxτ : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext hvt.symm
  have hfL : ∀ m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1),
      (K.eventPrefix j T hjT hTj).toHistory.activeStage a ≤ m →
      K.toHistory.activeStage a' ≤
        Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m :=
    fun m hf => Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ m.val from by
      have := Fin.le_iff_val_le_val.mp hf
      omega)
  have hlL : ∀ m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1),
      m ≤ (K.eventPrefix j T hjT hTj).toHistory.activeStage τ →
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m ≤
        K.toHistory.activeStage τ' :=
    fun m hl => Fin.le_iff_val_le_val.mpr (show m.val ≤ (K.toHistory.activeStage τ').val from by
      have := Fin.le_iff_val_le_val.mp hl
      omega)
  refine ⟨hr, a, hat, show (a' : ℝ) = (τ : ℝ) - r ^ 2 from by rw [hττ]; exact ha', fun x hx => ?_⟩
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidxτ) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx r hx
  obtain ⟨A', hA'⟩ := htr x' hx'
  let A : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage a)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat) x :=
    { point := fun m hf hl =>
        A'.point (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m)
          (hfL m hf) (hlL m hl)
      endpoint_eq := by
        have e1 := RetainedCoreHistory.point_heq_P6JA A' hidxτ
          (hfL _ ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat)) (hlL _ le_rfl)
          (K.toHistory.activeStage_mono hat') le_rfl
        exact eq_of_heq (e1.trans ((heq_of_eq A'.endpoint_eq).trans hxx.symm))
      crossing := fun i hf hl =>
        A'.crossing (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
          (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ i.val from by
            have := Fin.le_iff_val_le_val.mp hf
            simp only [Fin.val_castSucc] at this
            omega))
          (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage τ').val from by
            have := Fin.le_iff_val_le_val.mp hl
            simp only [Fin.val_succ] at this
            omega)) }
  refine ⟨A, ?_, ?_⟩
  · intro s has hst
    let s' : Icc (0 : ℝ) K.toHistory.horizon := ⟨s, s.2.1, s.2.2.trans hTH⟩
    have has' : a' ≤ s' := show (a' : ℝ) ≤ s from has
    have hst' : s' ≤ τ' := show (s : ℝ) ≤ τ' from hττ ▸ hst
    have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) = K.toHistory.activeStage s' :=
      Fin.ext (K.eventPrefix_activeStage_val j hjT hTj s s' rfl)
    have hP := RetainedCoreHistory.pt_index_P6JA K.toHistory
      (fun m pt => (Real.sqrt 3 * r) ^ 4 * normSq0S (K.toHistory.stageMetric m s) pt 4
        (metricRm04At (K.toHistory.stageMetric m s) pt) ≤ 1) hidx
      (RetainedCoreHistory.point_heq_P6JA A' hidx
        (hfL _ ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono has))
        (hlL _ ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hst))
        (K.toHistory.activeStage_mono has') (K.toHistory.activeStage_mono hst'))
      (hA'.1 s' has' hst')
    have hmet := K.eventPrefix_stageMetric j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) s
    rw [hmet]
    exact hP
  · intro i hf hl
    exact hA'.2 (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ i.val from by
        have := Fin.le_iff_val_le_val.mp hf
        simp only [Fin.val_castSucc] at this
        omega))
      (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage τ').val from by
        have := Fin.le_iff_val_le_val.mp hl
        simp only [Fin.val_succ] at this
        omega))


/-- **G5-3（`_P6JA`，PROVED）**：合同 seed（K 帧：`hsmall@(TnK, pTK, r)`、clock `aK = TnK − r²`、seedTrace、
选点 `τ' ∈ [TnK − r²/2, TnK]`）⇒ **∃** event 帧 E seed（`Tn^E := τ`、起点 `aE = τ − (r/100)²`、端点 `pTE`）
满足 G1 桥的兼容前提（`aK ≤ aE`、`hseed`）**且** J10WIRE (B) 族的 `hsmall@(τ, pTE, r/100)` 与
`hclock : aE = τ − (r/100)²`。合同 `r = 1` ⇒ `rX = 1/100`。 -/
theorem exists_seed_hsmall_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    {r : ℝ} (hclockK : (aK : ℝ) = (TnK : ℝ) - r ^ 2)
    (hsmallK : GC.LongTime.hasSmallParabolicCurvature K.toHistory TnK pTK r)
    (hhalf : (TnK : ℝ) - r ^ 2 / 2 ≤ τ') :
    ∃ (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (pTE : (E.stageAt τ).Carrier)
      (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
        (E.activeStage_mono haTE) pTE),
      (aK : ℝ) ≤ aE ∧
      (∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon), (v : ℝ) = v' →
        ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
          (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
          (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
          HEq (seedE.point (E.activeStage v) h1 h2)
            (seedK.point (K.toHistory.activeStage v') h1' h2')) ∧
      GC.LongTime.hasSmallParabolicCurvature E τ pTE (r / 100) ∧
      (aE : ℝ) = (τ : ℝ) - (r / 100) ^ 2 := by
  have ha1 : (aK : ℝ) ≤ (τ : ℝ) - (r / 100) ^ 2 := by
    rw [hclockK, hττ]
    nlinarith [sq_nonneg r]
  have ha2 : (τ : ℝ) - (r / 100) ^ 2 ≤ τ := sub_le_self _ (sq_nonneg _)
  obtain ⟨aE, haTE, pTE, seedE, haa, hseed⟩ :=
    K.exists_seed_eventPrefix_P6JA j hjT hTj E hE τ τ' hττ TnK aK haTK hsTK pTK seedK _ ha1 ha2
  have hsh := GC.LongTime.hasSmallParabolicCurvature_shift_P6JA haTK pTK r hclockK hsmallK seedK
    τ' hasK hsTK hhalf
  have hp : HEq pTE (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) :=
    (heq_of_eq seedE.endpoint_eq).symm.trans
      (hseed τ τ' hττ (E.activeStage_mono haTE) le_rfl (K.toHistory.activeStage_mono hasK)
        (K.toHistory.activeStage_mono hsTK))
  exact ⟨aE, haTE, pTE, seedE, ha1.trans_eq haa.symm, hseed,
    K.hsmall_of_eventPrefix_P6JA j hjT hTj E hE τ τ' hττ pTE _ hp hsh, haa⟩



/-! ### final 帧（`gen_h.py` 生成） -/

/-- **G5-2f（`_P6JA`，PROVED）**：K 层 `hsmall@(τ', p', r)` ⇒ final 截断帧 E 层 `hsmall@(τ, p, r)`（同实时刻、
`HEq` 点）：K 的 controlled trace 限制到 E（指标同型）（端点 = 原点），`isRmControlled` 的 slab 部分经
`stageMetric_final_P6M` + 指标 `subst` 搬运，seam 部分定义等。 -/
theorem hsmall_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E =
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : (E.stageAt τ).Carrier) (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {r : ℝ}
    (h : GC.LongTime.hasSmallParabolicCurvature K.toHistory τ' p' r) :
    GC.LongTime.hasSmallParabolicCurvature E τ p r := by
  subst hE
  obtain ⟨hr, a', hat', ha', htr⟩ := h
  have hTH : T ≤ K.horizon := hTs.le
  have haH : (a' : ℝ) ≤ ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.horizon := by
    have h0 : (a' : ℝ) ≤ τ' := hat'
    have h1 : (τ' : ℝ) ≤ ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.horizon := by
      rw [← hττ]
      exact τ.2.2
    exact h0.trans h1
  let a : Icc (0 : ℝ) ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.horizon := ⟨a', a'.2.1, haH⟩
  have hat : a ≤ τ := show (a' : ℝ) ≤ τ from by rw [hττ]; exact hat'
  have hva : (K.toHistory.activeStage a').val =
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage a).val :=
    (K.activeStage_val_final_P6M hfin hT hTs a a' rfl).symm
  have hvt : (K.toHistory.activeStage τ').val =
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ).val :=
    (K.activeStage_val_final_P6M hfin hT hTs τ τ' hττ).symm
  have hidxτ := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hfL : ∀ m : Fin (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.eventCount + 1),
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage a ≤ m →
      K.toHistory.activeStage a' ≤
        m :=
    fun m hf => Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ m.val from by
      have := Fin.le_iff_val_le_val.mp hf
      omega)
  have hlL : ∀ m : Fin (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.eventCount + 1),
      m ≤ ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ →
      m ≤
        K.toHistory.activeStage τ' :=
    fun m hl => Fin.le_iff_val_le_val.mpr (show m.val ≤ (K.toHistory.activeStage τ').val from by
      have := Fin.le_iff_val_le_val.mp hl
      omega)
  refine ⟨hr, a, hat, show (a' : ℝ) = (τ : ℝ) - r ^ 2 from by rw [hττ]; exact ha', fun x hx => ?_⟩
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidxτ) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ p x p' x' hp hxx r hx
  obtain ⟨A', hA'⟩ := htr x' hx'
  let A : BackwardPointTrace ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage a)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hat) x :=
    { point := fun m hf hl =>
        A'.point (m)
          (hfL m hf) (hlL m hl)
      endpoint_eq := by
        have e1 := RetainedCoreHistory.point_heq_P6JA A' hidxτ
          (hfL _ (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
              ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
              hTs).toHistory.activeStage_mono hat)) (hlL _ le_rfl)
          (K.toHistory.activeStage_mono hat') le_rfl
        exact eq_of_heq (e1.trans ((heq_of_eq A'.endpoint_eq).trans hxx.symm))
      crossing := fun i hf hl =>
        A'.crossing i
          (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ i.val from by
            have := Fin.le_iff_val_le_val.mp hf
            simp only [Fin.val_castSucc] at this
            omega))
          (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage τ').val from by
            have := Fin.le_iff_val_le_val.mp hl
            simp only [Fin.val_succ] at this
            omega)) }
  refine ⟨A, ?_, ?_⟩
  · intro s has hst
    let s' : Icc (0 : ℝ) K.toHistory.horizon := ⟨s, s.2.1, s.2.2.trans hTH⟩
    have has' : a' ≤ s' := show (a' : ℝ) ≤ s from has
    have hst' : s' ≤ τ' := show (s : ℝ) ≤ τ' from hττ ▸ hst
    have hidx := K.activeStage_final_P6M hfin hT hTs s s' rfl
    have hP := RetainedCoreHistory.pt_index_P6JA K.toHistory
      (fun m pt => (Real.sqrt 3 * r) ^ 4 * normSq0S (K.toHistory.stageMetric m s) pt 4
        (metricRm04At (K.toHistory.stageMetric m s) pt) ≤ 1) hidx
      (RetainedCoreHistory.point_heq_P6JA A' hidx
        (hfL _ (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
            ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
            hTs).toHistory.activeStage_mono has))
        (hlL _ (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
            ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
            hTs).toHistory.activeStage_mono hst))
        (K.toHistory.activeStage_mono has') (K.toHistory.activeStage_mono hst'))
      (hA'.1 s' has' hst')
    have hmet := K.stageMetric_final_P6M hfin hT hTs
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage s) s
    rw [hmet]
    exact hP
  · intro i hf hl
    exact hA'.2 i
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage a').val ≤ i.val from by
        have := Fin.le_iff_val_le_val.mp hf
        simp only [Fin.val_castSucc] at this
        omega))
      (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage τ').val from by
        have := Fin.le_iff_val_le_val.mp hl
        simp only [Fin.val_succ] at this
        omega))


/-- **G5-3f（`_P6JA`，PROVED）**：合同 seed（K 帧：`hsmall@(TnK, pTK, r)`、clock `aK = TnK − r²`、seedTrace、
选点 `τ' ∈ [TnK − r²/2, TnK]`）⇒ **∃** final 截断帧 E seed（`Tn^E := τ`、起点 `aE = τ − (r/100)²`、端点 `pTE`）
满足 G1 桥的兼容前提（`aK ≤ aE`、`hseed`）**且** J10WIRE (B) 族的 `hsmall@(τ, pTE, r/100)` 与
`hclock : aE = τ − (r/100)²`。合同 `r = 1` ⇒ `rX = 1/100`。 -/
theorem exists_seed_hsmall_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E =
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    {r : ℝ} (hclockK : (aK : ℝ) = (TnK : ℝ) - r ^ 2)
    (hsmallK : GC.LongTime.hasSmallParabolicCurvature K.toHistory TnK pTK r)
    (hhalf : (TnK : ℝ) - r ^ 2 / 2 ≤ τ') :
    ∃ (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (pTE : (E.stageAt τ).Carrier)
      (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
        (E.activeStage_mono haTE) pTE),
      (aK : ℝ) ≤ aE ∧
      (∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon), (v : ℝ) = v' →
        ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
          (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
          (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
          HEq (seedE.point (E.activeStage v) h1 h2)
            (seedK.point (K.toHistory.activeStage v') h1' h2')) ∧
      GC.LongTime.hasSmallParabolicCurvature E τ pTE (r / 100) ∧
      (aE : ℝ) = (τ : ℝ) - (r / 100) ^ 2 := by
  have ha1 : (aK : ℝ) ≤ (τ : ℝ) - (r / 100) ^ 2 := by
    rw [hclockK, hττ]
    nlinarith [sq_nonneg r]
  have ha2 : (τ : ℝ) - (r / 100) ^ 2 ≤ τ := sub_le_self _ (sq_nonneg _)
  obtain ⟨aE, haTE, pTE, seedE, haa, hseed⟩ :=
    K.exists_seed_final_P6JA hfin hT hTs E hE τ τ' hττ TnK aK haTK hsTK pTK seedK _ ha1 ha2
  have hsh := GC.LongTime.hasSmallParabolicCurvature_shift_P6JA haTK pTK r hclockK hsmallK seedK
    τ' hasK hsTK hhalf
  have hp : HEq pTE (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) :=
    (heq_of_eq seedE.endpoint_eq).symm.trans
      (hseed τ τ' hττ (E.activeStage_mono haTE) le_rfl (K.toHistory.activeStage_mono hasK)
        (K.toHistory.activeStage_mono hsTK))
  exact ⟨aE, haTE, pTE, seedE, ha1.trans_eq haa.symm, hseed,
    K.hsmall_final_P6JA hfin hT hTs E hE τ τ' hττ pTE _ hp hsh, haa⟩


end RetainedCoreHistory


namespace ObservedHistory

/-- **G5-4（`_P6JA`，PROVED；序列，event 帧）**：合同 seed 族 ⇒ 存在 E seed 族（`Tn^E := ts`）满足 G2 twins 的
`haa` / `hseedC` 与 J10WIRE (B) 族的 `hsmall` / `hclock`（`rX := r/100`）——twins 的这四个 binder 由合同付清。 -/
theorem exists_seedSeq_hsmall_eventPrefix_P6JA {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    {hjt : ∀ n, (K n).time (j n).castSucc < t n} {htj : ∀ n, t n < (K n).time (j n).succ}
    {Hs : ℕ → ObservedHistory.{u}}
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    (hσ : ∀ n, (ts n : ℝ) = σ n)
    (TnK aK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haTK : ∀ n, aK n ≤ TnK n)
    (hsTK : ∀ n, σ n ≤ TnK n) (hasK : ∀ n, aK n ≤ σ n)
    (pTK : ∀ n, ((K n).toHistory.stageAt (TnK n)).Carrier)
    (seedK : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aK n))
      ((K n).toHistory.activeStage (TnK n)) ((K n).toHistory.activeStage_mono (haTK n)) (pTK n))
    {r : ℝ} (hclockK : ∀ n, (aK n : ℝ) = (TnK n : ℝ) - r ^ 2)
    (hsmallK : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (TnK n) (pTK n) r)
    (hhalf : ∀ n, (TnK n : ℝ) - r ^ 2 / 2 ≤ σ n) :
    ∃ (aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTE : ∀ n, aE n ≤ ts n)
      (pTE : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (haTE n)) (pTE n)),
      (∀ n, (aK n : ℝ) ≤ aE n) ∧
      (∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
        (v : ℝ) = v' →
        ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
          (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (ts n))
          (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
          (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
          HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
            ((seedK n).point ((K n).toHistory.activeStage v') h1' h2')) ∧
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (ts n) (pTE n) (r / 100)) ∧
      (∀ n, (aE n : ℝ) = (ts n : ℝ) - (r / 100) ^ 2) := by
  choose aE haTE pTE seedE h using fun n =>
    (K n).exists_seed_hsmall_eventPrefix_P6JA (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n)
      (hσ n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n) (hclockK n) (hsmallK n)
      (hhalf n)
  exact ⟨aE, haTE, pTE, seedE, fun n => (h n).1, fun n => (h n).2.1, fun n => (h n).2.2.1,
    fun n => (h n).2.2.2⟩

/-- **G5-4f（`_P6JA`，PROVED；序列，final 截断帧）**：同 G5-4。 -/
theorem exists_seedSeq_hsmall_final_P6JA {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    {htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n} {htK : ∀ n, t n < (K n).horizon}
    {Hs : ℕ → ObservedHistory.{u}}
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    (hσ : ∀ n, (ts n : ℝ) = σ n)
    (TnK aK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haTK : ∀ n, aK n ≤ TnK n)
    (hsTK : ∀ n, σ n ≤ TnK n) (hasK : ∀ n, aK n ≤ σ n)
    (pTK : ∀ n, ((K n).toHistory.stageAt (TnK n)).Carrier)
    (seedK : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aK n))
      ((K n).toHistory.activeStage (TnK n)) ((K n).toHistory.activeStage_mono (haTK n)) (pTK n))
    {r : ℝ} (hclockK : ∀ n, (aK n : ℝ) = (TnK n : ℝ) - r ^ 2)
    (hsmallK : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (TnK n) (pTK n) r)
    (hhalf : ∀ n, (TnK n : ℝ) - r ^ 2 / 2 ≤ σ n) :
    ∃ (aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTE : ∀ n, aE n ≤ ts n)
      (pTE : ∀ n, ((Hs n).stageAt (ts n)).Carrier)
      (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
        ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (haTE n)) (pTE n)),
      (∀ n, (aK n : ℝ) ≤ aE n) ∧
      (∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
        (v : ℝ) = v' →
        ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
          (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (ts n))
          (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
          (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
          HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
            ((seedK n).point ((K n).toHistory.activeStage v') h1' h2')) ∧
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (ts n) (pTE n) (r / 100)) ∧
      (∀ n, (aE n : ℝ) = (ts n : ℝ) - (r / 100) ^ 2) := by
  choose aE haTE pTE seedE h using fun n =>
    (K n).exists_seed_hsmall_final_P6JA ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n)
      (ts n) (σ n) (hσ n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n)
      (hclockK n) (hsmallK n) (hhalf n)
  exact ⟨aE, haTE, pTE, seedE, fun n => (h n).1, fun n => (h n).2.1, fun n => (h n).2.2.1,
    fun n => (h n).2.2.2⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
