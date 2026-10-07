import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixHdistC11G2

/-!
# traced region 与 E 层数据沿 `K.eventPrefix j T`（S-CH11-HDISTC G0 底层，后缀 `_C11G3`）

P6PFX 的 K 层 `hdist` 经 `Hs := K.eventPrefix j T` 的 E 层 `hscal`；而 P6CE
`exists_hscal_of_isTracedRegion_P6E` 需要 **E 层** traced region。本文件补两块：
* `isTracedRegion_eventPrefix_C11G3`：**K → E** 的 traced region 搬运（同一实时刻 `τ ≤ T`、`HEq` 中心、
  半径 / 深度 / 曲率界不变；`E → K` 方向树内已有 `isTracedRegion_of_eventPrefix_P6M`）。证法 = P6PFX
  `hasSmallParabolicCurvature_eventPrefix_C11G2`（K0 搬运）同款：球成员 `mem_ball_of_eventPrefix_P6M`、trace 限制
  `exists_eventPrefixTrace_C11G2`、`isRmBoundedBy` 逐 stage / 逐 event 搬运。
* `exists_eventPrefixData_C11G3`：K 层种子数据 `(σ, aSeed, Tn, pT, y, seedTrace)`（`Tn ≤ T`）⇒ E 层数据
  `(sE, aE, Te, pe, yE, seedE)`，满足 `hdist_Kdata_pointwise_eventPrefix_C11G2` 要的全部关系
  （实时刻相等、`HEq` 中心、种子 trace 逐点相等）。序列层用 `choose` 取出。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- stage 指标推广：`‖Rm‖² ≤ C²` 在两种指标写法间搬运（`_C11G3`）。 -/
private theorem rm_sq_bound_congr_C11G3 {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (B : BackwardPointTrace H first last hle x) {m m' : Fin (H.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v C : ℝ)
    (h : normSq0S (H.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (H.stageMetric m' v) (B.point m' h1' h2')) ≤ C ^ 2) :
    normSq0S (H.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (H.stageMetric m v) (B.point m h1 h2)) ≤ C ^ 2 := by
  subst hm
  exact h

/-- **traced region 沿 eventPrefix（K → E，`_C11G3`）**：K 的 traced region `(ρ, δ, C)`（时刻 `τ'`、
中心 `p'`）⇒ E 的同形（同一实时刻 `τ ≤ T`、`HEq` 中心）。 -/
theorem isTracedRegion_eventPrefix_C11G3 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (τ : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (p : ((K.eventPrefix j T hjT hTj).toHistory.stageAt τ).Carrier)
    (p' : (K.toHistory.stageAt τ').Carrier) (hp : HEq p p') {ρ δ C : ℝ}
    (h : K.toHistory.isTracedRegion τ' p' ρ δ C) :
    (K.eventPrefix j T hjT hTj).toHistory.isTracedRegion τ p ρ δ C := by
  obtain ⟨hρ, hδ, a', hat', hclock', htr⟩ := h
  have hτT : (τ : ℝ) ≤ T := τ.2.2
  have ha'T : (a' : ℝ) ≤ T :=
    (show (a' : ℝ) ≤ τ' from hat').trans (by rw [← hττ]; exact hτT)
  let a : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon := ⟨a', a'.2.1, ha'T⟩
  have hat : a ≤ τ := show (a' : ℝ) ≤ τ by rw [hττ]; exact hat'
  refine ⟨hρ, hδ, a, hat, ?_, ?_⟩
  · change (a' : ℝ) = (τ : ℝ) - δ
    rw [hττ]
    exact hclock'
  intro x hx
  have hAτ := K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ
  have hAa := K.eventPrefix_activeStage_val j hjT hTj a a' rfl
  have hl : K.toHistory.activeStage τ' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) := Fin.ext hAτ.symm
  have hf : K.toHistory.activeStage a' = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage a) := Fin.ext hAa.symm
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hl.symm) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ p x p' x' hp hxx ρ hx
  obtain ⟨A', hA'⟩ := htr x' hx'
  obtain ⟨A, hApt⟩ := K.exists_eventPrefixTrace_C11G2 j hjT hTj hf hl
    (hle := (K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat)
    (hle' := K.toHistory.activeStage_mono hat') hxx A'
  refine ⟨A, ?_, ?_⟩
  · intro s has hst
    have hsT : (s : ℝ) ≤ T := s.2.2
    have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
    let s' : Icc (0 : ℝ) K.toHistory.horizon := ⟨s, s.2.1, hsT.trans hTH⟩
    have hAs := K.eventPrefix_activeStage_val j hjT hTj s s' rfl
    have hs : K.toHistory.activeStage s' = K.eIdx_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) := Fin.ext hAs.symm
    have h1' : a' ≤ s' := show (a' : ℝ) ≤ s from has
    have h2' : s' ≤ τ' := show (s : ℝ) ≤ τ' by rw [← hττ]; exact hst
    have hb := hA'.1 s' h1' h2'
    have hM1 : K.toHistory.activeStage a' ≤ K.eIdx_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) :=
      hf.le.trans (K.eIdx_mono_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono has))
    have hM2 : K.eIdx_C11G2 j hjT hTj ((K.eventPrefix j T hjT hTj).toHistory.activeStage s) ≤
        K.toHistory.activeStage τ' :=
      (K.eIdx_mono_C11G2 j hjT hTj
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hst)).trans hl.symm.le
    have hb' := rm_sq_bound_congr_C11G3 A' hs hM1 hM2
      (K.toHistory.activeStage_mono h1') (K.toHistory.activeStage_mono h2') s C hb
    rw [hApt _ ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono has)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hst) hM1 hM2,
      K.eventPrefix_stageMetric j hjT hTj]
    exact hb'
  · intro i hfi hli
    let i' : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i
    have hfK : K.toHistory.activeStage a' ≤ i'.castSucc :=
      hf.le.trans (K.eIdx_mono_C11G2 j hjT hTj hfi)
    have hlK : i'.succ ≤ K.toHistory.activeStage τ' :=
      (K.eIdx_mono_C11G2 j hjT hTj hli).trans hl.symm.le
    have hb := hA'.2 i' hfK hlK
    have hpt : A.point i.castSucc hfi (i.castSucc_lt_succ.le.trans hli) =
        A'.point i'.castSucc hfK (i'.castSucc_lt_succ.le.trans hlK) :=
      hApt _ hfi (i.castSucc_lt_succ.le.trans hli) hfK (i'.castSucc_lt_succ.le.trans hlK)
    intro x
    have hx : x = ⟨A'.point i'.castSucc hfK (i'.castSucc_lt_succ.le.trans hlK),
        (A'.crossing i' hfK hlK).mem_terminalRegularRegion (K.toHistory.event i')⟩ :=
      Subtype.ext hpt
    rw [hx]
    exact hb

/-- **E 层数据（`_C11G3`）**：K 层种子数据 `(σ, aSeed, Tn, pT, y, seedTrace)`，`(Tn : ℝ) ≤ T`
（K0 种子时刻在 prefix 的 horizon `T` 之内）⇒ E 层 `(sE, aE, Te, pe, yE, seedE)`，与
`hdist_Kdata_pointwise_eventPrefix_C11G2` / uniform 版要的关系逐字一致：实时刻相等、`HEq` 中心、
种子 trace 逐点相等（stage 指标 `eIdx`）。 -/
theorem exists_eventPrefixData_C11G3 (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    {σ aSeed Tn : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) (hTt : (Tn : ℝ) ≤ T) {pT : (K.toHistory.stageAt Tn).Carrier}
    (y : (K.toHistory.stageAt σ).Carrier)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT) :
    ∃ (Te aE sE : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
      (haTe : aE ≤ Te) (_hsTe : sE ≤ Te) (_hasE : aE ≤ sE)
      (pe : ((K.eventPrefix j T hjT hTj).toHistory.stageAt Te).Carrier)
      (yE : ((K.eventPrefix j T hjT hTj).toHistory.stageAt sE).Carrier)
      (seedE : BackwardPointTrace (K.eventPrefix j T hjT hTj).toHistory
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage aE)
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage Te)
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono haTe) pe),
      (sE : ℝ) = σ ∧ (aE : ℝ) = aSeed ∧ (Te : ℝ) = Tn ∧ HEq yE y ∧ HEq pe pT ∧
      (∀ (m : Fin ((K.eventPrefix j T hjT hTj).toHistory.eventCount + 1))
        (h1 : (K.eventPrefix j T hjT hTj).toHistory.activeStage aE ≤ m)
        (h2 : m ≤ (K.eventPrefix j T hjT hTj).toHistory.activeStage Te)
        (h1' : K.toHistory.activeStage aSeed ≤ K.eIdx_C11G2 j hjT hTj m)
        (h2' : K.eIdx_C11G2 j hjT hTj m ≤ K.toHistory.activeStage Tn),
        seedE.point m h1 h2 = seedTrace.point (K.eIdx_C11G2 j hjT hTj m) h1' h2') := by
  have hσT : (σ : ℝ) ≤ T := (show (σ : ℝ) ≤ Tn from hsT).trans hTt
  have haTT : (aSeed : ℝ) ≤ T := (show (aSeed : ℝ) ≤ Tn from haT).trans hTt
  let Te : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon :=
    ⟨Tn, Tn.2.1, hTt⟩
  let aE : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon :=
    ⟨aSeed, aSeed.2.1, haTT⟩
  let sE : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon :=
    ⟨σ, σ.2.1, hσT⟩
  have haTe : aE ≤ Te := show (aSeed : ℝ) ≤ Tn from haT
  have hsTe : sE ≤ Te := show (σ : ℝ) ≤ Tn from hsT
  have hasE : aE ≤ sE := show (aSeed : ℝ) ≤ σ from has
  have hlT := K.eventPrefix_activeStage_val j hjT hTj Te Tn rfl
  have hlS := K.eventPrefix_activeStage_val j hjT hTj sE σ rfl
  have hfA := K.eventPrefix_activeStage_val j hjT hTj aE aSeed rfl
  have hl : K.toHistory.activeStage Tn = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage Te) := Fin.ext hlT.symm
  have hs : K.toHistory.activeStage σ = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage sE) := Fin.ext hlS.symm
  have hf : K.toHistory.activeStage aSeed = K.eIdx_C11G2 j hjT hTj
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage aE) := Fin.ext hfA.symm
  let pe : ((K.eventPrefix j T hjT hTj).toHistory.stageAt Te).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hl) pT
  let yE : ((K.eventPrefix j T hjT hTj).toHistory.stageAt sE).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hs) y
  have hpe : HEq pe pT := cast_heq _ _
  have hyE : HEq yE y := cast_heq _ _
  obtain ⟨seedE, hseedE⟩ := K.exists_eventPrefixTrace_C11G2 j hjT hTj hf hl
    (hle := (K.eventPrefix j T hjT hTj).toHistory.activeStage_mono haTe)
    (hle' := K.toHistory.activeStage_mono haT) (x := pe) (x' := pT) hpe seedTrace
  exact ⟨Te, aE, sE, haTe, hsTe, hasE, pe, yE, seedE, rfl, rfl, rfl, hyE, hpe,
    fun m h1 h2 h1' h2' => hseedE m h1 h2 h1' h2'⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
