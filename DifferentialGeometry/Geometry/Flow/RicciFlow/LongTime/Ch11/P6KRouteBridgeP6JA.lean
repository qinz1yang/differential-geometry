import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CondBridgeP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# J10GEN2A G1：K→E 桥 `hgood` / `hdistC`（O-CH11-J10GEN2A，后缀 `_P6JA`）

无 J10 driver（`kRouteHICond_noJ10_P6JG` 族 / `kRouteHICond_noJ10_full_P6JA`）在 E 层吃 seed 数据
`(Tn, aSeed, pT, seedTrace)` 与 `hgood` / `hwin` / `hdistC`；四主合同与 consumer 在 K 层给同名前提。
本文件把 K 层 ⇒ E 层（仿 `hwitC_seq_of_eventPrefix_P6CD`），两种帧：
* **event 帧** `E = (K.eventPrefix j t).toHistory`
  （`eventPrefix_activeStage_val` / `eventPrefix_stageMetric`，
  E 的 stage `m` = K 的 stage `Fin.castLE _ m`，定义等）；
* **final 帧** `E = ((K.prefixAt last).extendAt … finalSlab …).toHistory`（`activeStage_final_P6M` /
  `stageMetric_final_P6M`，stage 指标同型）。
E 层 seed 与 K 层 seed 的联系 = 显式兼容前提 `hseed`（同实时刻的 seed 点 `HEq`）+ `haa`（E 起点不早于 K 起点：`aK ≤ aE`）；
`exists_seed_eventPrefix_P6JA` / `exists_seed_final_P6JA` 证明兼容 seed **存在**（K 的 seedTrace 限制到
`[aSeed, σ]`，`Tn^E := ts`——E 的 horizon 就是 `ts`，故 `hsT` 迫使 `Tn^E = ts`）。
主定理（全部 PROVED，standard axioms）：
* `hgood_seq_of_eventPrefix_P6JA` / `hdistC_seq_of_eventPrefix_P6JA`（event 帧）；
* `hgood_seq_final_P6JA` / `hdistC_seq_final_P6JA`（final 帧）；
* `hwin_seq_P6JA`（帧无关，`aE = aK` + `hσ`）/ `hwinE_of_clock_P6JA`（E 层 hwin ⇐ (B) 族 `hclock`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-! ### 通用指标搬运（`subst` 推广） -/

/-- 点态性质按 stage 指标搬运（`m = m'`、`HEq` 点）。 -/
theorem pt_index_P6JA (H : ObservedHistory.{u})
    (P : ∀ m : Fin (H.eventCount + 1), (H.stage m).Carrier → Prop)
    {m m' : Fin (H.eventCount + 1)} (hm : m = m') {x : (H.stage m).Carrier}
    {x' : (H.stage m').Carrier} (hx : HEq x x') (h : P m' x') : P m x := by
  subst hm
  obtain rfl := eq_of_heq hx
  exact h

/-- 同一 trace 在相等指标处的点 `HEq`。 -/
theorem point_heq_P6JA {H : ObservedHistory.{u}} {f l : Fin (H.eventCount + 1)} {hle : f ≤ l}
    {x : (H.stage l).Carrier} (B : BackwardPointTrace H f l hle x)
    {m m' : Fin (H.eventCount + 1)} (hm : m = m') (h1 : f ≤ m) (h2 : m ≤ l) (h1' : f ≤ m')
    (h2' : m' ≤ l) : HEq (B.point m h1 h2) (B.point m' h1' h2') := by
  subst hm
  rfl

/-- 距离按 stage 指标搬运（度量 `g = stageMetric m w`、`HEq` 两点）。 -/
theorem edist_congr_P6JA (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (w : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m w)
    (a b : (H.stage m).Carrier) (a' b' : (H.stage m').Carrier) (ha : HEq a a') (hb : HEq b b') :
    riemannianEDistOf g a b = riemannianEDistOf (H.stageMetric m' w) a' b' := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  rfl

/-- 标量按 stage 指标搬运。 -/
theorem scalar_congr_P6JA (H : ObservedHistory.{u}) {m m' : Fin (H.eventCount + 1)}
    (hm : m = m') (w : ℝ) (g : (H.stage m).Metric) (hg : g = H.stageMetric m w)
    (a : (H.stage m).Carrier) (a' : (H.stage m').Carrier) (ha : HEq a a') :
    metricScalarAt g a = metricScalarAt (H.stageMetric m' w) a' := by
  subst hg
  subst hm
  obtain rfl := eq_of_heq ha
  rfl

variable (K : RetainedCoreHistory.{u})

/-! ### event 帧 `E = K.eventPrefix j T` -/

/-- **`_P6JA`（event 帧，点态 time control）**：K 层 `HasSpatialCanonicalTimeControl`（同实时刻、`HEq` 点）
⇒ E 层（E 的 `v < horizon = T` ⇒ K 的 `v < K.horizon`）。 -/
theorem timeControl_of_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (v : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hvv : (v : ℝ) = v')
    (z : ((K.eventPrefix j T hjT hTj).toHistory.stageAt v).Carrier)
    (z' : (K.toHistory.stageAt v').Carrier) (hz : HEq z z') {eps C1 C2 : ℝ} {Ct : ℝ≥0}
    (h : K.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v' z') :
    (K.eventPrefix j T hjT hTj).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := by
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) = K.toHistory.activeStage v' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj v v' hvv)
  have hP := pt_index_P6JA K.toHistory
    (fun m pt => (∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) eps C1 C2 pt,
        W.capTubeHasNeckChart eps) ∧
      (K.toHistory.time m < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
        |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) pt)
          (Iic (v : ℝ)) v| ≤ Ct * metricScalarAt (K.toHistory.stageMetric m v) pt ^ 2))
    hidx hz (by rw [hvv]; exact h)
  have hfun : (K.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) =
      K.toHistory.stageMetric (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)) :=
    funext fun w => K.eventPrefix_stageMetric j hjT hTj _ w
  unfold ObservedHistory.HasSpatialCanonicalTimeControl
  rw [hfun]
  exact ⟨hP.1, fun h1 h2 => hP.2 h1 (lt_of_lt_of_le h2 hTH)⟩

/-- **`_P6JA`（event 帧，单 history `hgood`）**：K 层 hgood（K seed、基点 `τ'`、`yK`）+ seed 兼容
`haa` / `hseed` ⇒ E 层 hgood（E seed、基点 `τ`、`yE`；同 `L` / `Rn` / 阈值 `Cg·Rn`）。 -/
theorem hgood_of_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (TnE aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ TnE) (hsTE : τ ≤ TnE) (hasE : aE ≤ τ)
    (pTE : (E.stageAt TnE).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage TnE)
      (E.activeStage_mono haTE) pTE)
    (haa : (aK : ℝ) ≤ aE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage TnE)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    {eps C1 C2 Cg L Rn : ℝ} {Ct : ℝ≥0}
    (hK : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aK ≤ v) (hvs : v ≤ τ'),
      (τ' : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedK.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsTK))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
              (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
                (K.toHistory.activeStage_mono hsTK)) yK +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z) :
    ∀ (v : Icc (0 : ℝ) E.horizon) (hav : aE ≤ v) (hvs : v ≤ τ),
      (τ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (E.stageAt v).Carrier,
        riemannianEDistOf (E.stageMetric (E.activeStage v) v)
            (seedE.point (E.activeStage v) (E.activeStage_mono hav)
              (E.activeStage_mono (hvs.trans hsTE))) z ≤
          riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
              (seedE.point (E.activeStage τ) (E.activeStage_mono hasE)
                (E.activeStage_mono hsTE)) yE +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (E.stageMetric (E.activeStage v) v) z →
        E.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := by
  subst hE
  intro v hav hvs hL z hd hs
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidx : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) = K.toHistory.activeStage v' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj v v' rfl)
  have hidxτ : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  let z' : (K.toHistory.stageAt v').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) z
  have hzz : HEq z z' := (cast_heq _ _).symm
  have hav' : aK ≤ v' := show (aK : ℝ) ≤ v from haa.trans hav
  have hvs' : v' ≤ τ' := show (v : ℝ) ≤ τ' from hττ ▸ hvs
  have hL' : (τ' : ℝ) - L ^ 2 / Rn ≤ (v' : ℝ) := hττ ▸ hL
  have hmetv := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) v
  have hmetτ := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmetτ
  have e1 := edist_congr_P6JA K.toHistory hidx v _ hmetv
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hav)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono (hvs.trans hsTE))) z _ z'
    (hseed v v' rfl _ _ (K.toHistory.activeStage_mono hav')
      (K.toHistory.activeStage_mono (hvs'.trans hsTK))) hzz
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hasE)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e3 := scalar_congr_P6JA K.toHistory hidx v _ hmetv z z' hzz
  rw [hττ] at hd
  have hd' := (e1.symm.trans_le hd).trans_eq
    (congrArg (fun a => a + ENNReal.ofReal (L / Real.sqrt Rn)) e2)
  exact K.timeControl_of_eventPrefix_P6JA j hjT hTj v v' rfl z z' hzz
    (hK v' hav' hvs' hL' z' hd' (hs.trans_eq e3))

/-- **`_P6JA`（event 帧，单 history `hdist`）**：K 层 seed 距离界（基点球半径 `ρ`、深度 `θ`、余量 `δ`）
+ seed 兼容 ⇒ E 层同形（E 的 trace 经 `forall_trace_eventPrefix_P6M` 上推到 K）。 -/
theorem hdist_of_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (TnE aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ TnE) (hsTE : τ ≤ TnE) (hasE : aE ≤ τ)
    (pTE : (E.stageAt TnE).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage TnE)
      (E.activeStage_mono haTE) pTE)
    (haa : (aK : ℝ) ≤ aE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage TnE)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    {ρ θ : ℝ} {δ : ℝ≥0∞}
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') yK ρ,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aK ≤ v) (hvs : v ≤ τ'),
        (τ' : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedK.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsTK)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
              (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
                (K.toHistory.activeStage_mono hsTK)) yK + δ) :
    ∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) yE ρ,
      ∀ (v : Icc (0 : ℝ) E.horizon) (hav : aE ≤ v) (hvs : v ≤ τ), (τ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
          (E.activeStage_mono hvs) x,
        riemannianEDistOf (E.stageMetric (E.activeStage v) v)
            (seedE.point (E.activeStage v) (E.activeStage_mono hav)
              (E.activeStage_mono (hvs.trans hsTE)))
            (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvs)) ≤
          riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
              (seedE.point (E.activeStage τ) (E.activeStage_mono hasE)
                (E.activeStage_mono hsTE)) yE + δ := by
  subst hE
  intro x hx v hav hvs hθ tr
  have hTH : T ≤ K.horizon := hTj.le.trans (K.toHistory.time_le_horizon_at j.succ)
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidxτ : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidxτ) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_of_eventPrefix_P6M j hjT hTj τ τ' hττ yE x yK x' hy hxx ρ hx
  have hav' : aK ≤ v' := show (aK : ℝ) ≤ v from haa.trans hav
  have hvs' : v' ≤ τ' := show (v : ℝ) ≤ τ' from hττ ▸ hvs
  have hθ' : (τ' : ℝ) - θ ≤ (v' : ℝ) := hττ ▸ hθ
  have h := K.forall_trace_eventPrefix_P6M j hjT hTj τ v hvs τ' v' hττ rfl x x' hxx
    (fun m pt => ∀ sp : (K.stage m).Carrier,
      HEq sp (seedK.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono hav')
        (K.toHistory.activeStage_mono (hvs'.trans hsTK))) →
      riemannianEDistOf (K.toHistory.stageMetric m v) sp pt ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
            (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
              (K.toHistory.activeStage_mono hsTK)) yK + δ)
    (fun hvτ' tr' sp hsp => by
      obtain rfl := eq_of_heq hsp
      exact hK x' hx' v' hav' hvτ' hθ' tr') tr
  have hmetv := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) v
  have hmetτ := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmetτ
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hasE)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e1 := edist_congr_P6JA K.toHistory rfl v _ hmetv
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hav)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono (hvs.trans hsTE)))
    (tr.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v) le_rfl
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvs)) _ _ HEq.rfl HEq.rfl
  have hfn := h (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage v)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hav)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono (hvs.trans hsTE)))
    (hseed v v' rfl _ _ (K.toHistory.activeStage_mono hav')
      (K.toHistory.activeStage_mono (hvs'.trans hsTK)))
  rw [hττ]
  exact (e1.trans_le hfn).trans_eq
    (congrArg (fun a => a + δ) e2.symm)

/-- **`_P6JA`（event 帧，兼容 E seed 存在）**：K 的 seedTrace（`[aK, TnK]`，`τ' ≤ TnK`）限制到 `[aK, τ']`
并按 `Fin.castLE` 搬到 E（`Tn^E := τ`、起点 `a^E := a ∈ [aK, τ]` 任选）；seed 点与 K 的同实时刻 seed 点 `HEq`。
（`hgood_of_eventPrefix_P6JA` / `hdist_of_eventPrefix_P6JA` 的 `haa` / `hseed` 前提可满足。） -/
theorem exists_seed_eventPrefix_P6JA (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (a : ℝ) (haK : (aK : ℝ) ≤ a) (haτ : a ≤ τ) :
    ∃ (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (pTE : (E.stageAt τ).Carrier)
      (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
        (E.activeStage_mono haTE) pTE),
      (aE : ℝ) = a ∧
      ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon), (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2') := by
  subst hE
  have haH : a ≤ (K.eventPrefix j T hjT hTj).toHistory.horizon := haτ.trans τ.2.2
  let aE : Icc (0 : ℝ) (K.eventPrefix j T hjT hTj).toHistory.horizon := ⟨a, aK.2.1.trans haK, haH⟩
  have haTE : aE ≤ τ := haτ
  let a' : Icc (0 : ℝ) K.toHistory.horizon :=
    ⟨a, aK.2.1.trans haK, (haτ.trans (le_of_eq hττ)).trans τ'.2.2⟩
  have hva : (K.toHistory.activeStage aK).val ≤
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage aE).val := by
    have h1 := Fin.le_iff_val_le_val.mp (K.toHistory.activeStage_mono (show aK ≤ a' from haK))
    have h2 := K.eventPrefix_activeStage_val j hjT hTj aE a' rfl
    omega
  have hvt : (K.toHistory.activeStage τ').val =
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val :=
    (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ).symm
  have hTK : (K.toHistory.activeStage τ').val ≤ (K.toHistory.activeStage TnK).val :=
    Fin.le_iff_val_le_val.mp (K.toHistory.activeStage_mono hsTK)
  refine ⟨aE, haTE, seedK.point
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ))
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤
          ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val from by
        have := Fin.le_iff_val_le_val.mp
          ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono haTE)
        omega))
      (Fin.le_iff_val_le_val.mpr (show ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ).val ≤
          (K.toHistory.activeStage TnK).val from by omega)),
    ⟨fun m hf hl => seedK.point
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m)
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤ m.val from by
        have := Fin.le_iff_val_le_val.mp hf
        omega))
      (Fin.le_iff_val_le_val.mpr (show m.val ≤ (K.toHistory.activeStage TnK).val from by
        have := Fin.le_iff_val_le_val.mp hl
        omega)), rfl,
    fun i hf hl => seedK.crossing (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤ i.val from by
        have := Fin.le_iff_val_le_val.mp hf
        simp only [Fin.val_castSucc] at this
        omega))
      (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage TnK).val from by
        have := Fin.le_iff_val_le_val.mp hl
        simp only [Fin.val_succ] at this
        omega))⟩, rfl, ?_⟩
  intro v v' hvv h1 h2 h1' h2'
  exact point_heq_P6JA seedK (Fin.ext (K.eventPrefix_activeStage_val j hjT hTj v v' hvv)) _ _
    h1' h2'

/-! ### final 帧 `E = (K.prefixAt last).extendAt … finalSlab …` -/

/-- **`_P6JA`（final 帧，点态 time control）**：K 层 `HasSpatialCanonicalTimeControl`（同实时刻、`HEq` 点）
⇒ E 层（E 的 `v < horizon = T` ⇒ K 的 `v < K.horizon`）。 -/
theorem timeControl_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (v : Icc (0 : ℝ) ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.horizon)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hvv : (v : ℝ) = v')
    (z : (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.stageAt v).Carrier)
    (z' : (K.toHistory.stageAt v').Carrier) (hz : HEq z z') {eps C1 C2 : ℝ} {Ct : ℝ≥0}
    (h : K.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v' z') :
    ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := by
  have hTH : T ≤ K.horizon := hTs.le
  have hidx := K.activeStage_final_P6M hfin hT hTs v v' hvv
  have hP := pt_index_P6JA K.toHistory
    (fun m pt => (∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) eps C1 C2 pt,
        W.capTubeHasNeckChart eps) ∧
      (K.toHistory.time m < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
        |derivWithin (fun t => metricScalarAt (K.toHistory.stageMetric m t) pt)
          (Iic (v : ℝ)) v| ≤ Ct * metricScalarAt (K.toHistory.stageMetric m v) pt ^ 2))
    hidx hz (by rw [hvv]; exact h)
  have hfun : ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.stageMetric
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage v) =
      K.toHistory.stageMetric
        (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage v) :=
    funext fun w => K.stageMetric_final_P6M hfin hT hTs _ w
  unfold ObservedHistory.HasSpatialCanonicalTimeControl
  rw [hfun]
  exact ⟨hP.1, fun h1 h2 => hP.2 h1 (lt_of_lt_of_le h2 hTH)⟩

/-- **`_P6JA`（final 帧，单 history `hgood`）**：K 层 hgood（K seed、基点 `τ'`、`yK`）+ seed 兼容
`haa` / `hseed` ⇒ E 层 hgood（E seed、基点 `τ`、`yE`；同 `L` / `Rn` / 阈值 `Cg·Rn`）。 -/
theorem hgood_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E =
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (TnE aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ TnE) (hsTE : τ ≤ TnE) (hasE : aE ≤ τ)
    (pTE : (E.stageAt TnE).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage TnE)
      (E.activeStage_mono haTE) pTE)
    (haa : (aK : ℝ) ≤ aE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage TnE)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    {eps C1 C2 Cg L Rn : ℝ} {Ct : ℝ≥0}
    (hK : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aK ≤ v) (hvs : v ≤ τ'),
      (τ' : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedK.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsTK))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
              (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
                (K.toHistory.activeStage_mono hsTK)) yK +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z) :
    ∀ (v : Icc (0 : ℝ) E.horizon) (hav : aE ≤ v) (hvs : v ≤ τ),
      (τ : ℝ) - L ^ 2 / Rn ≤ (v : ℝ) →
      ∀ z : (E.stageAt v).Carrier,
        riemannianEDistOf (E.stageMetric (E.activeStage v) v)
            (seedE.point (E.activeStage v) (E.activeStage_mono hav)
              (E.activeStage_mono (hvs.trans hsTE))) z ≤
          riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
              (seedE.point (E.activeStage τ) (E.activeStage_mono hasE)
                (E.activeStage_mono hsTE)) yE +
            ENNReal.ofReal (L / Real.sqrt Rn) →
        Cg * Rn ≤ metricScalarAt (E.stageMetric (E.activeStage v) v) z →
        E.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := by
  subst hE
  intro v hav hvs hL z hd hs
  have hTH : T ≤ K.horizon := hTs.le
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidx := K.activeStage_final_P6M hfin hT hTs v v' rfl
  have hidxτ := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let z' : (K.toHistory.stageAt v').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidx) z
  have hzz : HEq z z' := (cast_heq _ _).symm
  have hav' : aK ≤ v' := show (aK : ℝ) ≤ v from haa.trans hav
  have hvs' : v' ≤ τ' := show (v : ℝ) ≤ τ' from hττ ▸ hvs
  have hL' : (τ' : ℝ) - L ^ 2 / Rn ≤ (v' : ℝ) := hττ ▸ hL
  have hmetv := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v) v
  have hmetτ := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage τ) τ
  rw [hττ] at hmetτ
  have e1 := edist_congr_P6JA K.toHistory hidx v _ hmetv
    (seedE.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hav)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono (hvs.trans hsTE))) z _ z'
    (hseed v v' rfl _ _ (K.toHistory.activeStage_mono hav')
      (K.toHistory.activeStage_mono (hvs'.trans hsTK))) hzz
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage τ)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hasE)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e3 := scalar_congr_P6JA K.toHistory hidx v _ hmetv z z' hzz
  rw [hττ] at hd
  have hd' := (e1.symm.trans_le hd).trans_eq
    (congrArg (fun a => a + ENNReal.ofReal (L / Real.sqrt Rn)) e2)
  exact K.timeControl_final_P6JA hfin hT hTs v v' rfl z z' hzz
    (hK v' hav' hvs' hL' z' hd' (hs.trans_eq e3))

/-- **`_P6JA`（final 帧，单 history `hdist`）**：K 层 seed 距离界（基点球半径 `ρ`、深度 `θ`、余量 `δ`）
+ seed 兼容 ⇒ E 层同形（E 的 trace 经 `forall_trace_final_P6M` 上推到 K）。 -/
theorem hdist_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E =
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (TnE aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ TnE) (hsTE : τ ≤ TnE) (hasE : aE ≤ τ)
    (pTE : (E.stageAt TnE).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage TnE)
      (E.activeStage_mono haTE) pTE)
    (haa : (aK : ℝ) ≤ aE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage TnE)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    {ρ θ : ℝ} {δ : ℝ≥0∞}
    (hK : ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ') yK ρ,
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aK ≤ v) (hvs : v ≤ τ'),
        (τ' : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
          (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hvs) x,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedK.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsTK)))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
              (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
                (K.toHistory.activeStage_mono hsTK)) yK + δ) :
    ∀ x ∈ riemannianBallOf (E.stageMetric (E.activeStage τ) τ) yE ρ,
      ∀ (v : Icc (0 : ℝ) E.horizon) (hav : aE ≤ v) (hvs : v ≤ τ), (τ : ℝ) - θ ≤ v →
      ∀ tr : BackwardPointTrace E (E.activeStage v) (E.activeStage τ)
          (E.activeStage_mono hvs) x,
        riemannianEDistOf (E.stageMetric (E.activeStage v) v)
            (seedE.point (E.activeStage v) (E.activeStage_mono hav)
              (E.activeStage_mono (hvs.trans hsTE)))
            (tr.point (E.activeStage v) le_rfl (E.activeStage_mono hvs)) ≤
          riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
              (seedE.point (E.activeStage τ) (E.activeStage_mono hasE)
                (E.activeStage_mono hsTE)) yE + δ := by
  subst hE
  intro x hx v hav hvs hθ tr
  have hTH : T ≤ K.horizon := hTs.le
  let v' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, v.2.1, v.2.2.trans hTH⟩
  have hidxτ := K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  let x' : (K.toHistory.stageAt τ').Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hidxτ) x
  have hxx : HEq x x' := (cast_heq _ _).symm
  have hx' := K.mem_ball_final_P6M hfin hT hTs τ τ' hττ yE x yK x' hy hxx ρ hx
  have hav' : aK ≤ v' := show (aK : ℝ) ≤ v from haa.trans hav
  have hvs' : v' ≤ τ' := show (v : ℝ) ≤ τ' from hττ ▸ hvs
  have hθ' : (τ' : ℝ) - θ ≤ (v' : ℝ) := hττ ▸ hθ
  have h := K.forall_trace_final_P6M hfin hT hTs τ v hvs τ' v' hττ rfl x x' hxx
    (fun m pt => ∀ sp : (K.stage m).Carrier,
      HEq sp (seedK.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono hav')
        (K.toHistory.activeStage_mono (hvs'.trans hsTK))) →
      riemannianEDistOf (K.toHistory.stageMetric m v) sp pt ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
            (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
              (K.toHistory.activeStage_mono hsTK)) yK + δ)
    (fun hvτ' tr' sp hsp => by
      obtain rfl := eq_of_heq hsp
      exact hK x' hx' v' hav' hvτ' hθ' tr') tr
  have hmetv := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v) v
  have hmetτ := K.stageMetric_final_P6M hfin hT hTs
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage τ) τ
  rw [hττ] at hmetτ
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage τ)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hasE)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e1 := edist_congr_P6JA K.toHistory rfl v _ hmetv
    (seedE.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hav)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono (hvs.trans hsTE)))
    (tr.point (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory.activeStage v) le_rfl
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hvs)) _ _ HEq.rfl HEq.rfl
  have hfn := h (seedE.point
    (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.activeStage v)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono hav)
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage_mono (hvs.trans hsTE)))
    (hseed v v' rfl _ _ (K.toHistory.activeStage_mono hav')
      (K.toHistory.activeStage_mono (hvs'.trans hsTK)))
  rw [hττ]
  exact (e1.trans_le hfn).trans_eq
    (congrArg (fun a => a + δ) e2.symm)

/-- **`_P6JA`（final 帧，兼容 E seed 存在）**：K 的 seedTrace（`[aK, TnK]`，`τ' ≤ TnK`）限制到 `[aK, τ']`
搬到 final 截断 E（stage 指标同型）（`Tn^E := τ`、`a^E := aK`）；seed 点与 K 的同实时刻 seed 点 `HEq`。
（`hgood_final_P6JA` / `hdist_final_P6JA` 的 `haa` / `hseed` 前提可满足。） -/
theorem exists_seed_final_P6JA (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {T : ℝ} (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E =
      ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
        hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (a : ℝ) (haK : (aK : ℝ) ≤ a) (haτ : a ≤ τ) :
    ∃ (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (pTE : (E.stageAt τ).Carrier)
      (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
        (E.activeStage_mono haTE) pTE),
      (aE : ℝ) = a ∧
      ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon), (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2') := by
  subst hE
  have haH : a ≤ ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.horizon := haτ.trans τ.2.2
  let aE : Icc (0 : ℝ) ((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
      hTs).toHistory.horizon := ⟨a, aK.2.1.trans haK, haH⟩
  have haTE : aE ≤ τ := haτ
  let a' : Icc (0 : ℝ) K.toHistory.horizon :=
    ⟨a, aK.2.1.trans haK, (haτ.trans (le_of_eq hττ)).trans τ'.2.2⟩
  have hva : (K.toHistory.activeStage aK).val ≤
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage aE).val := by
    have h1 := Fin.le_iff_val_le_val.mp (K.toHistory.activeStage_mono (show aK ≤ a' from haK))
    have h2 := K.activeStage_val_final_P6M hfin hT hTs aE a' rfl
    omega
  have hvt : (K.toHistory.activeStage τ').val =
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ).val :=
    (K.activeStage_val_final_P6M hfin hT hTs τ τ' hττ).symm
  have hTK : (K.toHistory.activeStage τ').val ≤ (K.toHistory.activeStage TnK).val :=
    Fin.le_iff_val_le_val.mp (K.toHistory.activeStage_mono hsTK)
  refine ⟨aE, haTE, seedK.point
      (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ)
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤
          (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
              ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
              hTs).toHistory.activeStage τ).val from by
        have := Fin.le_iff_val_le_val.mp
          (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
              ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
              hTs).toHistory.activeStage_mono haTE)
        omega))
      (Fin.le_iff_val_le_val.mpr (show
        (((K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
          ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT
          hTs).toHistory.activeStage τ).val ≤
          (K.toHistory.activeStage TnK).val from by omega)),
    ⟨fun m hf hl => seedK.point
      m
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤ m.val from by
        have := Fin.le_iff_val_le_val.mp hf
        omega))
      (Fin.le_iff_val_le_val.mpr (show m.val ≤ (K.toHistory.activeStage TnK).val from by
        have := Fin.le_iff_val_le_val.mp hl
        omega)), rfl,
    fun i hf hl => seedK.crossing i
      (Fin.le_iff_val_le_val.mpr (show (K.toHistory.activeStage aK).val ≤ i.val from by
        have := Fin.le_iff_val_le_val.mp hf
        simp only [Fin.val_castSucc] at this
        omega))
      (Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ (K.toHistory.activeStage TnK).val from by
        have := Fin.le_iff_val_le_val.mp hl
        simp only [Fin.val_succ] at this
        omega))⟩, rfl, ?_⟩
  intro v v' hvv h1 h2 h1' h2'
  exact point_heq_P6JA seedK (K.activeStage_final_P6M hfin hT hTs v v' hvv) _ _
    h1' h2'

end RetainedCoreHistory

namespace ObservedHistory

/-- **`_P6JA`（`hwin`，帧无关）**：K 层 `aK ≤ σ − T/R` ⇒ E 层 `aE ≤ ts − T/R`（`haa`、`hσ`）。 -/
theorem hwin_seq_P6JA {Hs : ℕ → ObservedHistory.{u}} {Kh : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
    {aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {aK : ∀ n, Icc (0 : ℝ) (Kh n).horizon} {R : ℕ → ℝ}
    (hσ : ∀ n, (ts n : ℝ) = σ n) (haa : ∀ n, (aE n : ℝ) = aK n)
    (h : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aK n : ℝ) ≤ σ n - T / R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aE n : ℝ) ≤ ts n - T / R n :=
  fun T hT => (h T hT).mono fun n hn => by rw [haa n, hσ n]; exact hn

/-- **`_P6JA`（E 层 `hwin` ⇐ (B) 族 `hclock`，帧无关）**：E seed 顶 `Tn^E ≥ ts = horizon`（故 `Tn^E = ts`）且
`aE = Tn^E − rX²`（`rX > 0`）⇒ `aE ≤ ts − T/R` eventually（`R → ∞`）。twins 用它代替 K 层 `hwin`
（E 起点不必等于 K 起点）。 -/
theorem hwinE_of_clock_P6JA {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
    {TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {R : ℕ → ℝ} {rX : ℝ}
    (hsTE : ∀ n, ts n ≤ TnE n) (htop : ∀ n, (ts n : ℝ) = (Hs n).horizon) (hrX : 0 < rX)
    (hclock : ∀ n, (aE n : ℝ) = (TnE n : ℝ) - rX ^ 2) (hRlim : Tendsto R atTop atTop) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aE n : ℝ) ≤ ts n - T / R n := by
  intro T hT
  have hr2 : 0 < rX ^ 2 := by positivity
  filter_upwards [hRlim.eventually_ge_atTop (T / rX ^ 2), hRlim.eventually_gt_atTop 0]
    with n hn hR0
  have hTn : (TnE n : ℝ) = ts n := le_antisymm ((TnE n).2.2.trans_eq (htop n).symm) (hsTE n)
  have hle : T / R n ≤ rX ^ 2 := by
    rw [div_le_iff₀ hR0]
    rw [div_le_iff₀ hr2] at hn
    linarith
  rw [hclock n, hTn]
  linarith

section Seq

variable {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
  {hjt : ∀ n, (K n).time (j n).castSucc < t n} {htj : ∀ n, t n < (K n).time (j n).succ}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}
  {TnK aK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {haTK : ∀ n, aK n ≤ TnK n}
  {hsTK : ∀ n, σ n ≤ TnK n} {hasK : ∀ n, aK n ≤ σ n}
  {pTK : ∀ n, ((K n).toHistory.stageAt (TnK n)).Carrier}
  {seedK : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aK n))
    ((K n).toHistory.activeStage (TnK n)) ((K n).toHistory.activeStage_mono (haTK n)) (pTK n)}
  {TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {haTE : ∀ n, aE n ≤ TnE n}
  {hsTE : ∀ n, ts n ≤ TnE n} {hasE : ∀ n, aE n ≤ ts n}
  {pTE : ∀ n, ((Hs n).stageAt (TnE n)).Carrier}
  {seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
    ((Hs n).activeStage (TnE n)) ((Hs n).activeStage_mono (haTE n)) (pTE n)}

/-- **G1（`_P6JA`，PROVED；序列 `hgood`，event 帧）**：K 层 hgood（closed-kappa / RERUN8B / CoarseChainA
的合同前提形，基点 `σ`、`y`）+ seed 兼容 ⇒ E 层 hgood（driver `kRouteHICond_noJ10_*` 的槽逐字）。 -/
theorem hgood_seq_of_eventPrefix_P6JA
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (haa : ∀ n, (aK n : ℝ) ≤ aE n)
    (hseed : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
        (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
        (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
        (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
        HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
          ((seedK n).point ((K n).toHistory.activeStage v') h1' h2'))
    {eps C1 C2 Cg : ℝ} {Ct : ℝ≥0} {L : ℕ → ℝ}
    (hK : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aK n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedK n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsTK n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedK n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (hasK n))
                ((K n).toHistory.activeStage_mono (hsTK n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z) :
    ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aE n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedE n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsTE n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
                ((Hs n).activeStage_mono (hsTE n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := fun n =>
  (K n).hgood_of_eventPrefix_P6JA (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n) (TnE n)
    (aE n) (haTE n) (hsTE n) (hasE n) (pTE n) (seedE n) (haa n) (hseed n) (hK n)

/-- **G1（`_P6JA`，PROVED；序列 `hdistC`，event 帧）**：K 层条件形 seed 距离界（余量 `δ n` 任意；closed-kappa
的 `L/4` 形先在 K 层放宽）+ seed 兼容 ⇒ E 层条件形（driver 槽逐字，`δ n := ofReal (L n/√R n)`）；
traced 条件 E → K 用 `tracedC_of_eventPrefix_P6CD`。 -/
theorem hdistC_seq_of_eventPrefix_P6JA
    (hHs : ∀ n, Hs n = ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (haa : ∀ n, (aK n : ℝ) ≤ aE n)
    (hseed : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
        (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
        (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
        (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
        HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
          ((seedK n).point ((K n).toHistory.activeStage v') h1' h2'))
    {δ : ℕ → ℝ≥0∞}
    (hK : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aK n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedK n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsTK n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedK n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (hasK n))
                ((K n).toHistory.activeStage_mono (hsTK n))) (y n) + δ n) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aE n ≤ v) (hvs : v ≤ ts n),
        (ts n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvs) x,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedE n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsTE n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
                ((Hs n).activeStage_mono (hsTE n))) (ys n) + δ n := by
  intro φ hφ D T Kc hD hT hKc htr
  filter_upwards [hK φ hφ D T Kc hD hT hKc (tracedC_of_eventPrefix_P6CD hHs hσ hys htr)]
    with n hn
  exact (K n).hdist_of_eventPrefix_P6JA (j n) (hjt n) (htj n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n) (TnE n)
    (aE n) (haTE n) (hsTE n) (hasE n) (pTE n) (seedE n) (haa n) (hseed n) hn

end Seq

section SeqFinal

variable {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
  {htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n} {htK : ∀ n, t n < (K n).horizon}
  {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
  {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ}
  {TnK aK : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon} {haTK : ∀ n, aK n ≤ TnK n}
  {hsTK : ∀ n, σ n ≤ TnK n} {hasK : ∀ n, aK n ≤ σ n}
  {pTK : ∀ n, ((K n).toHistory.stageAt (TnK n)).Carrier}
  {seedK : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aK n))
    ((K n).toHistory.activeStage (TnK n)) ((K n).toHistory.activeStage_mono (haTK n)) (pTK n)}
  {TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {haTE : ∀ n, aE n ≤ TnE n}
  {hsTE : ∀ n, ts n ≤ TnE n} {hasE : ∀ n, aE n ≤ ts n}
  {pTE : ∀ n, ((Hs n).stageAt (TnE n)).Carrier}
  {seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
    ((Hs n).activeStage (TnE n)) ((Hs n).activeStage_mono (haTE n)) (pTE n)}

/-- **G1（`_P6JA`，PROVED；序列 `hgood`，final 帧）**：K 层 hgood（FCKRoute / RERUN8B final 支
的合同前提形，基点 `σ`、`y`）+ seed 兼容 ⇒ E 层 hgood（driver `kRouteHICond_noJ10_*` 的槽逐字）。 -/
theorem hgood_seq_final_P6JA
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (haa : ∀ n, (aK n : ℝ) ≤ aE n)
    (hseed : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
        (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
        (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
        (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
        HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
          ((seedK n).point ((K n).toHistory.activeStage v') h1' h2'))
    {eps C1 C2 Cg : ℝ} {Ct : ℝ≥0} {L : ℕ → ℝ}
    (hK : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aK n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedK n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsTK n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedK n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (hasK n))
                ((K n).toHistory.activeStage_mono (hsTK n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ct v z) :
    ∀ n, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aE n ≤ v) (hvs : v ≤ ts n),
      (ts n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedE n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsTE n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
                ((Hs n).activeStage_mono (hsTE n))) (ys n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1 C2 Ct v z := fun n =>
  (K n).hgood_final_P6JA ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n) (σ n) (hσ n)
    (ys n) (y n) (hys n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n) (TnE n)
    (aE n) (haTE n) (hsTE n) (hasE n) (pTE n) (seedE n) (haa n) (hseed n) (hK n)

/-- **G1（`_P6JA`，PROVED；序列 `hdistC`，final 帧）**：K 层条件形 seed 距离界（余量 `δ n` 任意；closed-kappa
的 `L/4` 形先在 K 层放宽）+ seed 兼容 ⇒ E 层条件形（driver 槽逐字，`δ n := ofReal (L n/√R n)`）；
traced 条件 E → K 用 `isTracedRegion'_final_P6M`。 -/
theorem hdistC_seq_final_P6JA
    (hHs : ∀ n, Hs n = (((K n).prefixAt (Fin.last (K n).eventCount)).extendAt
      ((K n).prefixAt_time_last _) (((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming
        le_rfl ((htl n).trans (htK n)) le_rfl) ((K n).final_initial ((htl n).trans (htK n)))
      (htl n) (htK n)).toHistory)
    (hσ : ∀ n, (ts n : ℝ) = σ n) (hys : ∀ n, HEq (ys n) (y n))
    (haa : ∀ n, (aK n : ℝ) ≤ aE n)
    (hseed : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (K n).toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
        (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
        (h1' : (K n).toHistory.activeStage (aK n) ≤ (K n).toHistory.activeStage v')
        (h2' : (K n).toHistory.activeStage v' ≤ (K n).toHistory.activeStage (TnK n)),
        HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
          ((seedK n).point ((K n).toHistory.activeStage v') h1' h2'))
    {δ : ℕ → ℝ≥0∞}
    (hK : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aK n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedK n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsTK n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedK n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (hasK n))
                ((K n).toHistory.activeStage_mono (hsTK n))) (y n) + δ n) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Hs n).isTracedRegion (ts n) (ys n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aE n ≤ v) (hvs : v ≤ ts n),
        (ts n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvs) x,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedE n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hsTE n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
              ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
                ((Hs n).activeStage_mono (hsTE n))) (ys n) + δ n := by
  intro φ hφ D T Kc hD hT hKc htr
  filter_upwards [hK φ hφ D T Kc hD hT hKc (htr.mono fun n hn =>
      (K n).isTracedRegion'_final_P6M ((htl n).trans (htK n)) (htl n)
      (htK n) (Hs n) (hHs n) (ts n) (σ n) (hσ n) (ys n) (y n) (hys n) hn)]
    with n hn
  exact (K n).hdist_final_P6JA ((htl n).trans (htK n)) (htl n) (htK n) (Hs n) (hHs n) (ts n)
    (σ n) (hσ n)
    (ys n) (y n) (hys n) (TnK n) (aK n) (haTK n) (hsTK n) (hasK n) (pTK n) (seedK n) (TnE n)
    (aE n) (haTE n) (hsTE n) (hasE n) (pTE n) (seedE n) (haa n) (hseed n) hn

end SeqFinal

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
