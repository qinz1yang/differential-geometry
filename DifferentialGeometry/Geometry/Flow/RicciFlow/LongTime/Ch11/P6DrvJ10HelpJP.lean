import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10DJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBRowsA6K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceRecords_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTransportC11G2

/-!
# J10PAY G1：K 帧 ⇒ prefix / E 帧 的限制引理（`_JP`）

`J10ResE_DJ` 的 (A) 类项（slab 导数、pinching、δ、records、`hfinX`）在 prefix 帧
`H := K.prefixAt j.castSucc` / E 帧 `K.eventPrefix j T` 上的限制。全部 PROVED，无新前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

/-- 导数界对常数 / 阈值 / 终点单调（阈值升、常数升、终点降）。 -/
theorem DerivativeBoundBefore.mono_JP {C C' : ℝ≥0} {q q' t t' : ℝ}
    (h : G.DerivativeBoundBefore C q t) (hC : C ≤ C') (hq : q ≤ q') (ht : t' ≤ t) :
    G.DerivativeBoundBefore C' q' t' := by
  intro y τ hτ hqs
  have hτ' : τ ∈ Ioo a t := ⟨hτ.1, lt_of_lt_of_le hτ.2 ht⟩
  have h1 := h y τ hτ' (lt_of_le_of_lt hq hqs)
  refine h1.trans ?_
  have : (C : ℝ) ≤ C' := by exact_mod_cast hC
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end OrientedThreeStage.IncomingSlab

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- prefix 上事件 slab 的导数界（K 的截断形 `EventSlabsDerivative`——终点 `min (time i⁺) Tmax`——
限制到 `prefixAt k`，阈值单调；`Tmax` 不小于 prefix 全部事件时刻）。 -/
theorem prefix_eventSlabsDerivative_JP (k : Fin (K.eventCount + 1)) {Ctime : ℝ≥0} {Q q Tmax : ℝ}
    (hq : Q ≤ q) (hT : ∀ i : Fin (K.prefixAt k).eventCount, (K.prefixAt k).time i.succ ≤ Tmax)
    (h : ∀ i : Fin K.eventCount,
      (K.toHistory.event i).incoming.DerivativeBoundBefore Ctime Q (min (K.time i.succ) Tmax)) :
    (K.prefixAt k).EventSlabsDerivative Ctime q (Fin.last (K.prefixAt k).eventCount) := by
  intro i _
  refine OrientedThreeStage.IncomingSlab.DerivativeBoundBefore.mono_JP _
    (h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)) le_rfl hq ?_
  exact le_min le_rfl (hT i)

/-- slab `j` 上的导数界：`(Ctime, Q, 截断终点 min (time j⁺) Tmax)` ⇒ `(2 Ctime, 2 q)` 于 `T`
（`0 ≤ q`，`Q ≤ q`，`T ≤ time j⁺`，`T ≤ Tmax`）。 -/
theorem slabJ_derivativeBound_JP (j : Fin K.eventCount) {Ctime : ℝ≥0} {Q q T Tmax : ℝ}
    (hq : Q ≤ q) (hq0 : 0 ≤ q) (hT : T ≤ K.time j.succ) (hTm : T ≤ Tmax)
    (h : ∀ i : Fin K.eventCount,
      (K.toHistory.event i).incoming.DerivativeBoundBefore Ctime Q (min (K.time i.succ) Tmax)) :
    (K.toHistory.event j).incoming.DerivativeBoundBefore (2 * Ctime) (2 * q) T :=
  OrientedThreeStage.IncomingSlab.DerivativeBoundBefore.mono_JP _ (h j) (by
      have : Ctime ≤ 2 * Ctime := by
        rw [two_mul]; exact le_self_add
      exact this) (by linarith) (le_min hT hTm)

/-- **`hfinX` 搬运（`_JP`，PROVED）**：K 层基点到 seed 点的 edist 有限 ⇒ E 帧（`Tn^E = τ`）同形有限
（`edist_congr_P6JA` + seed 兼容 `hseed`，同 `hgood_of_eventPrefix_P6JA` 的 `e2` 段）。 -/
theorem hfinX_of_eventPrefix_JP (j : Fin K.eventCount) {T : ℝ}
    (hjT : K.time j.castSucc < T) (hTj : T < K.time j.succ)
    (E : ObservedHistory.{u}) (hE : E = (K.eventPrefix j T hjT hTj).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (hsTE : τ ≤ τ) (hasE : aE ≤ τ)
    (pTE : (E.stageAt τ).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
      (E.activeStage_mono haTE) pTE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    (hfin : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
        (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
          (K.toHistory.activeStage_mono hsTK)) yK ≠ ⊤) :
    riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
        (seedE.point (E.activeStage τ) (E.activeStage_mono hasE) (E.activeStage_mono hsTE))
        yE ≠ ⊤ := by
  subst hE
  have hidxτ : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) = K.toHistory.activeStage τ' :=
    Fin.ext (K.eventPrefix_activeStage_val j hjT hTj τ τ' hττ)
  have hmetτ := K.eventPrefix_stageMetric j hjT hTj
    ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ
  rw [hττ] at hmetτ
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hasE)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e3 := congrArg (fun w : ℝ => riemannianEDistOf
    ((K.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ) w)
    (seedE.point ((K.eventPrefix j T hjT hTj).toHistory.activeStage τ)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hasE)
      ((K.eventPrefix j T hjT hTj).toHistory.activeStage_mono hsTE)) yE) hττ
  exact fun h => hfin (e2.symm.trans (e3.symm.trans h))

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
