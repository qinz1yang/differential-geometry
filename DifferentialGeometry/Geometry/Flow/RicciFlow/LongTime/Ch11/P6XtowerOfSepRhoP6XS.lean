import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NRPrimeTowerC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.TimeDerivativeC12X

set_option autoImplicit false

/-!
# XSUP 局部核：合同 X 的四子句 ⇐ 时间导数供给 + (SEP-ρ) cap 窗实例（O-CH11-NRPRIME-WIRE XSUP，后缀 `_P6XS`）

`xclauses_of_supply_sep_P6XS`（PROVED，实例级、无总前提）：tower `F` 上的先验供给
`TimeDerivativeSupply_C11E F q.neckRadius C`（对**所有**点 `y`：`ρ(τ)⁻² < R ⇒ |∂R| ≤ C·R²`）、
`q.neckRadius` antitone、`T(e₂⁺) ≤ t`，以及 (SEP-ρ) 右支在该实例的不等式
`(q.neckRadius t ^ 2)⁻¹ ≤ Cbirth·q₁`（q₁ = e₁ 窗口 static cap 尺度）
⇒ Xtower 的 X 实例四子句（文本逐字取自 G1 Xtower，生成器 `gen/gen_xs.py`），取 `W := univ`：hW / htube 平凡；
hderivW / hfinalW 的 τ 都 ≤ T(e₂⁺) ≤ t，antitone ⇒ `ρ(τ)⁻² ≤ ρ(t)⁻² ≤ Cbirth·q₁ < R`，供给即付。
这是 "supply-threaded twin"（X → (SEP-ρ⁺)）的核心一步；整链 twin 未做（XSUP G0：Xtower 的 C 固定而供给常数为
`Γf.Ctime`、且供给只对 BlockTower 链有 producer ⇒ 现形 BLOCKED，见 state）。consumer：供给由树内
`timeDerivativeSupply_of_astra_C12X`（retention 链，常数 `Γf.Ctime`）付。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **XSUP 局部核（PROVED）**：X 实例四子句 ⇐ 供给 + (SEP-ρ) 实例不等式（`W := univ`）。 -/
theorem xclauses_of_supply_sep_P6XS {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q params : CutoffParameters) (C : ℝ≥0)
    (hTD : TimeDerivativeSupply_C11E F q.neckRadius C) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory e params)
    (Cbirth Rmod : ℝ) (n : ℕ) (t : ℝ) (e₁ e₂ : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event e₁).RetainedBoundaryIndex)
    (he₂t : (F.tower.history n).time e₂.succ ≤ t)
    (hsep : (q.neckRadius t ^ 2)⁻¹ ≤ Cbirth * ((records n e₁).static b).neck.scale) :
    let H := (F.tower.history n).toHistory
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
            C * (H.event e₂).incoming.flow.scalar τ x' ^ 2) := by
  intro H
  have hthr : ∀ τ : ℝ, 0 ≤ τ → τ ≤ t →
      (q.neckRadius τ ^ 2)⁻¹ ≤ Cbirth * ((records n e₁).static b).neck.scale := by
    intro τ h0 hτt
    have ht0 : 0 ≤ t := h0.trans hτt
    have hpos : 0 < q.neckRadius t := q.neckRadius_pos t ht0
    have hle : q.neckRadius t ≤ q.neckRadius τ :=
      hanti (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr ht0) hτt
    exact (inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)).trans hsep
  have htime0 : ∀ j : Fin ((F.tower.history n).eventCount + 1), 0 ≤ (F.tower.history n).time j :=
    fun j => H.time_nonneg j
  refine ⟨fun _ => univ, fun _ => isOpen_univ, fun _ _ _ _ _ _ => mem_univ _, ?_, ?_⟩
  · intro i _ hi2 x' _ τ hτ hR
    have hτt : τ ≤ t := by
      have h1 : (F.tower.history n).time i.succ ≤ (F.tower.history n).time e₂.castSucc :=
        (F.tower.history n).time_strictMono.monotone hi2
      have h2 : (F.tower.history n).time e₂.castSucc ≤ (F.tower.history n).time e₂.succ :=
        (F.tower.history n).time_strictMono.monotone Fin.castSucc_lt_succ.le
      linarith [hτ.2]
    exact hTD.1 n i x' τ hτ (lt_of_le_of_lt (hthr τ ((htime0 _).trans hτ.1.le) hτt) hR)
  · intro x' _ τ hτ hR
    exact hTD.1 n e₂ x' τ hτ
      (lt_of_le_of_lt (hthr τ ((htime0 _).trans hτ.1.le) (hτ.2.le.trans he₂t)) hR)

/-- **consumer**：供给由树内 retention 链 producer `timeDerivativeSupply_of_astra_C12X` 付（常数 `Γf.Ctime`），
得到该 tower 实例上的 X 四子句（`C := Γf.Ctime`）。 -/
example {pBase : CutoffParameters} {Γf : ClosedBirthConstants} {P : OrientedThreeStage.{u}}
    {g : P.Metric} (S : PreparedSpatialChain pBase Γf P g) (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (q params : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hdiagonal : ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v)
    (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
      GeometricCutoffRecord (F.tower.history n).toHistory e params)
    (Cbirth : ℝ) (n : ℕ) (t : ℝ) (e₁ e₂ : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event e₁).RetainedBoundaryIndex)
    (he₂t : (F.tower.history n).time e₂.succ ≤ t)
    (hsep : (q.neckRadius t ^ 2)⁻¹ ≤ Cbirth * ((records n e₁).static b).neck.scale) :
    ∃ W : ∀ i : Fin ((F.tower.history n).toHistory.eventCount + 1),
      Set ((F.tower.history n).toHistory.stage i).Carrier, ∀ i, IsOpen (W i) :=
  have h := xclauses_of_supply_sep_P6XS F q params Γf.Ctime
    (timeDerivativeSupply_of_astra_C12X S εcut Dcut mcut W hshift hoffset F hTower q hanti
      hdiagonal)
    hanti records Cbirth 0 n t e₁ e₂ b he₂t hsep
  let ⟨W', hW', _⟩ := h
  ⟨W', hW'⟩

end GC.LongTime.Ch11
