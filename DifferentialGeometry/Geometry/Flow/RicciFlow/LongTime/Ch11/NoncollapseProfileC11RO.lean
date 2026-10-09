import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryNoncollapsePrefixC11RO
import DifferentialGeometry.Analysis.Order.CommonProfile

set_option autoImplicit false

/-!
# O-CH11-REPROVE-O (G2)：S6 归约到逐层 noncollapse（tower prefix + common profile）

astra `exists_surgery_with_spatial_control`（`SH/PreparedSpatialSurgery.lean:23`，reference-only）
从 chain 的每个 observation 拿到**逐层** noncollapse
`hnc n : 0 < κ n ∧ (T.history n).NoncollapsedBefore (κ n) C.epsilon n`（`κ : ℕ → ℝ`），再用
`commonProfile κ`（antitone、正、`< κ ⌈t⌉`）与 tower 的 prefix 关系，把它变成 W1 的 noncollapse 条款
`∀ n, ∀ t ∈ [0, n], (T.history n).NoncollapsedBefore (κ' t) ε t`（:162–176）。这里在树内重证这一步：

* `RetainedCoreHistory.noncollapsedBefore_kappa_mono_C11RO`：`κ' ≤ κ` 时 noncollapse 变弱。
* `RetainedCoreObservationTower.history_isPrefixOf_C11RO`：`m ≤ n` ⇒ history `m` 是 history `n` 的
  prefix（tower 的 `successor` 字段 + `IsPrefixOf.trans`）。
* `exists_noncollapse_profile_of_levels_C11RO`：逐层 noncollapse ⇒ W1 条款（κ' = `commonProfile κ`；
  `t ∈ [0, n]` 在 history `⌈t⌉` 上读，再用 G1 的 `noncollapsedBefore_of_isPrefixOf_C11RO` 推到 `n`）。
  结论的三项与 ASM `supply6_of_astra_C11A` 的 binder `hκ / hκanti / hnc` 逐字同形。
* `noncollapseSupply_of_levels_C11RO`、`noncollapseSupply_iff_levels_C11RO`：
  `(∃ κ, NoncollapseSupply_C11S F κ ε) ↔`
  `∀ n : ℕ, ∃ k, 0 < k ∧ (F.tower.history n).NoncollapsedBefore k ε n`。
  即 S6 **恰好**是"每个 history 层 `n` 在尺度 `ε` 以下、时刻 `n` 之前有某个正 κ 的 noncollapse"；
  antitone profile 不额外要求任何东西。剩下的数学内容（逐层 κ 的产生 = L-geometry / reduced volume 链）
  见 design `docs/geometrization/chapter8/design-C11-S6-kappa-chain-C11RO-20261006.md`。
-/

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped ENNReal

namespace GC.LongTime.Ch11

universe u

/-- noncollapse 常数变小时结论变弱（`κ' ≤ κ`）。 -/
theorem noncollapsedBefore_kappa_mono_C11RO {H : RetainedCoreHistory.{u}} {κ κ' ρ t₀ : ℝ}
    (hκ : κ' ≤ κ) (h : H.NoncollapsedBefore κ ρ t₀) : H.NoncollapsedBefore κ' ρ t₀ :=
  fun t p r ht hr hball =>
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hκ) le_rfl).trans (h t p r ht hr hball)

/-- tower 的相邻两层：history `n` 是 history `n + 1` 的 prefix（`successor` 字段）。 -/
theorem history_isPrefixOf_succ_C11RO {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (n : ℕ) :
    (T.history n).toHistory.IsPrefixOf (T.history (n + 1)).toHistory := by
  have hle : (T.history n).horizon ≤ (T.history (n + 1)).horizon := by
    rw [T.horizon_eq, T.horizon_eq]
    exact_mod_cast Nat.le_succ n
  refine ⟨hle, ?_⟩
  have ha : (⟨(T.history n).toHistory.horizon, (T.history n).toHistory.horizon_nonneg, hle⟩ :
      Icc (0 : ℝ) (T.history (n + 1)).toHistory.horizon) =
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        change (n : ℝ) ≤ (T.history (n + 1)).horizon
        rw [T.horizon_eq]
        exact_mod_cast Nat.le_succ n⟩ :=
    Subtype.ext (T.horizon_eq n)
  rw [ha]
  exact T.successor n

/-- tower 的任意两层：`m ≤ n` ⇒ history `m` 是 history `n` 的 prefix。 -/
theorem history_isPrefixOf_C11RO {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) {m n : ℕ} (hmn : m ≤ n) :
    (T.history m).toHistory.IsPrefixOf (T.history n).toHistory := by
  induction n, hmn using Nat.le_induction with
  | base => exact ObservedHistory.IsPrefixOf.refl _
  | succ n _ ih => exact ih.trans (history_isPrefixOf_succ_C11RO T n)

/-- **逐层 noncollapse ⇒ W1 的 noncollapse 条款**：存在正、antitone 的 `κ'`，使每层 history `n`
在 `[0, n]` 的每个时刻 `t` 之前以 `κ' t` noncollapse（尺度 `ρ`）。 -/
theorem exists_noncollapse_profile_of_levels_C11RO {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (κ : ℕ → ℝ) (ρ : ℝ)
    (hnc : ∀ n : ℕ, 0 < κ n ∧ (T.history n).NoncollapsedBefore (κ n) ρ n) :
    ∃ κ' : ℝ → ℝ, (∀ t : ℝ, 0 < κ' t) ∧ Antitone κ' ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (T.history n).NoncollapsedBefore (κ' t) ρ t := by
  have hpos : ∀ n, 0 < κ n := fun n => (hnc n).1
  refine ⟨GC.GeneralFlow.commonProfile κ, GC.GeneralFlow.commonProfile_pos hpos,
    GC.GeneralFlow.commonProfile_antitone κ, ?_⟩
  intro n t ht
  have hκ : GC.GeneralFlow.commonProfile κ t ≤ κ (Nat.ceil t) :=
    (GC.GeneralFlow.commonProfile_lt_budget hpos t (Nat.ceil t)
      (Nat.ceil_le_floor_add_one t)).le
  have hsmall : (T.history (Nat.ceil t)).NoncollapsedBefore
      (GC.GeneralFlow.commonProfile κ t) ρ t :=
    noncollapsedBefore_kappa_mono_C11RO hκ
      ((T.history (Nat.ceil t)).noncollapsedBefore_mono (Nat.le_ceil t) (hnc (Nat.ceil t)).2)
  exact RetainedCoreHistory.noncollapsedBefore_of_isPrefixOf_C11RO
    (history_isPrefixOf_C11RO T (Nat.ceil_le.mpr ht.2))
    (by rw [T.horizon_eq]; exact Nat.le_ceil t) hsmall

/-- **S6 ⇐ 逐层 noncollapse**（同时给出 W1 的三项，供 ASM 的 `supply6_of_astra_C11A` 直接使用）。 -/
theorem noncollapseSupply_of_levels_C11RO {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (κ : ℕ → ℝ) (ε : ℝ)
    (hnc : ∀ n : ℕ, 0 < κ n ∧ (F.tower.history n).NoncollapsedBefore (κ n) ε n) :
    ∃ κ' : ℝ → ℝ, NoncollapseSupply_C11S F κ' ε ∧ (∀ t : ℝ, 0 < κ' t) ∧ Antitone κ' ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ' t) ε t := by
  obtain ⟨κ', hκ, hanti, hall⟩ := exists_noncollapse_profile_of_levels_C11RO F.tower κ ε hnc
  refine ⟨κ', ⟨fun t _ => hκ t, fun s _ t _ hst => hanti hst, fun n => ?_⟩, hκ, hanti, hall⟩
  exact hall n (n : ℝ) ⟨Nat.cast_nonneg n, le_rfl⟩

/-- **S6 的精确归约**：存在满足 S6 的 κ ⇔ 每层 history `n` 有某个正 κ 的 `NoncollapsedBefore _ ε n`。 -/
theorem noncollapseSupply_iff_levels_C11RO {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε : ℝ} :
    (∃ κ : ℝ → ℝ, NoncollapseSupply_C11S F κ ε) ↔
      ∀ n : ℕ, ∃ k : ℝ, 0 < k ∧ (F.tower.history n).NoncollapsedBefore k ε n := by
  constructor
  · rintro ⟨κ, hpos, _, hnc⟩ n
    exact ⟨κ n, hpos n (Nat.cast_nonneg n), hnc n⟩
  · intro h
    choose κ hκ using h
    obtain ⟨κ', hS6, -⟩ := noncollapseSupply_of_levels_C11RO F κ ε hκ
    exact ⟨κ', hS6⟩

/-! ## consumer -/

/-- consumer：逐层 noncollapse + 其余八个供给 ⇒ SKEL 的 bundle `SurgerySupplies_C11S`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (records : CutoffRecords_C11S F q)
    (ε C1 C2 : ℝ) (α : ℝ → ℝ → ℝ) (κ : ℕ → ℝ)
    (h1 : AccuracyDecaySupply_C11S q.delta) (h2 : RadiusAntitoneSupply_C11S q)
    (h3 : CanonicalWindowsSupply_C11S records) (h4 : CanonicalConstantsSupply_C11S ε C1 C2)
    (h5 : CanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hlev : ∀ n : ℕ, 0 < κ n ∧ (F.tower.history n).NoncollapsedBefore (κ n) ε n)
    (h7 : LargerBallAccuracySupply_C11S q.delta α)
    (h8 : LargerBallScalarLargeSupply_C11S F q.delta α) (h9 : RecentCutoffSupply_C11S records) :
    SurgerySupplies_C11S P g := by
  obtain ⟨κ', h6, -⟩ := noncollapseSupply_of_levels_C11RO F κ ε hlev
  exact ⟨F, q, records, ε, C1, C2, κ', α, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end GC.LongTime.Ch11
