import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants

set_option autoImplicit false

/-!
# S-CH11-REPROVE-D (G1)：S4 `CanonicalConstantsSupply_C11S` 的重证

astra 的 `ClosedBirthConstants`（`SH/PreparedSpatialState.lean:17`）是一个 reference-only 的结构：
它一次性选定 `epsilon C1 C2 C1s C2s Cs tauMin Cbirth Ctime Cgrad` 与字段
`epsilon_pos / epsilon_small / C1_ge_one / C2_ge_one / C1s_ge_one / C2s_ge_one / Cbirth_ge_one /
epsilon_cone`，而 astra 的 tuple `exists_surgery_with_spatial_control_and_decay` 用
`ε := C.epsilon`、`C1 := max C.C1s C.Cbirth`、`C2 := max C.C2s (max C.Cbirth Cgrad)`。
这里**不引入该结构**，用显式数值 binder 重证：

* `canonicalConstantsSupply_of_closedBirth_C11RD`：`ClosedBirthConstants` 的数值字段 ⇒ S4（`max` 形）；
* `exists_canonicalConstantsSupply_C11RD`：S4 无条件非空（`ε = 1/200`、`C1 = C2 = 1`）；
* P4（ch12 `epsilon ≤ εKL70_O2`，A12′ 的加强版 S4）：树内 `coneAccuracy`（`ClosedBirthConstants.epsilon_cone`）
  `coneAccuracy < 1/100`，所以 `0 < ε ≤ coneAccuracy` 蕴含 `epsilon_small`，且 `ε = coneAccuracy` 给出
  带 cone 条款的非空性 `exists_canonicalConstantsSupply_cone_C11RD`；
* 常数单调：S4 对 `C1 C2` 上调稳定（S5 的 witness 用 `enlargeConstants` 同向上调）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

/-- 树内 `coneAccuracy < 1/100`：astra `ClosedBirthConstants.epsilon_cone` 蕴含 `epsilon_small`。 -/
theorem coneAccuracy_lt_C11RD : coneAccuracy < 1 / 100 := by
  unfold coneAccuracy
  rw [div_lt_iff₀ (by norm_num)]
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- astra `ClosedBirthConstants` 的数值字段 ⇒ S4（`ε := epsilon`，`C1 := max C1s Cbirth`，
`C2 := max C2s (max Cbirth Cgrad)`，与 tuple 的取法逐字）。 -/
theorem canonicalConstantsSupply_of_closedBirth_C11RD {ε C1s C2s Cbirth Cgrad : ℝ}
    (hε : 0 < ε) (hεs : ε < 1 / 100) (hC1s : 1 ≤ C1s) (hC2s : 1 ≤ C2s) :
    CanonicalConstantsSupply_C11S ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) :=
  ⟨hε, hεs, hC1s.trans (le_max_left _ _), hC2s.trans (le_max_left _ _)⟩

/-- S4 无条件非空：`ε = 1/200`、`C1 = C2 = 1`。 -/
theorem exists_canonicalConstantsSupply_C11RD :
    ∃ ε C1 C2 : ℝ, CanonicalConstantsSupply_C11S ε C1 C2 :=
  ⟨1 / 200, 1, 1, by norm_num [CanonicalConstantsSupply_C11S]⟩

/-- P4 形：`0 < ε ≤ coneAccuracy` 蕴含 S4 的 `epsilon_small`，故 S4 在 cone 条款下仍成立。 -/
theorem canonicalConstantsSupply_of_le_cone_C11RD {ε C1 C2 : ℝ} (hε : 0 < ε)
    (hcone : ε ≤ coneAccuracy) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    CanonicalConstantsSupply_C11S ε C1 C2 :=
  ⟨hε, hcone.trans_lt coneAccuracy_lt_C11RD, hC1, hC2⟩

/-- S4 带 cone 条款（A12′ 的加强版 S4，`epsilon_cone`）非空：`ε = coneAccuracy`。 -/
theorem exists_canonicalConstantsSupply_cone_C11RD :
    ∃ ε C1 C2 : ℝ, CanonicalConstantsSupply_C11S ε C1 C2 ∧ ε ≤ coneAccuracy :=
  ⟨coneAccuracy, 1, 1,
    canonicalConstantsSupply_of_le_cone_C11RD coneAccuracy_pos le_rfl le_rfl le_rfl, le_rfl⟩

/-- S4 对 `C1 C2` 上调稳定。 -/
theorem canonicalConstantsSupply_mono_C11RD {ε C1 C2 C1' C2' : ℝ}
    (h : CanonicalConstantsSupply_C11S ε C1 C2) (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    CanonicalConstantsSupply_C11S ε C1' C2' :=
  ⟨h.1, h.2.1, h.2.2.1.trans h1, h.2.2.2.trans h2⟩

/-! ## Consumers -/

/-- consumer：astra tuple 的取法 `C1 := max C1s Cbirth`、`C2 := max C2s (max Cbirth Cgrad)`
在 cone 条款 `ε ≤ coneAccuracy`（P4）下给出 S4（`epsilon_small` 由 cone 推出，不另设）。 -/
example {ε C1s C2s Cbirth Cgrad : ℝ} (hε : 0 < ε) (hcone : ε ≤ coneAccuracy)
    (hC1s : 1 ≤ C1s) (hC2s : 1 ≤ C2s) :
    CanonicalConstantsSupply_C11S ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) :=
  canonicalConstantsSupply_of_closedBirth_C11RD hε (hcone.trans_lt coneAccuracy_lt_C11RD)
    hC1s hC2s

/-- consumer：S4 的存在性可直接填进 W1 的第一个 `∃ ε C1 C2` 合取项（与 `SurgerySupplies_C11S`
里 S4 的位置同形）。 -/
example : ∃ ε C1 C2 : ℝ, CanonicalConstantsSupply_C11S ε C1 C2 ∧ ε ≤ coneAccuracy ∧
    CanonicalConstantsSupply_C11S ε (max C1 1) (max C2 1) := by
  obtain ⟨ε, C1, C2, h, hε⟩ := exists_canonicalConstantsSupply_cone_C11RD
  exact ⟨ε, C1, C2, h, hε, canonicalConstantsSupply_mono_C11RD h (le_max_left _ _)
    (le_max_left _ _)⟩

end GC.LongTime.Ch11
