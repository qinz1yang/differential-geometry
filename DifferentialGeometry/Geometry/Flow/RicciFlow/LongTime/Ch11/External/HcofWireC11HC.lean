import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.P5LinkedSupplyC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialPhysicalVolumeEvent

set_option autoImplicit false

/-!
# S-CH11-HCOF G2：outer 的共尾 request ⇒ S14 `hcof` 逐字形（后缀 `_C11HC`）

S14-GAP A：outer（`SH/PreparedSpatialPhysicalVolumeEvent:65`）原来只知 `request` 的
`ε ≤ 1/2`、`D > transitionEnd + 10`、`m ≥ 4`，没有共尾性，所以 `lateLinkedRecordsSupply_of_outer_C12X`
的前提 `hcof` 供不出来。S-CH11-HCOF 的 patch（`PolicyReserveQuality` / `BirthVolumeOrReserve` /
`PhysicalVolumeEvent` 三个 tracked 文件）在源头把 `request` 换成共尾 request
`preparedSpatialCofinalRequest`，outer 结论里 `∃ request` 多带共尾子句 `hCof`：
`req.1 ≤ (E + 1)⁻¹ ∧ E ≤ req.2.1 ∧ E ≤ req.2.2.1`（对任意 `E ≥ 0`）。

本文件：
* `hcof_of_cofinal_request_C11HC`：`hCof`（`E = √(3 ^ n) → ∞`）+ retention 族 `W` 的
  `fine_accuracy / fine_radius / fine_order` ⇒ `hcof` 逐字形
  （`lateLinkedRecordsSupply_of_outer_C12X` 的显式前提）。
* `example`：剥开 patch 后的 outer 结论，`hfixed / hrc / hmiOuter / hblockOuter` 取自 outer tuple，
  `hcof` 取自上一条，适配器 `lateLinkedRecordsSupply_of_outer_C12X` 只剩 `hlink`（S14-GAP B，S10-link
  同源缺口）未供。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.GeneralFlow
open Set Filter

namespace GC.LongTime.Ch11

universe u

/-- **outer 共尾 request ⇒ `hcof`**：`request` 满足共尾子句 `hCof`（`E → ∞` 时 `ε → 0`、`D → ∞`、
`m → ∞`），`W` 是 outer 的 retention 族（`εcut n / Dcut n / mcut n` 取 `request` 在
`E = √(3 ^ n)` 处的值，`rNext n > 0`），则 fine 模型窗口共尾。结论即
`lateLinkedRecordsSupply_of_outer_C12X` / `lateLinkedRecordsSupply_of_astra_C12X` 的 `hcof` 逐字形。 -/
theorem hcof_of_cofinal_request_C11HC {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} (S : PreparedSpatialChain pBase C P g)
    (request : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℕ × ℝ) (rNext : ℕ → ℝ)
    (hCof : ∀ (Aact E rTerm qDeriv ρ : ℝ), 0 ≤ E → 0 < rTerm → 0 < qDeriv → 0 < ρ →
      let req := request Aact E rTerm qDeriv ρ
      req.1 ≤ (E + 1)⁻¹ ∧ E ≤ req.2.1 ∧ E ≤ (req.2.2.1 : ℝ))
    (hrNext : ∀ n, 0 < rNext n)
    (W : ∀ n, PreparedSpatialStepRetention (S.state n) (S.state (n + 1)) (S.accuracy n)
      (1 / ((n : ℝ) + 2)) (preparedSpatialPhysicalQualityRequest request n (rNext n)).1
      (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.1
      (preparedSpatialPhysicalQualityRequest request n (rNext n)).2.2.1) :
    ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
  intro D ζ m hζ
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_ge_atTop
      (max (max D ζ⁻¹) (m : ℝ) ^ 2))
  refine ⟨k₀, fun k hk => ?_⟩
  have hX : max (max D ζ⁻¹) (m : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ k) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (hk₀ k hk))
  have hDX : D ≤ Real.sqrt ((3 : ℝ) ^ k) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hζX : ζ⁻¹ ≤ Real.sqrt ((3 : ℝ) ^ k) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hmX : (m : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ k) := (le_max_right _ _).trans hX
  have hr := hrNext k
  obtain ⟨hε, hD, hm⟩ := hCof
    (preparedSpatialPhysicalActionFactor (12 * (3 : ℝ) ^ k) * Real.sqrt (2 * (3 : ℝ) ^ k))
    (Real.sqrt ((3 : ℝ) ^ k)) (rNext k / 100) ((rNext k ^ 2)⁻¹) 1
    (Real.sqrt_nonneg _) (by positivity) (by positivity) (by norm_num)
  have hacc := (W k).fine_accuracy
  have hrad := (W k).fine_radius
  have hord := (W k).fine_order
  simp only [preparedSpatialPhysicalQualityRequest, ite_eq_left hr] at hacc hrad hord
  refine ⟨hDX.trans (hD.trans hrad), ?_, ?_⟩
  · refine hacc.trans (hε.trans ?_)
    exact (inv_le_comm₀ (by positivity) hζ).2 (hζX.trans (by linarith))
  · exact Nat.cast_le.1 (hmX.trans (hm.trans (Nat.cast_le.2 hord)))

/-- **接线 example**：patch 后的 outer 结论给出 `hfixed / hrc / hmiOuter / hblockOuter`（outer tuple 的
合取项）与 `hcof`（上面的定理），`lateLinkedRecordsSupply_of_outer_C12X` 只剩 `hlink`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (Dstar : ℝ)
    (hDstar : StandardCap.transitionEnd < Dstar) : True := by
  obtain ⟨_εcap, _cBG, -, -, _Cdist, -, _constants, makeInitial⟩ :=
    exists_surgery_with_same_flow_volume_or_reserve_and_positive_event_restart_with_closed_support_and_window_scale_bound.{u}
      Dstar hDstar
  obtain ⟨_a₀, -, -, _cMax, -, _κVol, -, _cSpatial, -, _κLarge, -, hSelected⟩ := makeInitial P g
  obtain ⟨-, -, -, -, _pBase, _base, -, -, -, -, -, -, -, -, -, request, -, hCof, -, -, -,
      hChain⟩ := hSelected
  obtain ⟨S, _future, rNext, -, -, -, -, -, hState, -, -, W, F, q, _κ, records, hTuple⟩ := hChain
  have hcof := hcof_of_cofinal_request_C11HC S request rNext hCof (fun n => (hState n).1) W
  casesm* _ ∧ _
  exact (fun _ => trivial)
    (lateLinkedRecordsSupply_of_outer_C12X S W F q records ‹_› ‹_› ‹_› ‹_› hcof)

end GC.LongTime.Ch11
