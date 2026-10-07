import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopC11GT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineTowerC11Q6

set_option autoImplicit false

/-!
# S-CH11-GAPTOP2 G1：`hK` 的 budget 形——动态请求预算证书 + W0 生产（后缀 `_C11GT2`）

R-C11-6 D-13(1)：`a12EnhancedFull_of_gaps_C11GT` 的 `hK` 对**任意** `PreparedSpatialChain` 成立，没有
"该 chain 的请求支配 κ 三类动态请求"的前提；W0 只强制 `RequestCofinal_C11W4 ∧ accuracyCap ≤ 1/8646`，
所以 R1（FINEPACK）的 construction-specific 产物对不上全称 `hK`。修正形（审稿 Q5 原文）：
`hK` 只对**携带实际请求预算证书**的 tower / chain 成立，W0 选择时生产该证书；
预算谓词允许依赖 `(j, X, ℓ, req)`（lookahead 先选的 `ℓ.rNext`，不只是 `Q(j, req)`）。

* `BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req`：FINEPACK `budgetChoice_dominating_C11Q6`
  结论的四块支配（本块 K3 @ `ℓ.rNext`、上一块 K3 @ `X.radius`、event @ `ℓ.rNext`、URE @ `ℓ.rNext`）逐字；
  `Λrec := pB.recenterConstant`、`Cderiv := Γ.Ctime`（`exists_blockData_C11Q6` 同口径）。
* `BudgetCertificate_C11GT2.mono`：对"更强请求"（`epsCut` 更小、`Dcut` / `mcut` 更大、`cap` 更小）向上封闭。
* `budgetChoice_certified_C11GT2`：**W0 的第二版（定理）**：支配四个 chooser ∧ `RequestCofinal_C11W4 j` ∧
  `accuracyCap ≤ δ₀`（FINEPACK HANDOVER 第 3 项：同一 `budgetChoice` 再 join `BlockRequest_C11W.cofinal`）。
* `exists_budget_tower_C11GT2`：`BlockStep` 族 + 起点 ⇒ tower `T`，逐块带证书 ∧ 共尾 ∧ `cap ≤ δ₀`
  （`tower_of_blockSteps_policy_C11Q6`，谓词看 `X ℓ req`）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **动态请求预算证书**（形参照 FINEPACK `budgetChoice_dominating_C11Q6` 的结论）：块 `j` 在 lookahead
`ℓ`（`rNext = ℓ.rNext`）之后选的请求 `req` 支配 K3 / event / URE 三类 κ 动态请求 chooser
（本块输入 `ℓ.rNext`；K3 还要支配上一块输入 `X.radius`）。 -/
def BudgetCertificate_C11GT2 (Λrec : ℝ) (Cderiv : ℝ≥0) (j : ℕ) (X : BlockState_C11W pBase C P g j)
    (ℓ : BlockLookahead_C11W X) (req : BlockRequest_C11W) : Prop :=
  ((k3BlockConsts_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.1 ≤ req.Dcut ∧
      (k3BlockConsts_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.2 ≤ req.mcut ∧
      req.epsCut ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.1 ∧
      req.accuracyCap ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv j ℓ.rNext).1) ∧
    ((k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.2.1 ≤ req.Dcut ∧
      (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.2.2 ≤ req.mcut ∧
      req.epsCut ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).2.1 ∧
      req.accuracyCap ≤ (k3BlockConsts_C11Q6 P g Λrec Cderiv (j - 1) X.radius).1) ∧
    ((eventBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.1 ≤ req.Dcut ∧
      (eventBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.1 ≤ req.mcut ∧
      req.epsCut ≤ (eventBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).1 ∧
      req.accuracyCap ≤ (eventBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.2) ∧
    ((ureBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.1 ≤ req.Dcut ∧
      (ureBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.1 ≤ req.mcut ∧
      req.epsCut ≤ (ureBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).1 ∧
      req.accuracyCap ≤ (ureBlockRequest_C11Q6 P g Λrec Cderiv j ℓ.rNext).2.2.2)

/-- 预算证书对更强的请求（`epsCut` 更小、`Dcut` / `mcut` 更大、`accuracyCap` 更小）向上封闭。 -/
theorem BudgetCertificate_C11GT2.mono {Λrec : ℝ} {Cderiv : ℝ≥0} {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {ℓ : BlockLookahead_C11W X}
    {req req' : BlockRequest_C11W} (h : BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req)
    (he : req'.epsCut ≤ req.epsCut) (hD : req.Dcut ≤ req'.Dcut) (hm : req.mcut ≤ req'.mcut)
    (hc : req'.accuracyCap ≤ req.accuracyCap) :
    BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req' := by
  unfold BudgetCertificate_C11GT2 at h ⊢
  obtain ⟨⟨a₁, a₂, a₃, a₄⟩, ⟨b₁, b₂, b₃, b₄⟩, ⟨c₁, c₂, c₃, c₄⟩, ⟨d₁, d₂, d₃, d₄⟩⟩ := h
  exact ⟨⟨a₁.trans hD, a₂.trans hm, he.trans a₃, hc.trans a₄⟩,
    ⟨b₁.trans hD, b₂.trans hm, he.trans b₃, hc.trans b₄⟩,
    ⟨c₁.trans hD, c₂.trans hm, he.trans c₃, hc.trans c₄⟩,
    ⟨d₁.trans hD, d₂.trans hm, he.trans d₃, hc.trans d₄⟩⟩

/-- **W0 第二版（定理）**：lookahead `ℓ`（`ℓ.rNext > 0`）之后存在合格请求，它携带预算证书
（支配 K3 / event / URE 的动态请求）、`RequestCofinal_C11W4 j`，且 `accuracyCap ≤ δ₀`。
证明：FINEPACK 的 `budgetChoice_dominating_C11Q6` 给支配请求，再与共尾请求
`⟨1/(j+2), j+1, j, δ₀⟩` 取 join（`epsCut` 取 min、`Dcut` / `mcut` 取 max、`cap` 取 min）。 -/
theorem budgetChoice_certified_C11GT2 {Λrec : ℝ} (hΛ : 0 < Λrec) (Cderiv : ℝ≥0) (δ₀ : ℝ)
    (hδ₀ : 0 < δ₀) (j : ℕ) (X : BlockState_C11W pBase C P g j) {ℓ : BlockLookahead_C11W X}
    (hrNext : 0 < ℓ.rNext) :
    ∃ req : BlockRequest_C11W, RequestReady_C11W X req ∧
      BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req ∧ RequestCofinal_C11W4 j req ∧
        req.accuracyCap ≤ δ₀ := by
  obtain ⟨req₀, hready, h₁, h₂, h₃, h₄⟩ :=
    budgetChoice_dominating_C11Q6 P g hΛ Cderiv j X hrNext
  have hcert : BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req₀ := by
    unfold BudgetCertificate_C11GT2
    exact ⟨h₁, h₂, h₃, h₄⟩
  have hj2 : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
  refine ⟨⟨min req₀.epsCut (1 / ((j : ℝ) + 2)), max req₀.Dcut ((j : ℝ) + 1), max req₀.mcut j,
    min req₀.accuracyCap δ₀⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    hcert.mono (min_le_left _ _) (le_max_left _ _) (le_max_left _ _) (min_le_left _ _),
    ⟨min_le_right _ _, le_max_right _ _, le_max_right _ _⟩, min_le_right _ _⟩
  · exact lt_min hready.cap_pos hδ₀
  · exact (min_le_left _ _).trans hready.cap_le_level
  · exact (min_le_left _ _).trans hready.cap_le_quarter
  · exact lt_min hready.epsCut_pos hj2
  · exact hready.Dcut_pos.trans_le (le_max_left _ _)

/-- **预算 tower**：`BlockStep` 族 + 起点 ⇒ tower `T`，每块的请求携带预算证书、共尾、`accuracyCap ≤ δ₀`。
（`hK` 的 budget 形 binder 的作用对象；`tower_of_blockSteps_policy_C11Q6` 的谓词看 `X ℓ req`。） -/
theorem exists_budget_tower_C11GT2 {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} {Λrec : ℝ}
    (hΛ : 0 < Λrec) (Cderiv : ℝ≥0) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, ∀ j,
      BudgetCertificate_C11GT2 Λrec Cderiv j (T.block j) (T.lookahead j) (T.request j) ∧
        RequestCofinal_C11W4 j (T.request j) ∧ (T.request j).accuracyCap ≤ δ₀ := by
  obtain ⟨T, -, hQ⟩ := tower_of_blockSteps_policy_C11Q6
    (fun j X ℓ req => BudgetCertificate_C11GT2 Λrec Cderiv j X ℓ req ∧
      RequestCofinal_C11W4 j req ∧ req.accuracyCap ≤ δ₀)
    (fun j X _ ℓ hℓ => by
      obtain ⟨req, h₁, h₂, h₃, h₄⟩ :=
        budgetChoice_certified_C11GT2 hΛ Cderiv δ₀ hδ₀ j X hℓ.rNext_pos
      exact ⟨req, h₁, h₂, h₃, h₄⟩) hstep X₀ hX₀ hhist hrad
  exact ⟨T, hQ⟩

/-- consumer：任何"对携带预算证书的 tower 成立"的性质 `Φ`（`hK` 的 budget 形）在 W0 生产的 tower 上
成立，且该 tower 同时满足 A12′ 顶层要的共尾 + `accuracyCap ≤ δ₀`。 -/
example {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} {Λrec : ℝ} (hΛ : 0 < Λrec) (Cderiv : ℝ≥0)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1)
    (Φ : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve → Prop)
    (hΦ : ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      (∀ j, BudgetCertificate_C11GT2 Λrec Cderiv j (T.block j) (T.lookahead j) (T.request j)) →
        Φ T) :
    ∃ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, Φ T ∧
      ∀ j, RequestCofinal_C11W4 j (T.request j) ∧ (T.request j).accuracyCap ≤ 1 / 8646 := by
  obtain ⟨T, hT⟩ := exists_budget_tower_C11GT2 hΛ Cderiv (1 / 8646) (by norm_num) hstep X₀ hX₀
    hhist hrad
  exact ⟨T, hΦ T fun j => (hT j).1, fun j => (hT j).2⟩

end GC.LongTime.Ch11
