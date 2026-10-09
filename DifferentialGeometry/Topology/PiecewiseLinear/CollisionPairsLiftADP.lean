import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk

/-!
# S-MY-ADAPT G6（rev2 A-5(a)）：`P_T(·, α)` 沿 lift 单调

`vertexCollisionPairs T φ`（`LoopTheorem/SingularCell.lean`）= 固定 source complex `T` 的顶点
pair 里被 `φ` 粘在一起的那些。R11 的 tower 终止量是
`P_T(f, α) = vertexCollisionPairs T (diskExtension f ∘ α)`（rev2 D-3′，固定 `T`、`α`，**每层不重新细分**）。

* `vertexCollisionPairs_lift_subset_of_comp_ADP`：一般形。`pr ∘ φ' = φ` ⇒
  `vertexCollisionPairs T φ' ⊆ vertexCollisionPairs T φ`（单调性只用 lift 等式）。
* `vertexCollisionPairs_lift_subset_ADP`：scratch `Lanes.lean:24`
  `vertexCollisionPairs_lift_subset_MYD3` 的逐字形（`f : C(closedDisk, M)`、`f'` 是 `pr` 下的 lift）。
* `vertexCollisionPairs_lift_card_le_ADP`：consumer（tower 的 `Finset.card` 不增）。

只用 `vertexCollisionPairs` 的定义与 `mem_vertexCollisionPairs`；不加 `Finite` 之外的前提；
不碰 `T` 的细分。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.Geometry DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **一般形**：`pr ∘ φ' = φ` ⇒ `P_T(φ') ⊆ P_T(φ)`（`φ'` 上不单射的顶点 pair 在 `φ` 上更不单射）。 -/
theorem vertexCollisionPairs_lift_subset_of_comp_ADP {M M' : Type*}
    (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces] {φ : E → M} {φ' : E → M'}
    (pr : M' → M) (hcomp : pr ∘ φ' = φ) :
    vertexCollisionPairs T φ' ⊆ vertexCollisionPairs T φ := by
  intro s hs
  rw [mem_vertexCollisionPairs] at hs ⊢
  refine ⟨hs.1, hs.2.1, fun hinj => hs.2.2 ?_⟩
  rw [← hcomp] at hinj
  exact hinj.of_comp

/-- **G6**（rev2 A-5(a)，scratch `vertexCollisionPairs_lift_subset_MYD3` 逐字形）：固定 `T`、`α`，
`pr ∘ f' = f` ⇒ `P_T(f', α) ⊆ P_T(f, α)`。 -/
theorem vertexCollisionPairs_lift_subset_ADP {M M' : Type*} [TopologicalSpace M]
    [TopologicalSpace M'] (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊆
      vertexCollisionPairs T (diskExtension f ∘ α) := by
  refine vertexCollisionPairs_lift_subset_of_comp_ADP T pr ?_
  funext z
  simp only [Function.comp_apply, diskExtension, hlift]

/-- consumer：tower 的终止量 `|P_T(f, α)|` 沿 lift 不增（R11 的归纳测度；严格降另见 R11-PL(b)）。 -/
theorem vertexCollisionPairs_lift_card_le_ADP {M M' : Type*} [TopologicalSpace M]
    [TopologicalSpace M'] (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) :
    (vertexCollisionPairs T (diskExtension f' ∘ α)).card ≤
      (vertexCollisionPairs T (diskExtension f ∘ α)).card :=
  Finset.card_le_card (vertexCollisionPairs_lift_subset_ADP T α pr hlift)

end DifferentialGeometry.Topology.PiecewiseLinear
