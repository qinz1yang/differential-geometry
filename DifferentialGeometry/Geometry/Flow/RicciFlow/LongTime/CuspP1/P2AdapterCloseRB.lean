import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterOpenRB
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskWeakJordanRB

/-!
# S-A11-ROUTEB G1，零件 RB-C：ambient 闭合引理

把 `exists_eventual_confined_morrey_disk_HC` 的一个盘 `q : C(closedDisk, U)` 与冻结 `hMY`
（`design-A08-reduction-20261006.md` §3）的结论
`Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧
∀ z ∈ closedBall 0 1, Injective (mfderiv Q z)` 合成 `isExteriorSpanningDisk`：

* `Function.Injective q` + 紧 + T2 ⇒ `IsEmbedding q`（`Continuous.isClosedEmbedding`），再沿开嵌入 `ι`（RB-2）；
* `range γ ⊆ frontier {ρ ≤ 0}`：边界 `ρ = 0`、`dρ ≠ 0`（RB-F）与 σ 满射；
* 精确迹：`exists_isExteriorSpanningDisk_of_weakJordan_RB`（RB-1，基于 S-A08-ATTAIN 的零件）。

只依赖已跟踪文件与 S-A08-ATTAIN G1（`ExteriorDiskAttainAT`），无 sorry 家族，可登记。
-/

set_option autoImplicit false
noncomputable section

open Filter Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

/-- **RB-C.**  ρ-sublevel 域 `W = {ρ ≤ 0}`、`U ⊆ X` 开、`q : C(closedDisk, U)` 满足 `_HC` 的 range /
interior / boundary 条款，`γ` 为光滑嵌入环且 `ι ∘ q` 有弱 Jordan trace `γ`，再加 `hMY` 的结论，则存在
以 `γ` 为精确迹的 exterior spanning disk。 -/
theorem exists_exteriorSpanningDisk_of_confined_RB {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {ρ : X → ℝ} (hρc : Continuous ρ) {a : ℝ} (ha : 0 < a)
    (hdρ : ∀ x, 0 ≤ ρ x → ρ x < a → mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0)
    {γ : freeLoop X} (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (U : Opens X) {q : C(closedDisk, U)}
    (hwj : DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q))
    (hrange : Set.range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆
      {x | ρ x ≤ 0})
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z ∈ interior {x | ρ x ≤ 0})
    (hzero : ∀ θ : loopCircle, ρ (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)
      (diskBoundary θ)) = 0)
    (hMY : Function.Injective q ∧
      ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
        ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) :
    ∃ u : C(closedDisk, X), isExteriorSpanningDisk {x | ρ x ≤ 0} γ u := by
  obtain ⟨hq, Q, hQ, hinj⟩ := hMY
  have hemb : Topology.IsEmbedding q := (q.continuous.isClosedEmbedding hq).isEmbedding
  have hfront : Set.range γ ⊆ frontier {x | ρ x ≤ 0} :=
    range_subset_of_weakJordan_boundary_RB hwj fun θ =>
      frontier_of_profile_RB (hzero θ) (hdρ _ (hzero θ).ge (hzero θ ▸ ha)) hρc
  exact exists_isExteriorSpanningDisk_of_weakJordan_RB hγ hwj hrange hint hfront
    ⟨fun z => (Q z : X), smoothDiskExtension_val_comp_RB U hQ, isEmbedding_val_comp_RB U hemb,
      fun z hz => injective_mfderiv_val_comp_RB U (hinj z hz)⟩

end GC.LongTime.CuspP1
