import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNotionFIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexCurve2FIX2

/-!
# S-MY-FIX2 G2a consumers（`_FIX2`）：revolve 模型对 notion 字段的原样陈述

`curve2_FIX2` 的 F 侧 collision interface 以 `IsPreparedSheetComplex_FIX2` 的字段形状给出（对任意 `(T, α)`
成立的部分）：S4 `ext` / `rank` / `collar`、S7 `tangency_vertices`、S8 `nodal`（Ico 版 `k = 1`）、S6 的
集合侧。**没有**：`T`、`α`（S1–S3、S6 的 `α(子复形)` 形）、thickening（S5）、`local_product`、`ambient_collar`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Bundle Manifold
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

/-- revolve 模型限制到闭盘上的连续映射 `f`。 -/
def curve2Disk_FIX2 : C(closedDisk, EcR_FIX2) :=
  ⟨fun z => curve2_FIX2 z, curve2_contDiff_FIX2.continuous.comp continuous_subtype_val⟩

/-- S4 `ext`：`F` 是 `f` 的光滑延拓（整个 ℂ 上 `C^∞`）。 -/
theorem curve2_ext_consumer_FIX2 :
    SmoothDiskExtension (E := EcR_FIX2) curve2Disk_FIX2 curve2_FIX2 :=
  ⟨fun _ => rfl, univ, isOpen_univ, subset_univ _, curve2_contDiff_FIX2.contMDiff.contMDiffOn⟩

/-- S4 `rank`：闭盘上 immersion（字段原样陈述）。 -/
theorem curve2_rank_consumer_FIX2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z) :=
  fun _ hz => curve2_rank_FIX2 hz

/-- S4 `collar`（`μ = 7/8`：半径 `> 7/8` 处无碰撞）。 -/
theorem curve2_collar_consumer_FIX2 :
    ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → curve2Disk_FIX2 z = curve2Disk_FIX2 w →
      z = w := by
  refine ⟨7 / 8, by norm_num, fun z w hz hF => Subtype.ext ?_⟩
  exact curve2_collar_FIX2 (mem_closedBall_zero_iff.mp z.2) (mem_closedBall_zero_iff.mp w.2) hz hF

/-- **S7 consumer**：对**任意** `(T, α)`，字段 `tangency_vertices` 的陈述成立（所有碰撞 transverse，
tangency 顶点集 = ∅）。 -/
theorem curve2_tangency_consumer_FIX2 (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      curve2_FIX2 z = curve2_FIX2 w →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z).coprod
          (-(show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 w))) →
      ∃ v ∈ T.vertices, α v = z :=
  fun _ hz _ hw hzw hF hns => absurd (curve2_all_transverse_FIX2 hz hw hzw hF) hns

/-- **S8 consumer**：字段 `nodal` 的陈述（Ico 版，`k = 1`）。 -/
theorem curve2_nodal_consumer_FIX2 :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      curve2_FIX2 z = curve2_FIX2 w → IsCollisionNodal_FIX2 (E := EcR_FIX2) curve2_FIX2 z w :=
  fun _ hz _ hw hzw hF => curve2_nodal_FIX2 hz hw hzw hF

/-- **S6 集合侧 consumer**：闭盘内的碰撞集非空，恰是两个同心圆（半径 `1/2`、`3/4`）。 -/
theorem curve2_collision_nonempty_FIX2 :
    ∃ z ∈ closedBall (0 : ℂ) 1, ∃ w ∈ closedBall (0 : ℂ) 1, w ≠ z ∧
      curve2_FIX2 w = curve2_FIX2 z ∧ ‖z‖ = 1 / 2 := by
  have hz : (1 / 2 : ℂ) ∈ {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ (‖z‖ = 1 / 2 ∨ ‖z‖ = 3 / 4)} := by
    refine ⟨?_, Or.inl ?_⟩
    · rw [mem_closedBall_zero_iff]
      simp
      norm_num
    · simp
  rw [← curve2_collision_set_FIX2] at hz
  obtain ⟨hz1, w, hw, hwz, hF⟩ := hz
  exact ⟨_, hz1, w, hw, hwz, hF, by simp⟩

end DifferentialGeometry.Geometry
