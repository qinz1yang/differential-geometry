import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNotionFIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexLocal2FIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFlatFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FlatLensCollapseR10

/-!
# S-MY-FIX2：consumers（`_FIX2`）

* `flatDisk_prepared_FIX2`：新 notion `IsPreparedSheetComplex_FIX2`（Ico 版 S8 + `local_product` +
  `ambient_collar`，共 24 字段）的 inhabitant——平坦标准盘（S6–S8 空真；两个 rev3 字段取自 O-MY-R10PL 的
  `flatDisk_localProduct_R10` / `flatDisk_ambientCollar_R10`）。
* G1 consumers：局部 fixture `line2_FIX2` 的 S7 / S8 以 **notion 字段的原样陈述** 对任意 `(T, α)` 成立
  （tangency 顶点集 = ∅，所以字段 `tangency_vertices` 从“所有碰撞 transverse”空真得出；`nodal` 字段 = Ico 版 k = 1）。
-/

set_option autoImplicit false
noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

/-- **notion inhabitant**：平坦标准盘满足 24 字段的 `IsPreparedSheetComplex_FIX2`。 -/
theorem flatDisk_prepared_FIX2 :
    IsPreparedSheetComplex_FIX2 (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX 3 bipyramid_FIX (⇑flatAffine_FIX) bipyramidRealization_FIX where
  faces_finite := flatDisk_prepared_FIX.faces_finite
  dim_le := flatDisk_prepared_FIX.dim_le
  alpha_bij := flatDisk_prepared_FIX.alpha_bij
  alpha_cont := flatDisk_prepared_FIX.alpha_cont
  alpha_bdry := fun hz => flatDisk_prepared_FIX.alpha_bdry hz
  alpha_lip := flatDisk_prepared_FIX.alpha_lip
  alpha_smooth := flatDisk_prepared_FIX.alpha_smooth
  alpha_rank := flatDisk_prepared_FIX.alpha_rank
  ext := flatDisk_prepared_FIX.ext
  rank := flatDisk_prepared_FIX.rank
  collar := flatDisk_prepared_FIX.collar
  A_finite := flatDisk_prepared_FIX.A_finite
  A_manifold := flatDisk_prepared_FIX.A_manifold
  h_cont := flatDisk_prepared_FIX.h_cont
  h_inj := flatDisk_prepared_FIX.h_inj
  face_map := flatDisk_prepared_FIX.face_map
  factor := flatDisk_prepared_FIX.factor
  bdry_frontier := flatDisk_prepared_FIX.bdry_frontier
  int_interior := flatDisk_prepared_FIX.int_interior
  collision_subcomplex := flatDisk_prepared_FIX.collision_subcomplex
  tangency_vertices := flatDisk_prepared_FIX.tangency_vertices
  nodal := fun _ _ _ _ hzw hF => absurd (flatCLM_injective_FIX hF) hzw
  local_product := flatDisk_localProduct_R10
  ambient_collar := flatDisk_ambientCollar_R10

/-- **G1 consumer（S7）**：局部 fixture 的所有碰撞都 transverse，所以对**任意** `(T, α)`，
notion 字段 `tangency_vertices` 的陈述成立（前提 `¬ Surjective` 不可能，tangency 顶点集 = ∅）。 -/
theorem line2_tangency_consumer_FIX2 (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      line2_FIX2 z = line2_FIX2 w →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z).coprod
          (-(show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 w))) →
      ∃ v ∈ T.vertices, α v = z :=
  fun _ _ _ _ hzw hF hns => absurd (line2_all_transverse_FIX2 hzw hF) hns

/-- **G1 consumer（S8）**：notion 字段 `nodal` 的陈述（Ico 版，`k = 1`）对局部 fixture 成立。 -/
theorem line2_nodal_consumer_FIX2 :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w →
      line2_FIX2 z = line2_FIX2 w → IsCollisionNodal_FIX2 (E := E3P_FIX2) line2_FIX2 z w :=
  fun _ hz _ _ hzw hF => line2_nodal_FIX2 hz hzw hF

/-- **G1 consumer（S4 / S6 集合侧）**：fixture 在闭盘上是 immersion，碰撞集非空（两条弦）。 -/
theorem line2_collision_nonempty_FIX2 :
    ∃ z ∈ closedBall (0 : ℂ) 1, ∃ w ∈ closedBall (0 : ℂ) 1, w ≠ z ∧
      line2_FIX2 w = line2_FIX2 z ∧ Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z) := by
  have hz : (⟨0, 1 / 2⟩ : ℂ) ∈ {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧
      (z.im = 1 / 2 ∨ z.im = -(1 / 2))} := by
    refine ⟨?_, Or.inl rfl⟩
    rw [mem_closedBall_zero_iff, Complex.norm_def, Complex.normSq_apply]
    simp only
    rw [Real.sqrt_le_one]
    norm_num
  rw [← line2_collision_set_FIX2] at hz
  obtain ⟨hz1, w, hw, hwz, hF⟩ := hz
  exact ⟨_, hz1, w, hw, hwz, hF, line2_rank_FIX2 _⟩

end DifferentialGeometry.Geometry
