import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexTriangleFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexBipyramidFIX
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell

/-!
# S-MY-FIX G3：平坦标准盘的 prepared witness `flatDisk_prepared_FIX`（R9 model fixture，非空性证据）

`E = M = ℝ³`，平坦标准盘 `f z = (Re z, Im z, 0)`（`flatDisk_FIX`），`F = flat`。`IsPreparedSheetComplex_FIX`
的 22 个字段对下列**显式**数据全部证明（无未证目标，standard axioms only）：

* `T = triComplex_FIX`（三角形 `Δ` 的 cone 剖分），`α = radialGrid_FIX`（径向 gauge 映射），
* `A = bipyramid_FIX`（`K_flat` 的 suspension），`φ = flatAffine_FIX`，`h = bipyramidRealization_FIX`。

**碰撞集为空**：`F = flat` 单射，所以 (S6) `collision_subcomplex`（`S = ∅`）、(S7) `tangency_vertices`、
(S8) `nodal` 三个字段是**空真**的；这个 fixture 只验证 (S1)–(S5) 非空。带横截碰撞的非空性
（例如两个横截平盘拼成的 immersed 盘 = fixture-2）等 R-MY3 裁决，**这里不做**。

consumers（statement 级对齐；R10 / R11 / R12 的合同仍只在 scratch、不在树里）：
* `flatDisk_nbhd_data_FIX`：R10.1 `IsRelRegularNbhd` 的 `Nb = h(|A|)` 部分对 witness 实例化；
* `flatDisk_complexity_zero_FIX`：R11 / R12 总装里的 complexity
  `|vertexCollisionPairs T (diskExtension f ∘ α)| = 0`（总装归纳的起点 `n = 0`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Bundle Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal Manifold

namespace DifferentialGeometry.Geometry

theorem norm_diskBoundary_FIX (θ : loopCircle) : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 :=
  Circle.norm_coe (AddCircle.toCircle θ)
/-- **R9 model fixture**：平坦标准盘的 prepared witness。 -/
theorem flatDisk_prepared_FIX :
    IsPreparedSheetComplex_FIX (E := E3_FIX) flatDisk_FIX (⇑flatCLM_FIX) triComplex_FIX
      radialGrid_FIX 3 bipyramid_FIX (⇑flatAffine_FIX) bipyramidRealization_FIX where
  faces_finite := triComplex_faces_finite_FIX
  dim_le := triComplex_dim_le_FIX
  alpha_bij := radialGrid_bijOn_FIX
  alpha_cont := radialGrid_continuous_FIX.continuousOn
  alpha_bdry := radialGrid_bdry_FIX
  alpha_lip := radialGrid_lip_FIX
  alpha_smooth := radialGrid_smooth_FIX
  alpha_rank := radialGrid_rank_FIX
  ext := ⟨fun _ => rfl, univ, isOpen_univ, subset_univ _,
    flatCLM_FIX.contDiff.contMDiff.contMDiffOn⟩
  rank := fun z _ => by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    exact flatCLM_injective_FIX
  collar := ⟨0, by norm_num, fun z w _ hzw => Subtype.ext (flatCLM_injective_FIX hzw)⟩
  A_finite := bipyramid_faces_finite_FIX
  A_manifold := bipyramid_manifold_FIX
  h_cont := continuous_realization_FIX.continuousOn
  h_inj := realization_injOn_FIX
  face_map := fun s hs => ⟨
    Or.inl ((mem_coneComplex_faces_iff _).mpr (Or.inl ((mem_simplicialImage_faces_iff _ _ _ _).mpr
      ⟨s, hs, rfl⟩))),
    Finset.card_image_of_injective _ flatCLM_injective_FIX⟩
  factor := by
    intro z hz
    rw [simplicialMap_eqOn_affine _ _ hz]
    change bipyramidRealization_FIX (flatCLM_FIX z) = _
    rw [bipyramidRealization_FIX, proj12_flat_FIX, pz_flat_FIX, zero_smul, add_zero]
  bdry_frontier := fun θ => by
    rw [realization_image_FIX]
    exact flat_mem_frontier_FIX (norm_diskBoundary_FIX θ)
  int_interior := fun z hz => by
    rw [realization_image_FIX]
    exact flat_mem_interior_FIX hz
  collision_subcomplex := ⟨∅, empty_subset _, by
    ext z
    simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, image_empty,
      false_iff, not_and, not_exists, mem_ofPred_eq]
    exact fun _ w _ hwz hF => hwz (flatCLM_injective_FIX hF)⟩
  tangency_vertices := fun _ _ _ _ hzw hF => absurd (flatCLM_injective_FIX hF) hzw
  nodal := fun _ _ _ _ hzw hF => absurd (flatCLM_injective_FIX hF) hzw


/-- `triComplex_FIX` 是有限复形（给 `vertexCollisionPairs` 的 `[Finite K.faces]` 用）。 -/
instance finite_triComplex_faces_FIX : Finite triComplex_FIX.faces :=
  triComplex_faces_finite_FIX.to_subtype

/-- **consumer（R10.1 对齐）**：`flatDisk_prepared_FIX` 的 thickening 数据 = R10.1 `IsRelRegularNbhd`
的 `Nb = h(|A|)` 部分。 -/
theorem flatDisk_nbhd_data_FIX :
    (∃ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → E3_FIX), Ab.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 Ab ∧ ContinuousOn hb Ab.space ∧ InjOn hb Ab.space ∧
      hb '' Ab.space = bipyramidRealization_FIX '' bipyramid_FIX.space) ∧
    (∀ θ, flatDisk_FIX (diskBoundary θ) ∈
      frontier (bipyramidRealization_FIX '' bipyramid_FIX.space)) ∧
    (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      flatDisk_FIX z ∈ interior (bipyramidRealization_FIX '' bipyramid_FIX.space)) :=
  flatDisk_prepared_FIX.nbhd_data

/-- **consumer（R11 / R12 对齐）**：fixture 的 complexity `P_T(f, α)` 为空（`f ∘ α` 在 `T` 的顶点上单射），
所以总装的归纳从 `n = 0` 起步。 -/
theorem flatDisk_complexity_zero_FIX :
    (vertexCollisionPairs triComplex_FIX
      (diskExtension flatDisk_FIX ∘ radialGrid_FIX)).card = 0 := by
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun s hs => ?_)
  obtain ⟨hsub, -, hninj⟩ := (mem_vertexCollisionPairs _ _ s).mp hs
  refine hninj fun x hx y hy hxy => ?_
  have hxT : x ∈ {z : ℂ | triGauge_FIX z ≤ 1} :=
    triComplex_space_FIX ▸ triComplex_FIX.vertices_subset_space (hsub hx)
  have hyT : y ∈ {z : ℂ | triGauge_FIX z ≤ 1} :=
    triComplex_space_FIX ▸ triComplex_FIX.vertices_subset_space (hsub hy)
  have hx1 : ‖radialGrid_FIX x‖ ≤ 1 := by
    rw [norm_radialGrid_FIX]
    exact hxT
  have hy1 : ‖radialGrid_FIX y‖ ≤ 1 := by
    rw [norm_radialGrid_FIX]
    exact hyT
  have h := hxy
  simp only [Function.comp_apply] at h
  rw [diskExtension_flat_FIX hx1, diskExtension_flat_FIX hy1] at h
  exact radialGrid_injective_FIX (flatCLM_injective_FIX h)

end DifferentialGeometry.Geometry
