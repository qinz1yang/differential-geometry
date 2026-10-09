import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNotionFIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexCons2FIX2
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexSubdivFIX2
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell

/-!
# S-MY-FIX2 G3：revolve 模型的 **planar interface**（`IsPlanarInterface_FIX2`，S1–S4、S6–S8）

`IsPlanarInterface_FIX2 f F T α` 是 `IsPreparedSheetComplex_FIX2` 去掉 S5（thickening `A`、`φ`、`h`）
与两个 rev3 字段（`local_product`、`ambient_collar`）后剩下的 14 个字段
（`IsPreparedSheetComplex_FIX2.toPlanarInterface` 证它确实是 notion 的前缀）。
对 revolve 模型 `curve2_FIX2`，取 `T` = G3 的分层剖分 `R`（level 三角形 `g = 1/2`、`g = 3/4`
是子复形）、`α = radialGrid_FIX`，14 个字段全证（`curve2_planar_interface_FIX2`），
S6 的 `α(子复形)` 形是真的：`α '' |S| = {半径 1/2 与 3/4 的两个圆}`，非空。
consumer：R12 总装的 `|vertexCollisionPairs T (f ∘ α)| ≥ 1`（card ≥ 1 情形的陈述对齐），
因为 `(1/2) • V₁` 与 `(3/4) • V₁` 是 `R` 的顶点且 `F ∘ α` 把它们粘在一起。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- `IsPreparedSheetComplex_FIX2` 的前缀：S1–S4 与 S6–S8（不含 thickening 与 rev3 字段）。 -/
structure IsPlanarInterface_FIX2 (f : C(closedDisk, M)) (F : ℂ → M)
    (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (α : ℂ → ℂ) : Prop where
  faces_finite : T.faces.Finite
  dim_le : ∀ s ∈ T.faces, s.card ≤ 3
  alpha_bij : BijOn α T.space (Metric.closedBall 0 1)
  alpha_cont : ContinuousOn α T.space
  alpha_bdry : ∀ {z : ℂ}, z ∈ T.space → (‖α z‖ = 1 ↔ z ∈ frontier T.space)
  alpha_lip : ∃ L : ℝ≥0, LipschitzOnWith L α T.space
  alpha_smooth : ∀ s ∈ T.faces, s.card = 3 →
    ContDiffOn ℝ ∞ α (convexHull ℝ (s : Set ℂ) \ (s : Set ℂ))
  alpha_rank : ∀ s ∈ T.faces, s.card = 3 → ∀ z ∈ convexHull ℝ (s : Set ℂ) \ (s : Set ℂ),
    Function.Injective (fderivWithin ℝ α (convexHull ℝ (s : Set ℂ)) z)
  ext : SmoothDiskExtension (E := E) f F
  rank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z)
  collar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w
  collision_subcomplex : ∃ S ⊆ T.faces, α '' (⋃ s ∈ S, convexHull ℝ (s : Set ℂ)) =
    {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧ ∃ w ∈ Metric.closedBall (0 : ℂ) 1, w ≠ z ∧ F w = F z}
  tangency_vertices : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w))) →
    ∃ v ∈ T.vertices, α v = z
  nodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
    IsCollisionNodal_FIX2 (E := E) F z w

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- notion 的前缀：任意 prepared 数据给出 planar interface。 -/
theorem IsPreparedSheetComplex_FIX2.toPlanarInterface {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h) :
    IsPlanarInterface_FIX2 (E := E) f F T α where
  faces_finite := hprep.faces_finite
  dim_le := hprep.dim_le
  alpha_bij := hprep.alpha_bij
  alpha_cont := hprep.alpha_cont
  alpha_bdry := fun hz => hprep.alpha_bdry hz
  alpha_lip := hprep.alpha_lip
  alpha_smooth := hprep.alpha_smooth
  alpha_rank := hprep.alpha_rank
  ext := hprep.ext
  rank := hprep.rank
  collar := hprep.collar
  collision_subcomplex := hprep.collision_subcomplex
  tangency_vertices := hprep.tangency_vertices
  nodal := hprep.nodal

end Generic

/-- `α '' (g = 1/2 或 3/4) = 闭盘内半径 1/2 或 3/4 的圆`。 -/
theorem radialGrid_image_levelSet_FIX2 :
    radialGrid_FIX '' levelSet_FIX2 =
      {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ (‖z‖ = 1 / 2 ∨ ‖z‖ = 3 / 4)} := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hn := norm_radialGrid_FIX z
    rcases hz with h | h
    · refine ⟨?_, Or.inl (hn.trans h)⟩
      rw [mem_closedBall, dist_zero_right, hn, h]; norm_num
    · refine ⟨?_, Or.inr (hn.trans h)⟩
      rw [mem_closedBall, dist_zero_right, hn, h]; norm_num
  · rintro w ⟨hw, hn⟩
    obtain ⟨z, hz, hzw⟩ := radialGrid_surjOn_FIX hw
    have hg : triGauge_FIX z = ‖w‖ := by rw [← hzw, norm_radialGrid_FIX]
    exact ⟨z, by rcases hn with h | h
                 · exact Or.inl (hg.trans h)
                 · exact Or.inr (hg.trans h), hzw⟩

/-- `radialGrid` 对非负标量齐次。 -/
theorem radialGrid_smul_FIX2 {c : ℝ} (hc : 0 < c) (z : ℂ) :
    radialGrid_FIX (c • z) = c • radialGrid_FIX z := by
  by_cases hz : z = 0
  · subst hz; simp [radialGrid_zero_FIX]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  unfold radialGrid_FIX
  rw [triGauge_smul_FIX hc.le, norm_smul, Real.norm_of_nonneg hc.le, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **G3 主定理**：revolve 模型的 planar interface——存在 `T`（分层剖分）使 `IsPlanarInterface_FIX2` 成立，
且 `|vertexCollisionPairs T (f ∘ α)| ≥ 1`（R12 总装 card ≥ 1 情形的陈述对齐）。 -/
theorem curve2_planar_interface_FIX2 :
    ∃ (T : _root_.Geometry.SimplicialComplex ℝ ℂ) (_ : Finite T.faces),
      IsPlanarInterface_FIX2 (E := EcR_FIX2) curve2Disk_FIX2 curve2_FIX2 T radialGrid_FIX ∧
      0 < (vertexCollisionPairs T (diskExtension curve2Disk_FIX2 ∘ radialGrid_FIX)).card := by
  classical
  obtain ⟨R, hfin, hsp, hRs, hlev, hvert⟩ := exists_subdiv_FIX2
  have : Finite R.faces := hfin.to_subtype
  refine ⟨R, this, ⟨hfin, subdiv_dim_le_FIX2 R, ?_, ?_, ?_, ?_, subdiv_smooth_FIX2 hRs,
    subdiv_rank_FIX2 hRs, curve2_ext_consumer_FIX2, curve2_rank_consumer_FIX2,
    curve2_collar_consumer_FIX2, ?_, curve2_tangency_consumer_FIX2 R radialGrid_FIX,
    curve2_nodal_consumer_FIX2⟩, ?_⟩
  · rw [hsp]; exact radialGrid_bijOn_FIX
  · rw [hsp]; exact radialGrid_continuous_FIX.continuousOn
  · intro z hz
    rw [hsp] at hz ⊢
    exact radialGrid_bdry_FIX hz
  · rw [hsp]; exact radialGrid_lip_FIX
  · refine ⟨{s | s ∈ R.faces ∧ convexHull ℝ (s : Set ℂ) ⊆ levelSet_FIX2},
      fun s hs => hs.1, ?_⟩
    rw [hlev, radialGrid_image_levelSet_FIX2, ← curve2_collision_set_FIX2]
  · -- 顶点碰撞对：`(1/2) • V₁`、`(3/4) • V₁`
    have hV1 : triV1_FIX ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num [triV1_FIX] at this
    have hgV : triGauge_FIX triV1_FIX = 1 := triGauge_V1_FIX
    have hα1 : ‖radialGrid_FIX triV1_FIX‖ = 1 := by rw [norm_radialGrid_FIX, hgV]
    set u : ℂ := (1 / 2 : ℝ) • triV1_FIX with hu
    set u' : ℂ := (3 / 4 : ℝ) • triV1_FIX with hu'
    have hαu : radialGrid_FIX u = (1 / 2 : ℝ) • radialGrid_FIX triV1_FIX :=
      radialGrid_smul_FIX2 (by norm_num) _
    have hαu' : radialGrid_FIX u' = (3 / 4 : ℝ) • radialGrid_FIX triV1_FIX :=
      radialGrid_smul_FIX2 (by norm_num) _
    have hn1 : ‖radialGrid_FIX u‖ = 1 / 2 := by
      rw [hαu, norm_smul, hα1, Real.norm_of_nonneg (by norm_num)]; norm_num
    have hrel : radialGrid_FIX u' = (3 / 2 : ℝ) • radialGrid_FIX u := by
      rw [hαu, hαu', smul_smul]; norm_num
    have hpair : curve2_FIX2 (radialGrid_FIX u) = curve2_FIX2 (radialGrid_FIX u') := by
      rw [hrel]; exact curve2_pair_FIX2 hn1
    have hb1 : ‖radialGrid_FIX u‖ ≤ 1 := by rw [hn1]; norm_num
    have hb2 : ‖radialGrid_FIX u'‖ ≤ 1 := by
      rw [hrel, norm_smul, hn1, Real.norm_of_nonneg (by norm_num)]; norm_num
    have hne : u ≠ u' := by
      intro h
      have h2 : ‖radialGrid_FIX u‖ = ‖radialGrid_FIX u'‖ := by rw [h]
      rw [hn1, hrel, norm_smul, hn1, Real.norm_of_nonneg (by norm_num)] at h2
      norm_num at h2
    have hmem : ({u, u'} : Finset ℂ) ∈ vertexCollisionPairs R
        (diskExtension curve2Disk_FIX2 ∘ radialGrid_FIX) := by
      rw [mem_vertexCollisionPairs]
      refine ⟨?_, Finset.card_pair hne, ?_⟩
      · intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hvert false
        · exact hvert true
      · intro hinj
        have hum : u ∈ (↑({u, u'} : Finset ℂ) : Set ℂ) := by simp
        have hum' : u' ∈ (↑({u, u'} : Finset ℂ) : Set ℂ) := by simp
        have hdu : diskExtension curve2Disk_FIX2 (radialGrid_FIX u) =
            curve2_FIX2 (radialGrid_FIX u) :=
          diskExtension_coe curve2Disk_FIX2 ⟨_, mem_closedBall_zero_iff.mpr hb1⟩
        have hdu' : diskExtension curve2Disk_FIX2 (radialGrid_FIX u') =
            curve2_FIX2 (radialGrid_FIX u') :=
          diskExtension_coe curve2Disk_FIX2 ⟨_, mem_closedBall_zero_iff.mpr hb2⟩
        have hf : (diskExtension curve2Disk_FIX2 ∘ radialGrid_FIX) u =
            (diskExtension curve2Disk_FIX2 ∘ radialGrid_FIX) u' := by
          simp only [Function.comp_apply]
          rw [hdu, hdu']
          exact hpair
        exact hne (hinj hum hum' hf)
    exact Finset.card_pos.mpr ⟨_, hmem⟩

end DifferentialGeometry.Geometry
