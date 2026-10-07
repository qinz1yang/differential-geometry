import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4AModel
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ABallify
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionNodalF4ACross
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNodalFIX2
import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3C
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.SheetCoincidenceDiskR3B

/-!
# F4-a（`_F4A`）G2：解析 Morrey 盘 ⇒ pairwise collision nodal（R9 的 S8，`IsCollisionNodal_FIX2`，Ico 版）

`pairwise_nodal_of_analytic_morrey_F4A`：`F : ℂ → M` 在 `ball 0 1` 上光滑、conformal、harmonic、浸入、
像在开集 `P` 内，且对 analytic atlas `𝒜` 的每个 chart `e` 满足 F3C 结论形
`AnalyticOn ℝ (e ∘ F) (ball 0 1 ∩ F⁻¹' (e.source ∩ P))`（`morrey_disk_analytic_F3C`），并且没有开 sheet 包含
（R3b：`coincidentGermPairs = ∅` 的形式，`no_open_sheet_inclusion_of_coincidentGermPairs_eq_empty_R3B`）
⇒ 内部每对碰撞点 `z ≠ w`、`F z = F w` 都有 `IsCollisionNodal_FIX2 F z w`。

**消除 FIX2 G4 记录的两处差别**：同半径球版（`ballify_F4A`：每条弧取退出参数、线性重参数化，使
`{z' ∈ ball z ρ | ∃ w' ∈ ball w ρ, F z' = F w'}` 恰为弧的并），横截条款用 `Surjective coprod`
（`dw ≠ 0` ⇒ 横截，`fderiv_height_diff_eq_zero_F4A`；横截碰撞走隐函数）。

证明链：chart `e ∈ 𝒜` ⇒ `chart_transfer_F4A`（模型空间 `(g', e ∘ F)`）⇒ 横截 / 切向二分
（`collision_arcs_model_F4A`）⇒ `ballify_F4A` ⇒ 逐字对上 `IsCollisionNodal_FIX2`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Analytic

universe u

section Pred

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- `IsCollisionNodal_FIX2` 的加强：每条半弧在 `Icc 0 ρ` 上 `C^∞`（R14 / R11-RT 的 up-to-endpoint 输入，
D-R-MY4-15）。 -/
def IsCollisionNodalSm_F4A (F : ℂ → M) (z w : ℂ) : Prop :=
  ∃ (ρ : ℝ) (k : ℕ) (Γ : Fin (2 * k) → ℝ → ℂ) (v : Fin (2 * k) → ℂ), 0 < ρ ∧ 1 ≤ k ∧
    Disjoint (Metric.ball z ρ) (Metric.ball w ρ) ∧
    Metric.ball z ρ ⊆ Metric.ball 0 1 ∧ Metric.ball w ρ ⊆ Metric.ball 0 1 ∧
    InjOn F (Metric.ball z ρ) ∧ InjOn F (Metric.ball w ρ) ∧
    (∀ m, Γ m 0 = z ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ v m ≠ 0 ∧
      HasDerivWithinAt (Γ m) (v m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) (Metric.ball z ρ)) ∧
    (∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
      ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
    (∀ z' ∈ Metric.ball z ρ,
      (∃ w' ∈ Metric.ball w ρ, F z' = F w') ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z' = Γ m r) ∧
    (∀ m, ∀ r ∈ Ioo 0 ρ, ∀ w' ∈ Metric.ball w ρ, F (Γ m r) = F w' →
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F (Γ m r)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w')))) ∧
    ∀ m, ContDiffOn ℝ ∞ (Γ m) (Icc 0 ρ)

theorem IsCollisionNodalSm_F4A.toFIX2 {F : ℂ → M} {z w : ℂ}
    (h : IsCollisionNodalSm_F4A (E := E) F z w) :
    IsCollisionNodal_FIX2 (E := E) F z w := by
  obtain ⟨ρ, k, Γ, v, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := h
  exact ⟨ρ, k, Γ, v, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Pred

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **G2 / G3**：解析 Morrey 盘（F3C 结论形）的内部逐对碰撞都有 `IsCollisionNodal_FIX2`（Ico 版、同半径球），
并且每条半弧在 `Icc 0 ρ` 上 `C^∞`（`IsCollisionNodalSm_F4A`）。 -/
theorem pairwise_nodal_smooth_of_analytic_morrey_F4A (hd3 : Module.finrank ℝ E = 3)
    {P : Set M} (hPo : IsOpen P) {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {F : ℂ → M} (hsmI : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (ball (0 : ℂ) 1))
    (hconf : ∀ z ∈ ball (0 : ℂ) 1, DiskMapConformalAt G F z)
    (hharm : ∀ z ∈ ball (0 : ℂ) 1, diskMapTension G F z = 0)
    (hrank : ∀ z ∈ ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hP : ∀ z ∈ ball (0 : ℂ) 1, F z ∈ P)
    (hFa : ∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (F z))
      (ball (0 : ℂ) 1 ∩ F ⁻¹' (e.source ∩ P)))
    (hnc : ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → V₁.Nonempty → Disjoint V₁ V₂ →
      V₁ ⊆ ball (0 : ℂ) 1 → V₂ ⊆ ball (0 : ℂ) 1 → InjOn F V₁ → InjOn F V₂ →
      ¬ F '' V₁ ⊆ F '' V₂) :
    ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, z ≠ w → F z = F w →
      IsCollisionNodalSm_F4A (E := E) F z w := by
  intro z hz w hw hzw hFzw
  obtain ⟨e, he, hze⟩ := h𝒜.exists_mem_source (hP z hz)
  have hemax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := h𝒜.mem_maximalAtlas e he
  set s : Set ℂ := ball (0 : ℂ) 1 ∩ F ⁻¹' (e.source ∩ P) with hsdef
  have hso : IsOpen s :=
    hsmI.continuousOn.isOpen_inter_preimage isOpen_ball (e.open_source.inter hPo)
  have hzs : z ∈ s := ⟨hz, hze, hP z hz⟩
  have hws : w ∈ s := ⟨hw, by rw [← hFzw]; exact hze, hP w hw⟩
  have hFs : ∀ z' ∈ s, F z' ∈ e.source := fun z' hz' => hz'.2.1
  have hs_ball : s ⊆ ball (0 : ℂ) 1 := inter_subset_left
  obtain ⟨g', s', hs'o, hzs', hs'sub, hX', hconf', hharm', hback⟩ := chart_transfer_F4A G hemax hso
    hFs (hsmI.mono hs_ball) (fun z' hz' => hconf z' (hs_ball hz'))
    (fun z' hz' => hharm z' (hs_ball hz')) hzs
  have hws' : w ∈ s' := hback w hws (by rw [hFzw])
  have hs's : s' ⊆ s := hs'sub
  set X : ℂ → E := e ∘ F with hXdef
  have hXa : AnalyticOnNhd ℝ X s' :=
    (hso.analyticOn_iff_analyticOnNhd.mp (hFa e he)).mono hs'sub
  have hFc : ∀ z' ∈ s', ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z' := fun z' hz' =>
    hsmI.contMDiffAt (isOpen_ball.mem_nhds (hs_ball (hs'sub hz')))
  have hrankX : ∀ z' ∈ s', Function.Injective (fderiv ℝ X z') := by
    intro z' hz' v v' h
    apply hrank z' (hs_ball (hs'sub hz'))
    have h1 := mfderiv_symm_comp_F4A hemax (hFc z' hz') (hFs z' (hs'sub hz')) v
    have h2 := mfderiv_symm_comp_F4A hemax (hFc z' hz') (hFs z' (hs'sub hz')) v'
    rw [← h1, ← h2]
    exact congrArg _ h
  have hncX : ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → V₁.Nonempty → Disjoint V₁ V₂ → V₁ ⊆ s' →
      V₂ ⊆ s' → InjOn X V₁ → InjOn X V₂ → ¬ X '' V₁ ⊆ X '' V₂ := by
    intro V₁ V₂ hV₁ hV₂ hne hdisj hV₁s hV₂s hi₁ hi₂ hsub
    refine hnc V₁ V₂ hV₁ hV₂ hne hdisj (hV₁s.trans (hs'sub.trans hs_ball))
      (hV₂s.trans (hs'sub.trans hs_ball)) ?_ ?_ ?_
    · intro z₁ h₁ z₂ h₂ h
      exact hi₁ h₁ h₂ (congrArg e h)
    · intro z₁ h₁ z₂ h₂ h
      exact hi₂ h₁ h₂ (congrArg e h)
    · rintro _ ⟨z₁, h₁, rfl⟩
      obtain ⟨z₂, h₂, hz₂⟩ := hsub ⟨z₁, h₁, rfl⟩
      refine ⟨z₂, h₂, ?_⟩
      exact e.injOn (hFs z₂ (hs'sub (hV₂s h₂))) (hFs z₁ (hs'sub (hV₁s h₁))) hz₂
  have hvX : X z = X w := congrArg e hFzw
  -- 局部单射半径
  obtain ⟨rz, hrz, hinjz⟩ := exists_injOn_ball_of_injective_fderiv_F4A
    (((hX'.contMDiffAt (hs'o.mem_nhds hzs')).contDiffAt).of_le (by norm_num)) (hrankX z hzs')
  obtain ⟨rw, hrw, hinjw⟩ := exists_injOn_ball_of_injective_fderiv_F4A
    (((hX'.contMDiffAt (hs'o.mem_nhds hws')).contDiffAt).of_le (by norm_num)) (hrankX w hws')
  obtain ⟨εz, hεz, hεzsub⟩ := Metric.isOpen_iff.mp hs'o z hzs'
  obtain ⟨εw, hεw, hεwsub⟩ := Metric.isOpen_iff.mp hs'o w hws'
  have hdzw : 0 < dist z w / 2 := half_pos (dist_pos.mpr hzw)
  set r₁ : ℝ := min (min rz rw) (min (min εz εw) (dist z w / 2)) with hr₁def
  have hr₁pos : 0 < r₁ := lt_min (lt_min hrz hrw) (lt_min (lt_min hεz hεw) hdzw)
  obtain ⟨k, r₂, S, c, d, v, v', hk, hr₂pos, hr₂₁, hSpos, hc0, hd0, hcC, hcinj, hcv, hdC, hdv,
    hpair, hR, hcover, hT, hmem, hsmooth⟩ := collision_arcs_model_F4A hd3 g' hs'o hX' hXa hconf'
      hharm' hrankX hncX hzs' hws' hzw hvX hr₁pos
  have hr₁rz : r₁ ≤ rz := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁rw : r₁ ≤ rw := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁εz : r₁ ≤ εz := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hr₁εw : r₁ ≤ εw := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hr₁d : r₁ ≤ dist z w / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbz : ∀ ρ, ρ ≤ r₁ → ball z ρ ⊆ s' := fun ρ hρ =>
    (ball_subset_ball (hρ.trans hr₁εz)).trans hεzsub
  have hbw : ∀ ρ, ρ ≤ r₁ → ball w ρ ⊆ s' := fun ρ hρ =>
    (ball_subset_ball (hρ.trans hr₁εw)).trans hεwsub
  have hR' : ∀ m, ∀ t ∈ Ico 0 S, F (c m t) = F (d m t) := by
    intro m t ht
    have hm := hmem m t ⟨ht.1, ht.2.le⟩
    exact e.injOn (hFs _ (hs'sub hm.1)) (hFs _ (hs'sub hm.2)) (hR m t ht)
  have hcover' : ∀ z' ∈ ball z r₂, ∀ w' ∈ ball w r₂, F z' = F w' →
      ∃ m, ∃ t ∈ Ico 0 S, z' = c m t ∧ w' = d m t :=
    fun z' hz' w' hw' h => hcover z' hz' w' hw' (congrArg e h)
  have hT' : ∀ z' ∈ ball z r₂, ∀ w' ∈ ball w r₂, F z' = F w' → z' ≠ z →
      Function.Surjective ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z').coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w'))) := by
    intro z' hz' w' hw' h hne
    have hz'' : z' ∈ s' := hbz r₂ hr₂₁ hz'
    have hw'' : w' ∈ s' := hbw r₂ hr₂₁ hw'
    exact coprod_surjective_transfer_F4A hemax (hFc z' hz'') (hFc w' hw'') (hFs z' (hs'sub hz''))
      (hFs w' (hs'sub hw'')) h (hT z' hz' w' hw' (congrArg e h) hne)
  obtain ⟨ρ, hρ, hρr, Γ, u, harc, hpr, hiff, htr, hσ⟩ := ballify_F4A (R := fun z' w' => F z' = F w')
    (T := fun z' w' => Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z').coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F w'))))
    (z := z) (w := w) hr₂pos hk hSpos c d v v' hc0 hd0 hcC hcinj hcv hdC hdv hpair hR' hcover' hT'
  have hρ₁ : ρ ≤ r₁ := hρr.trans hr₂₁
  refine ⟨ρ, k, Γ, u, hρ, hk, ?_, ?_, ?_, ?_, ?_, harc, hpr, hiff, htr, ?_⟩
  · refine Metric.ball_disjoint_ball ?_
    have : ρ + ρ ≤ dist z w := by linarith [hρ₁.trans hr₁d]
    exact this
  · exact (hbz ρ hρ₁).trans (hs'sub.trans hs_ball)
  · exact (hbw ρ hρ₁).trans (hs'sub.trans hs_ball)
  · intro a ha b hb h
    exact hinjz (ball_subset_ball (hρ₁.trans hr₁rz) ha) (ball_subset_ball (hρ₁.trans hr₁rz) hb)
      (congrArg e h)
  · intro a ha b hb h
    exact hinjw (ball_subset_ball (hρ₁.trans hr₁rw) ha) (ball_subset_ball (hρ₁.trans hr₁rw) hb)
      (congrArg e h)
  · intro m
    obtain ⟨σ, hσpos, hσS, hΓ⟩ := hσ m
    have hmaps : MapsTo (fun r : ℝ => σ * r) (Icc 0 ρ) (Icc 0 S) := fun r hr =>
      ⟨mul_nonneg hσpos.le hr.1, (mul_le_mul_of_nonneg_left hr.2 hσpos.le).trans hσS⟩
    exact ((hsmooth m).comp (contDiff_const.mul contDiff_id).contDiffOn hmaps).congr
      (fun r _ => hΓ r)

/-- **G2**：`IsCollisionNodal_FIX2` 形（`C¹` 半弧，S8 冻结形）。 -/
theorem pairwise_nodal_of_analytic_morrey_F4A (hd3 : Module.finrank ℝ E = 3)
    {P : Set M} (hPo : IsOpen P) {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {F : ℂ → M} (hsmI : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F (ball (0 : ℂ) 1))
    (hconf : ∀ z ∈ ball (0 : ℂ) 1, DiskMapConformalAt G F z)
    (hharm : ∀ z ∈ ball (0 : ℂ) 1, diskMapTension G F z = 0)
    (hrank : ∀ z ∈ ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hP : ∀ z ∈ ball (0 : ℂ) 1, F z ∈ P)
    (hFa : ∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (F z))
      (ball (0 : ℂ) 1 ∩ F ⁻¹' (e.source ∩ P)))
    (hnc : ∀ V₁ V₂ : Set ℂ, IsOpen V₁ → IsOpen V₂ → V₁.Nonempty → Disjoint V₁ V₂ →
      V₁ ⊆ ball (0 : ℂ) 1 → V₂ ⊆ ball (0 : ℂ) 1 → InjOn F V₁ → InjOn F V₂ →
      ¬ F '' V₁ ⊆ F '' V₂) :
    ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, z ≠ w → F z = F w →
      IsCollisionNodal_FIX2 (E := E) F z w := fun z hz w hw hzw h =>
  (pairwise_nodal_smooth_of_analytic_morrey_F4A hd3 hPo h𝒜 hsmI hconf hharm hrank hP hFa hnc
    z hz w hw hzw h).toFIX2

open DifferentialGeometry.Analysis.Elliptic.HarmonicMap DifferentialGeometry.Topology in
/-- **G2 的 consumer**：`F = diskExtension u`（`u` 是 analytic 度量下的 Morrey 盘）+ F3C
（`morrey_disk_analytic_F3C`）+ R3b（`coincidentGermPairs = ∅`）+ rank ⇒ S8 的 `nodal` 字段形
`∀ z w ∈ D°, z ≠ w → F z = F w → IsCollisionNodal_FIX2 F z w`（加强为 `C^∞` 半弧）。 -/
theorem pairwise_nodal_smooth_of_morrey_disk_F4A [T2Space M] (hd3 : Module.finrank ℝ E = 3)
    {P : Set M} (hPo : IsOpen P) {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk G γ u) (hcgp : coincidentGermPairs (u : closedDisk → M) = ∅)
    (hrank : ∀ z ∈ ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hP : ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z ∈ P) :
    ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, z ≠ w → diskExtension u z = diskExtension u w →
      IsCollisionNodalSm_F4A (E := E) (diskExtension u) z w :=
  pairwise_nodal_smooth_of_analytic_morrey_F4A hd3 hPo h𝒜 hu.smoothInterior hu.conformal hu.harmonic
    hrank hP (fun e he => morrey_disk_analytic_F3C hPo h𝒜 hG hu e he)
    (fun V₁ V₂ h₁ h₂ hne hdisj hV₁ hV₂ hi₁ hi₂ hsub =>
      no_open_sheet_inclusion_of_coincidentGermPairs_eq_empty_R3B hcgp
        ⟨V₁, V₂, h₁, h₂, hne, hdisj, hV₁, hV₂, hi₁, hi₂, hsub⟩)

open DifferentialGeometry.Analysis.Elliptic.HarmonicMap DifferentialGeometry.Topology in
/-- **G2 的 consumer（FIX2 形）**：同上，只取 `IsCollisionNodal_FIX2`。 -/
theorem pairwise_nodal_of_morrey_disk_F4A [T2Space M] (hd3 : Module.finrank ℝ E = 3)
    {P : Set M} (hPo : IsOpen P) {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜) {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : IsAnalyticMetricOn_F3A 𝒜 P G) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk G γ u) (hcgp : coincidentGermPairs (u : closedDisk → M) = ∅)
    (hrank : ∀ z ∈ ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hP : ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z ∈ P) :
    ∀ z ∈ ball (0 : ℂ) 1, ∀ w ∈ ball (0 : ℂ) 1, z ≠ w → diskExtension u z = diskExtension u w →
      IsCollisionNodal_FIX2 (E := E) (diskExtension u) z w := fun z hz w hw hzw h =>
  (pairwise_nodal_smooth_of_morrey_disk_F4A hd3 hPo h𝒜 hG hu hcgp hrank hP z hz w hw hzw h).toFIX2

end DifferentialGeometry.Geometry
