import DifferentialGeometry.Geometry.MinimalSurface.Plateau.F4.OutputF4D

/-!
# O-MY-F4D G1：平面路线 (i)——collar + 紧性 ⇒ 碰撞集紧且被有限个 nodal chart 覆盖（`_F4D`）

* `collisionSet_subset_closedBall_F4D` / `collision_set_compact_F4D`：S4 `collar`（`μ < 1`）⇒ 源碰撞集落在
  `closedBall 0 μ`，其闭包紧、远离 `∂D`（`⊆ ball 0 1`）。只用 `ext` 的第一分量 `F = f` on `D̄`。
* `uniform_sep_of_locallyInjOn_F4D`：逐点局部单射 + 紧 ⇒ 一致分离 `hsep`（Lebesgue number）。
* `isCompact_collisionPairs_F4D` / `isClosed_collisionSet_F4D` / `isCompact_collisionSet_F4D`：
  `F` 在 `D̄` 上连续 + 一致分离 ⇒ 碰撞对集 `Σ_F`（`collisionPairs_F4D`）紧，碰撞集闭、紧。
* `locallyInjOn_of_closedDisk_immersion_F4D`：S4 `ext` + `rank`（闭盘 immersion）⇒ 逐点局部单射
  （chart 里严格可微 + 单射导数的 antilipschitz 估计 `locallyInjOn_of_hasStrictFDerivAt_F4D`）。
* **`collisionPairs_compact_F4D`（D-R-AN1-1 精确形）**：`ext` + `rank` + `collar` ⇒ `Σ_F` 紧、
  避开对角线、两投影 `⊆ closedBall 0 μ`（`μ < 1`）；局部单射版 `collisionPairs_compact_of_locallyInjOn_F4D`。
* `fiber_finite_F4D`：同一 `hsep` ⇒ 每个纤维 `F⁻¹(F z) ∩ D̄` 有限（多 partner 情形的有限性，D-R-MY4-12）。
* `exists_finite_nodal_cover_F4D`：紧 `K ⊆ collisionSet`、`collisionSet ⊆ D°` + S8 pairwise nodal
  （S-MY-F4A G4 的输出形 `∀ z w ∈ D°, z ≠ w → F z = F w → IsCollisionNodal_FIX2 F z w`）⇒ 有限个
  碰撞对 `(zᵢ, wᵢ)` 与 chart 半径 `ρᵢ`（`IsCollisionNodalAt_F4D`）使 `K ⊆ ⋃ ball zᵢ ρᵢ`。
* consumer `IsPreparedSheetComplex_FIX2.collisionSet_nodal_cover_F4D`：24 字段 prepared 数据（无额外前提）⇒
  整个碰撞集紧、`⊆ D°`、有限 nodal cover。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

/-! ## (a) collar ⇒ 碰撞集闭包紧、远离 `∂D` -/

section Collar

variable {M : Type u}

/-- collar（`μ` 外 `f` 单射）⇒ 源碰撞集 `⊆ closedBall 0 μ`。 -/
theorem collisionSet_subset_closedBall_F4D {f : closedDisk → M} {F : ℂ → M}
    (hF : ∀ z : closedDisk, F z = f z) {μ : ℝ}
    (hμ : ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w) :
    collisionSet_F4D F ⊆ Metric.closedBall (0 : ℂ) μ := by
  rintro z ⟨hz, w, hw, hwz, hFwz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  have heq := hμ ⟨z, hz⟩ ⟨w, hw⟩ (not_le.1 hlt) (by rw [← hF, ← hF]; exact hFwz.symm)
  exact hwz (congrArg Subtype.val heq).symm

end Collar

section Ext

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **(a) `collision_set_compact_F4D`**：S4 的 `ext` + `collar` ⇒ 存在 `μ < 1`，源碰撞集的闭包紧、
`⊆ closedBall 0 μ`（因而 `⊆ D°`，远离 `∂D`）。 -/
theorem collision_set_compact_F4D {f : C(closedDisk, M)} {F : ℂ → M}
    (hext : SmoothDiskExtension (E := E) f F)
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w) :
    ∃ μ : ℝ, μ < 1 ∧ IsCompact (closure (collisionSet_F4D F)) ∧
      closure (collisionSet_F4D F) ⊆ Metric.closedBall (0 : ℂ) μ ∧
      closure (collisionSet_F4D F) ⊆ Metric.ball (0 : ℂ) 1 := by
  obtain ⟨μ, hμ1, hμ⟩ := hcollar
  have hsub : closure (collisionSet_F4D F) ⊆ Metric.closedBall (0 : ℂ) μ :=
    closure_minimal (collisionSet_subset_closedBall_F4D (f := ⇑f) hext.1 hμ)
      Metric.isClosed_closedBall
  exact ⟨μ, hμ1, (isCompact_closedBall 0 μ).of_isClosed_subset isClosed_closure hsub, hsub,
    hsub.trans (Metric.closedBall_subset_ball hμ1)⟩

/-- 推论：碰撞集本身 `⊆ D°`（S8 的 `z, w ∈ ball 0 1` 前件对每个碰撞对成立）。 -/
theorem collisionSet_subset_ball_F4D {f : C(closedDisk, M)} {F : ℂ → M}
    (hext : SmoothDiskExtension (E := E) f F)
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w) :
    collisionSet_F4D F ⊆ Metric.ball (0 : ℂ) 1 := by
  obtain ⟨_, _, _, _, hball⟩ := collision_set_compact_F4D hext hcollar
  exact subset_closure.trans hball

end Ext

/-! ## (a′) 一致分离 ⇒ 碰撞集闭、紧，纤维有限 -/

section Separation

/-- 碰撞对集 `Σ_F = {(z, w) | z, w ∈ D̄, z ≠ w, F z = F w}`（D-R-AN1-1 的 `Σ_f`）。 -/
def collisionPairs_F4D {M : Type u} (F : ℂ → M) : Set (ℂ × ℂ) :=
  {p | p.1 ∈ Metric.closedBall (0 : ℂ) 1 ∧ p.2 ∈ Metric.closedBall (0 : ℂ) 1 ∧ p.1 ≠ p.2 ∧
    F p.1 = F p.2}

variable {M : Type u} [TopologicalSpace M]

omit [TopologicalSpace M] in
/-- 局部单射 ⇒ 一致分离（Lebesgue number）：紧 `K` 上每点有邻域使 `F` 单射 ⇒ 存在 `δ > 0`，
`K` 中距离 `< δ` 的两点若同像则相等。闭盘 immersion 的逐点局部单射见下文
`locallyInjOn_of_closedDisk_immersion_F4D`。 -/
theorem uniform_sep_of_locallyInjOn_F4D {F : ℂ → M} {K : Set ℂ} (hK : IsCompact K)
    (hloc : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn F U) :
    ∃ δ > 0, ∀ z ∈ K, ∀ w ∈ K, dist z w < δ → F z = F w → z = w := by
  choose! U hU hinj using hloc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun z : K => interior (U z))
    hK (fun _ => isOpen_interior)
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, mem_interior_iff_mem_nhds.2 (hU z hz)⟩)
  refine ⟨δ, hδ, fun z hz w _ hzw hF => ?_⟩
  obtain ⟨i, hi⟩ := hball z hz
  have hzU : z ∈ U i := interior_subset (hi (Metric.mem_ball_self hδ))
  have hwU : w ∈ U i := interior_subset (hi (by rw [Metric.mem_ball, dist_comm]; exact hzw))
  exact hinj i i.2 hzU hwU hF

omit [TopologicalSpace M] in
/-- `Σ_F` 的第一投影 = 源碰撞集。 -/
theorem fst_image_collisionPairs_F4D {F : ℂ → M} :
    Prod.fst '' collisionPairs_F4D F = collisionSet_F4D F := by
  ext z
  constructor
  · rintro ⟨⟨z', w⟩, ⟨hz, hw, hzw, hF⟩, rfl⟩
    exact ⟨hz, w, hw, Ne.symm hzw, hF.symm⟩
  · rintro ⟨hz, w, hw, hwz, hF⟩
    exact ⟨(z, w), ⟨hz, hw, Ne.symm hwz, hF.symm⟩, rfl⟩

omit [TopologicalSpace M] in
/-- `Σ_F` 的第二投影 = 源碰撞集（对称）。 -/
theorem snd_image_collisionPairs_F4D {F : ℂ → M} :
    Prod.snd '' collisionPairs_F4D F = collisionSet_F4D F := by
  ext w
  constructor
  · rintro ⟨⟨z, w'⟩, ⟨hz, hw, hzw, hF⟩, rfl⟩
    exact ⟨hw, z, hz, hzw, hF⟩
  · rintro ⟨hw, z, hz, hzw, hF⟩
    exact ⟨(z, w), ⟨hz, hw, hzw, hF⟩, rfl⟩

/-- 一致分离 + `D̄` 上连续 + `T2` ⇒ 碰撞对集 `Σ_F` 紧：它等于闭集
`{(z, w) ∈ D̄ × D̄ | δ ≤ dist z w ∧ F z = F w}`。 -/
theorem isCompact_collisionPairs_F4D [T2Space M] {F : ℂ → M}
    (hFc : ContinuousOn F (Metric.closedBall (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      dist z w < δ → F z = F w → z = w) :
    IsCompact (collisionPairs_F4D F) := by
  set D := Metric.closedBall (0 : ℂ) 1 with hD
  have hcont : ContinuousOn (fun p : ℂ × ℂ => (F p.1, F p.2))
      (D ×ˢ D ∩ {p | δ ≤ dist p.1 p.2}) :=
    ((hFc.comp continuousOn_fst fun p hp => hp.1.1).prodMk
      (hFc.comp continuousOn_snd fun p hp => hp.1.2))
  have hclosed : IsClosed ((D ×ˢ D ∩ {p | δ ≤ dist p.1 p.2}) ∩
      (fun p : ℂ × ℂ => (F p.1, F p.2)) ⁻¹' {q : M × M | q.1 = q.2}) :=
    hcont.preimage_isClosed_of_isClosed
      ((Metric.isClosed_closedBall.prod Metric.isClosed_closedBall).inter
        (isClosed_le continuous_const continuous_dist))
      isClosed_diagonal
  have heq : collisionPairs_F4D F = (D ×ˢ D ∩ {p | δ ≤ dist p.1 p.2}) ∩
      (fun p : ℂ × ℂ => (F p.1, F p.2)) ⁻¹' {q : M × M | q.1 = q.2} := by
    ext ⟨z, w⟩
    constructor
    · rintro ⟨hz, hw, hzw, hF⟩
      refine ⟨⟨⟨hz, hw⟩, ?_⟩, hF⟩
      change δ ≤ dist z w
      by_contra hlt
      exact hzw (hsep z hz w hw (not_le.1 hlt) hF)
    · rintro ⟨⟨⟨hz, hw⟩, hdist⟩, hF⟩
      refine ⟨hz, hw, fun hzw => ?_, hF⟩
      have hd : δ ≤ dist z w := hdist
      have hzw' : z = w := hzw
      rw [hzw', dist_self] at hd
      exact absurd hd (not_le.2 hδ)
  rw [heq]
  exact ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
    hclosed fun p hp => hp.1.1

/-- 一致分离 + `D̄` 上连续 + `T2` ⇒ 源碰撞集闭（`Σ_F` 紧集的第一投影）。 -/
theorem isClosed_collisionSet_F4D [T2Space M] {F : ℂ → M}
    (hFc : ContinuousOn F (Metric.closedBall (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      dist z w < δ → F z = F w → z = w) :
    IsClosed (collisionSet_F4D F) := by
  rw [← fst_image_collisionPairs_F4D]
  exact ((isCompact_collisionPairs_F4D hFc hδ hsep).image continuous_fst).isClosed

/-- 一致分离 ⇒ 源碰撞集紧。 -/
theorem isCompact_collisionSet_F4D [T2Space M] {F : ℂ → M}
    (hFc : ContinuousOn F (Metric.closedBall (0 : ℂ) 1)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      dist z w < δ → F z = F w → z = w) :
    IsCompact (collisionSet_F4D F) :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_collisionSet_F4D hFc hδ hsep)
    fun _ hz => hz.1

omit [TopologicalSpace M] in
/-- 一致分离 ⇒ 每个纤维 `{w ∈ D̄ | F w = F z}` 有限（`δ/2`-球有限覆盖，每个球至多一个纤维点）。 -/
theorem fiber_finite_F4D {F : ℂ → M} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      dist z w < δ → F z = F w → z = w) (z : ℂ) :
    {w | w ∈ Metric.closedBall (0 : ℂ) 1 ∧ F w = F z}.Finite := by
  obtain ⟨t, -, ht, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : ℂ) 1) (half_pos hδ)
  have hc : ∀ w ∈ {w | w ∈ Metric.closedBall (0 : ℂ) 1 ∧ F w = F z},
      ∃ c ∈ t, w ∈ Metric.ball c (δ / 2) := fun w hw => by
    simpa only [mem_iUnion₂, exists_prop] using hcover hw.1
  choose! c hct hwc using hc
  refine Set.Finite.of_finite_image (f := c) (ht.subset ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hct w hw
  · intro w hw w' hw' hcc
    refine hsep w hw.1 w' hw'.1 ?_ (hw.2.trans hw'.2.symm)
    have h1 := hwc w hw
    have h2 := hwc w' hw'
    rw [Metric.mem_ball] at h1 h2
    rw [hcc] at h1
    calc dist w w' ≤ dist w (c w') + dist w' (c w') := dist_triangle_right _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 h2
      _ = δ := add_halves δ

end Separation

/-! ## (a″) 闭盘 immersion ⇒ 逐点局部单射（chart 里的反函数定理估计） -/

section Immersion

/-- 导数单射的严格可微映射 `ℂ → V` 局部单射：antilipschitz 常数 `K` 与逼近常数 `(2K)⁻¹` 比较。 -/
theorem locallyInjOn_of_hasStrictFDerivAt_F4D {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {g : ℂ → V} {L : ℂ →L[ℝ] V} {z : ℂ}
    (hg : HasStrictFDerivAt g L z) (hL : Function.Injective L) : ∃ U ∈ 𝓝 z, InjOn g U := by
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith (L : ℂ →ₗ[ℝ] V)
    (LinearMap.ker_eq_bot.2 hL)
  obtain ⟨s, hs, happrox⟩ :=
    hg.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (Or.inr (by positivity))
  refine ⟨s, hs, fun a ha b hb hab => ?_⟩
  have h1 := happrox a ha b hb
  rw [hab, sub_self, zero_sub, norm_neg] at h1
  have h2 : dist a b ≤ K * dist (L a) (L b) := hanti.le_mul_dist a b
  rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
  have hK' : (0 : ℝ) < K := hK
  have h3 : ‖a - b‖ ≤ ‖a - b‖ / 2 := by
    calc ‖a - b‖ ≤ K * ‖L (a - b)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : ℝ≥0) * ‖a - b‖) := by gcongr
      _ = ‖a - b‖ / 2 := by
        push_cast
        field_simp
  have h4 : ‖a - b‖ = 0 := le_antisymm (by linarith [norm_nonneg (a - b)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 h4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **`locallyInjOn_of_closedDisk_immersion_F4D`**：S4 `ext` + `rank`（闭盘 immersion）⇒ 闭盘上每点有邻域使
`F` 单射（在 `F z` 的 chart 里 `e ∘ F` 严格可微、导数 = `mfderiv` 单射）。 -/
theorem locallyInjOn_of_closedDisk_immersion_F4D {f : C(closedDisk, M)} {F : ℂ → M}
    (hext : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ U ∈ 𝓝 z, InjOn F U := by
  intro z hz
  obtain ⟨-, N, hN, hDN, hF⟩ := hext
  have hFz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z := hF.contMDiffAt (hN.mem_nhds (hDN hz))
  set g : ℂ → E := extChartAt 𝓘(ℝ, E) (F z) ∘ F with hg
  have hgd : ContDiffAt ℝ ∞ g z := by
    have := (contMDiffAt_iff.1 hFz).2
    simpa [mfld_simps, hg, contDiffWithinAt_univ] using this
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z = fderiv ℝ g z := by
    rw [(hFz.mdifferentiableAt (by simp)).mfderiv_abuse]
    simp [mfld_simps, writtenInExtChartAt, hg]
    rfl
  have hinjL : Function.Injective (fderiv ℝ g z) := by
    rw [← hmf]
    exact hrank z hz
  obtain ⟨U, hU, hinj⟩ := locallyInjOn_of_hasStrictFDerivAt_F4D
    (hgd.hasStrictFDerivAt (by simp)) hinjL
  exact ⟨U, hU, fun a ha b hb hab => hinj ha hb (by simp only [hg, Function.comp, hab])⟩

end Immersion

/-! ## (b) 有限 nodal cover -/

section Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **(b) `exists_finite_nodal_cover_F4D`**：紧 `K ⊆ collisionSet`、`collisionSet ⊆ D°`，
S8 pairwise nodal（S-MY-F4A 输出形，显式前提）⇒ 有限个碰撞对 `p = (z, w)`（`z ∈ K`、`w` 也是碰撞点）及半径 `ρ p`，
每个满足 `IsCollisionNodalAt_F4D F z w (ρ p)`，且 `K ⊆ ⋃ₚ ball z (ρ p)`。 -/
theorem exists_finite_nodal_cover_F4D {F : ℂ → M} {K : Set ℂ} (hK : IsCompact K)
    (hKC : K ⊆ collisionSet_F4D F) (hCb : collisionSet_F4D F ⊆ Metric.ball (0 : ℂ) 1)
    (hnodal : ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1, z ≠ w → F z = F w →
      IsCollisionNodal_FIX2 (E := E) F z w) :
    ∃ (t : Finset (ℂ × ℂ)) (ρ : ℂ × ℂ → ℝ),
      (∀ p ∈ t, p.1 ∈ K ∧ p.2 ∈ collisionSet_F4D F ∧ p.1 ≠ p.2 ∧ F p.1 = F p.2 ∧
        IsCollisionNodalAt_F4D (E := E) F p.1 p.2 (ρ p)) ∧
      K ⊆ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := by
  have key : ∀ z ∈ K, ∃ w : ℂ, ∃ r : ℝ, w ∈ collisionSet_F4D F ∧ z ≠ w ∧ F z = F w ∧
      IsCollisionNodalAt_F4D (E := E) F z w r := by
    intro z hzK
    obtain ⟨hz, w, hw, hwz, hFwz⟩ := hKC hzK
    have hwC : w ∈ collisionSet_F4D F := mem_collisionSet_F4D_symm hz hw hwz hFwz
    obtain ⟨r, hr⟩ := isCollisionNodal_FIX2_iff_F4D.1
      (hnodal z (hCb (hKC hzK)) w (hCb hwC) hwz.symm hFwz.symm)
    exact ⟨w, r, hwC, hwz.symm, hFwz.symm, hr⟩
  choose! wf rf hwf using key
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun z => Metric.ball z (rf z))
    fun z hz => Metric.ball_mem_nhds z (hwf z hz).2.2.2.pos
  refine ⟨t.image fun z => (z, wf z), fun p => rf p.1, ?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨htK z hz, hwf z (htK z hz)⟩
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover hx)
    exact mem_iUnion₂.2 ⟨(z, wf z), Finset.mem_image_of_mem _ hz, hxz⟩

end Cover

/-! ## consumer：prepared 数据 + 一致分离 ⇒ 整个碰撞集的有限 nodal cover -/

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- 局部单射版：S4 `ext` + `collar` + 闭盘逐点局部单射 ⇒ 碰撞对集 `Σ_F` 紧、避开对角线
（`δ ≤ dist z w`）、两个投影都 `⊆ closedBall 0 μ`（`μ < 1`）。 -/
theorem collisionPairs_compact_of_locallyInjOn_F4D [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
    (hext : SmoothDiskExtension (E := E) f F)
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w)
    (hloc : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ U ∈ 𝓝 z, InjOn F U) :
    IsCompact (collisionPairs_F4D F) ∧
      (∃ δ > 0, ∀ p ∈ collisionPairs_F4D F, δ ≤ dist p.1 p.2) ∧
      ∃ μ : ℝ, μ < 1 ∧ Prod.fst '' collisionPairs_F4D F ⊆ Metric.closedBall (0 : ℂ) μ ∧
        Prod.snd '' collisionPairs_F4D F ⊆ Metric.closedBall (0 : ℂ) μ := by
  obtain ⟨δ, hδ, hsep⟩ :=
    uniform_sep_of_locallyInjOn_F4D (isCompact_closedBall (0 : ℂ) 1) hloc
  obtain ⟨μ, hμ1, hμ⟩ := hcollar
  have hsub := collisionSet_subset_closedBall_F4D (f := ⇑f) hext.1 hμ
  obtain ⟨-, Nn, -, hDN, hsmooth⟩ := hext
  have hFc : ContinuousOn F (Metric.closedBall (0 : ℂ) 1) := hsmooth.continuousOn.mono hDN
  refine ⟨isCompact_collisionPairs_F4D hFc hδ hsep, ⟨δ, hδ, fun p hp => ?_⟩, μ, hμ1, ?_, ?_⟩
  · by_contra hlt
    exact hp.2.2.1 (hsep p.1 hp.1 p.2 hp.2.1 (not_le.1 hlt) hp.2.2.2)
  · rw [fst_image_collisionPairs_F4D]
    exact hsub
  · rw [snd_image_collisionPairs_F4D]
    exact hsub

/-- **D-R-AN1-1 精确形（G1(a)）**：S4 `ext` + `collar` + **闭盘 immersion**（`rank`）⇒ 碰撞对集 `Σ_F` 紧、
避开对角线（`δ ≤ dist z w`）、两个投影都 `⊆ closedBall 0 μ`（`μ < 1`，即 `D̄_μ ⋐ D`）。 -/
theorem collisionPairs_compact_F4D [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
    (hext : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hcollar : ∃ μ : ℝ, μ < 1 ∧ ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ → f z = f w → z = w) :
    IsCompact (collisionPairs_F4D F) ∧
      (∃ δ > 0, ∀ p ∈ collisionPairs_F4D F, δ ≤ dist p.1 p.2) ∧
      ∃ μ : ℝ, μ < 1 ∧ Prod.fst '' collisionPairs_F4D F ⊆ Metric.closedBall (0 : ℂ) μ ∧
        Prod.snd '' collisionPairs_F4D F ⊆ Metric.closedBall (0 : ℂ) μ :=
  collisionPairs_compact_of_locallyInjOn_F4D hext hcollar
    (locallyInjOn_of_closedDisk_immersion_F4D hext hrank)

/-- consumer：24 字段 prepared（S4 `ext`/`rank`/`collar` + S8 `nodal`）⇒ 碰撞集紧、`⊆ D°`、
被有限个 nodal chart 覆盖（无额外前提）。 -/
theorem IsPreparedSheetComplex_FIX2.collisionSet_nodal_cover_F4D [T2Space M]
    {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX2 (E := E) f F T α N A φ h) :
    IsCompact (collisionSet_F4D F) ∧ collisionSet_F4D F ⊆ Metric.ball (0 : ℂ) 1 ∧
      ∃ (t : Finset (ℂ × ℂ)) (ρ : ℂ × ℂ → ℝ),
        (∀ p ∈ t, p.1 ∈ collisionSet_F4D F ∧ p.2 ∈ collisionSet_F4D F ∧ p.1 ≠ p.2 ∧
          F p.1 = F p.2 ∧ IsCollisionNodalAt_F4D (E := E) F p.1 p.2 (ρ p)) ∧
        collisionSet_F4D F ⊆ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := by
  obtain ⟨hcpt, -, -⟩ := collisionPairs_compact_F4D hprep.ext hprep.rank hprep.collar
  have hcptC : IsCompact (collisionSet_F4D F) := by
    rw [← fst_image_collisionPairs_F4D]
    exact hcpt.image continuous_fst
  have hCb := collisionSet_subset_ball_F4D hprep.ext hprep.collar
  exact ⟨hcptC, hCb, exists_finite_nodal_cover_F4D hcptC subset_rfl hCb hprep.nodal⟩

end Consumer

end DifferentialGeometry.Geometry
