import DifferentialGeometry.Topology.PiecewiseLinear.CollisionPairsLiftADP
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

/-!
# S-MY-R11PL G1（rev2 §A-5(b)）：`vertexCollisionPairs` 在 connected preimage 下**严格**下降

R11-step 的终止量是 `P_T(f, α) = vertexCollisionPairs T (diskExtension f ∘ α)`（rev2 D-3′/D-22：
**固定** source complex `T` 与 `α`，**每层不重细分**）。`CollisionPairsLiftADP`（S-MY-ADAPT G6）给的是
单调 `⊆`；本文件补严格 `⊂`（scratch `MYD3/Lanes.lean:42` `vertexCollisionPairs_ssubset_MYD3` 的对应物）。

数学（D-22 链）：
1. `p⁻¹(L) = L' ∪ τL'`（`L' = f'(D̄)`）连通 ⇒ 两个紧集相交（`exists_meet_of_isConnected_preimage_R11PL`）；
2. 相交 ⇒ `∃ x y, f x = f y ∧ f' x ≠ f' y`（`τ` 无不动点、`p ∘ τ = p`）；
3. 若所有顶点碰撞对都不被 `f'` 分开，则上层顶点映射沿下层 factor 过 `ψ`（`φ' = ψ ∘ φ` 于顶点），
   由两层**逐面非退化** simplicial factorization 与 barycentric 坐标唯一性
   （`simplicialMap_comp_of_nondegenerate_R11PL`，`simplicialMap_simplicialMap` 的广义版）
   得 `|φ'| = Ψ ∘ |φ|` ⇒ `f x = f y ⇒ f' x = f' y`，矛盾。

不要求 `pr` 本身 simplicial；`A'`、`φ'`、`h'` 是**独立的**上层 prepared 数据（不声称 `A'` 是旧 `A`
的 lift——`O ⊇ N` 并不蕴含 `h(|A|) ⊆ O`，上层 thickening 须是位于 `O` 内且与同一 `T`、`α` 兼容的
relative thickening，由 R11-step 总装提供）。`τ ∘ τ = id` 在本文件的下降论证里用不到（只用
`p ∘ τ = p`、`τ x ≠ x`、纤维 `{x, τ x}`），它由 G2（`RelRegularNbhdCoverR11PL`）的 genuine double cover 输出提供。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.Geometry DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section SimplicialComp

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **广义 simplicial 复合**（`simplicialMap_simplicialMap` 的广义版）：`φ` 逐面非退化（像面在 `L`、
`card` 保持），`ψ ∘ φ = χ` 于 `K` 的各面顶点 ⇒ `|ψ| ∘ |φ| = |χ|`（于 `|K|`）。 -/
theorem simplicialMap_comp_of_nondegenerate_R11PL [DecidableEq F]
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (φ : E → F) (ψ : F → G) (χ : E → G)
    (hφ : ∀ s ∈ K.faces, s.image φ ∈ L.faces ∧ (s.image φ).card = s.card)
    (hψφ : ∀ s ∈ K.faces, ∀ v ∈ s, ψ (φ v) = χ v) {x : E} (hx : x ∈ K.space) :
    simplicialMap L ψ (simplicialMap K φ x) = simplicialMap K χ x := by
  classical
  set s := carrierFace K x with hsdef
  have hs : s ∈ K.faces := carrierFace_mem hx
  have hxs : x ∈ convexHull ℝ (s : Set E) := mem_convexHull_carrierFace hx
  have hinj : Set.InjOn φ s := Finset.card_image_iff.mp (hφ s hs).2
  have ht : s.image φ ∈ L.faces := (hφ s hs).1
  have hfx : simplicialMap K φ x = ∑ v ∈ s, weights s x v • φ v :=
    simplicialMap_eq_of_mem K φ hs hxs
  have hfxt : simplicialMap K φ x ∈ convexHull ℝ ((s.image φ : Finset F) : Set F) :=
    simplicialMap_mem_convexHull_image K φ hs hxs
  let σ : F → E := Function.invFunOn φ s
  have hσ : ∀ v ∈ s, σ (φ v) = v := fun v hv => hinj.leftInvOn_invFunOn hv
  have hwt : ∀ u ∈ s.image φ,
      weights (s.image φ) (simplicialMap K φ x) u = weights s x (σ u) := by
    refine weights_eq (L.indep ht) hfxt ?_ ?_
    · rw [Finset.sum_image hinj, ← sum_weights hxs]
      exact Finset.sum_congr rfl fun v hv => by rw [hσ v hv]
    · rw [Finset.sum_image hinj, hfx]
      exact Finset.sum_congr rfl fun v hv => by rw [hσ v hv]
  rw [simplicialMap_eq_of_mem L ψ ht hfxt,
    Finset.sum_congr rfl fun u hu => by rw [hwt u hu], Finset.sum_image hinj,
    simplicialMap_eq_of_mem K χ hs hxs]
  exact Finset.sum_congr rfl fun v hv => by rw [hσ v hv, hψφ s hs v hv]

end SimplicialComp

section Descent

variable {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']

/-- `diskExtension` 在闭盘点上取原值（`diskExtension_coe` 的等式形）。 -/
theorem diskExtension_eq_of_eq_R11PL {Q : Type*} (g : closedDisk → Q) {q : ℂ} {u : closedDisk}
    (hq : q = u) : diskExtension g q = g u := by
  rw [hq, diskExtension_coe]

/-- 面的顶点是 `T` 的顶点。 -/
theorem mem_vertices_of_mem_face_R11PL {K : Geometry.SimplicialComplex ℝ ℂ} {s : Finset ℂ}
    (hs : s ∈ K.faces) {v : ℂ} (hv : v ∈ s) : v ∈ K.vertices :=
  K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

/-- 逐面非退化的 `φ` 把 `T` 的顶点送进 `A` 的空间。 -/
theorem vertex_image_mem_space_R11PL {N : ℕ} {T : Geometry.SimplicialComplex ℝ ℂ}
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))} {φ : ℂ → EuclideanSpace ℝ (Fin N)}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card) {v : ℂ}
    (hv : v ∈ T.vertices) : φ v ∈ A.space := by
  classical
  have h1 : ({v} : Finset ℂ).image φ ∈ A.faces := (hφ {v} hv).1
  rw [Finset.image_singleton] at h1
  exact A.vertices_subset_space h1

/-- **G1 核心**（顶点层面）：下层有碰撞 `f x = f y` 而上层 `f' x ≠ f' y` ⇒ `P_T(f', α) ⊊ P_T(f, α)`。
同 `T, α`；`φ`、`φ'` 逐面非退化（两层 `face_map`）；两个 factor identity `h ∘ |φ| = f ∘ α`、
`h' ∘ |φ'| = f' ∘ α`；`h`、`h'` 在各自 thickening 上单射；`pr ∘ f' = f`（`pr` 不必 simplicial）。 -/
theorem vertexCollisionPairs_ssubset_of_separated_R11PL {N N' : ℕ}
    (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    (hα : SurjOn α T.space (Metric.closedBall 0 1))
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M)
    (hlift : ∀ z, pr (f' z) = f z)
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {A' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
    {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card)
    (hφ' : ∀ s ∈ T.faces, s.image φ' ∈ A'.faces ∧ (s.image φ').card = s.card)
    (hinj : InjOn h A.space) (hinj' : InjOn h' A'.space)
    (hfac : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z))
    (hfac' : ∀ z ∈ T.space, h' (simplicialMap T φ' z) = diskExtension f' (α z))
    (hsep : ∃ x y : closedDisk, f x = f y ∧ f' x ≠ f' y) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) := by
  classical
  refine Finset.ssubset_def.mpr ⟨vertexCollisionPairs_lift_subset_ADP T α pr hlift, fun hsup => ?_⟩
  -- 顶点层：下层顶点碰撞 ⇒ 上层顶点碰撞
  have hvert : ∀ v ∈ T.vertices, ∀ w ∈ T.vertices,
      diskExtension f (α v) = diskExtension f (α w) →
        diskExtension f' (α v) = diskExtension f' (α w) := by
    intro v hv w hw hvw
    by_cases hne : v = w
    · rw [hne]
    · have hmem : ({v, w} : Finset ℂ) ∈ vertexCollisionPairs T (diskExtension f ∘ α) := by
        rw [mem_vertexCollisionPairs]
        refine ⟨?_, by simp [hne], fun hi => hne (hi (by simp) (by simp) hvw)⟩
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption
      have hmem' := (mem_vertexCollisionPairs T _ _).mp (hsup hmem)
      by_contra hneq
      refine hmem'.2.2 fun a ha b hb hab => ?_
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
        mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact absurd hab hneq
      · exact absurd hab.symm hneq
      · rfl
  -- 上层顶点映射沿下层 factor 过 ψ
  let ψ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N') := fun a =>
    if hex : ∃ v ∈ T.vertices, φ v = a then φ' (Classical.choose hex) else 0
  have hψ : ∀ v ∈ T.vertices, ψ (φ v) = φ' v := by
    intro v hv
    have hex : ∃ u ∈ T.vertices, φ u = φ v := ⟨v, hv, rfl⟩
    simp only [ψ, hex, ↓reduceDIte]
    obtain ⟨hu, hφu⟩ := Classical.choose_spec hex
    set u := Classical.choose hex
    have hfu : diskExtension f (α u) = diskExtension f (α v) := by
      rw [← hfac u (T.vertices_subset_space hu), ← hfac v (T.vertices_subset_space hv),
        simplicialMap_vertex T φ hu, simplicialMap_vertex T φ hv, hφu]
    have hfu' := hvert u hu v hv hfu
    rw [← hfac' u (T.vertices_subset_space hu), ← hfac' v (T.vertices_subset_space hv),
      simplicialMap_vertex T φ' hu, simplicialMap_vertex T φ' hv] at hfu'
    exact hinj' (vertex_image_mem_space_R11PL hφ' hu) (vertex_image_mem_space_R11PL hφ' hv) hfu'
  have hcomp : ∀ z ∈ T.space,
      simplicialMap A ψ (simplicialMap T φ z) = simplicialMap T φ' z := fun z hz =>
    simplicialMap_comp_of_nondegenerate_R11PL T A φ ψ φ' hφ
      (fun s hs v hv => hψ v (mem_vertices_of_mem_face_R11PL hs hv)) hz
  -- 取分离的点对并拉回到 T
  obtain ⟨x, y, hxy, hxy'⟩ := hsep
  obtain ⟨z, hz, hzx⟩ := hα x.2
  obtain ⟨w, hw, hwy⟩ := hα y.2
  have hmaps : MapsTo (simplicialMap T φ) T.space A.space :=
    simplicialMap_mapsTo T A φ fun s hs => (hφ s hs).1
  have hmaps' : MapsTo (simplicialMap T φ') T.space A'.space :=
    simplicialMap_mapsTo T A' φ' fun s hs => (hφ' s hs).1
  have heq : simplicialMap T φ z = simplicialMap T φ w := by
    refine hinj (hmaps hz) (hmaps hw) ?_
    rw [hfac z hz, hfac w hw, diskExtension_eq_of_eq_R11PL f hzx,
      diskExtension_eq_of_eq_R11PL f hwy]
    exact hxy
  apply hxy'
  have h1 : h' (simplicialMap T φ' z) = f' x := by
    rw [hfac' z hz, diskExtension_eq_of_eq_R11PL f' hzx]
  have h2 : h' (simplicialMap T φ' w) = f' y := by
    rw [hfac' w hw, diskExtension_eq_of_eq_R11PL f' hwy]
  rw [← h1, ← h2, ← hcomp z hz, ← hcomp w hw, heq]

/-- **连通 preimage ⇒ 两个 lift 像相交**（D-22 链第一步）：`p : M' → M` 的 deck `τ`（连续、`p ∘ τ = p`、
纤维 `{x, τ x}`，纤维条件只在 `range f` 之上需要），`f'` 是 `f` 的 lift，`p⁻¹(range f)` 连通
⇒ `f'(D̄) ∩ τ f'(D̄) ≠ ∅`。 -/
theorem exists_meet_of_isConnected_preimage_R11PL [T2Space M'] {f : C(closedDisk, M)}
    {f' : C(closedDisk, M')} (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M')
    (hτc : Continuous τ) (hτ₁ : ∀ x, pr (τ x) = pr x)
    (hfib : ∀ x y, pr x = pr y → y = x ∨ y = τ x)
    (hconn : IsConnected (pr ⁻¹' Set.range f)) :
    ∃ x y : closedDisk, f' x = τ (f' y) := by
  have hC₁ : IsClosed (Set.range f') := (isCompact_range f'.continuous).isClosed
  have hC₂ : IsClosed (Set.range (τ ∘ f')) :=
    (isCompact_range (hτc.comp f'.continuous)).isClosed
  have hmem : ∀ z : closedDisk, f' z ∈ pr ⁻¹' Set.range f := fun z => ⟨z, (hlift z).symm⟩
  have hmem' : ∀ z : closedDisk, τ (f' z) ∈ pr ⁻¹' Set.range f := fun z => by
    rw [mem_preimage, hτ₁]
    exact hmem z
  have hcover : pr ⁻¹' Set.range f ⊆ Set.range f' ∪ Set.range (τ ∘ f') := by
    intro u hu
    obtain ⟨z, hz⟩ := hu
    rcases hfib (f' z) u ((hlift z).trans hz) with h | h
    · exact Or.inl ⟨z, h.symm⟩
    · exact Or.inr ⟨z, h.symm⟩
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  obtain ⟨u, hu, hu₁, hu₂⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected _ _ hC₁ hC₂ hcover
    ⟨f' ⟨0, h0⟩, hmem _, ⟨⟨0, h0⟩, rfl⟩⟩ ⟨τ (f' ⟨0, h0⟩), hmem' _, ⟨⟨0, h0⟩, rfl⟩⟩
  obtain ⟨x, rfl⟩ := hu₁
  obtain ⟨y, hy⟩ := hu₂
  exact ⟨x, y, hy.symm⟩

/-- 相交 + `τ` 无不动点 + `p ∘ τ = p` ⇒ 存在被 `f` 粘合而 `f'` 分开的点对。 -/
theorem exists_separated_of_meet_R11PL {f : C(closedDisk, M)} {f' : C(closedDisk, M')}
    (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M') (hτ₁ : ∀ x, pr (τ x) = pr x)
    (hτ₃ : ∀ x, τ x ≠ x) (hmeet : ∃ x y : closedDisk, f' x = τ (f' y)) :
    ∃ x y : closedDisk, f x = f y ∧ f' x ≠ f' y := by
  obtain ⟨x, y, hxy⟩ := hmeet
  refine ⟨x, y, ?_, ?_⟩
  · rw [← hlift x, ← hlift y, hxy, hτ₁]
  · rw [hxy]
    exact hτ₃ _

/-- **G1**（scratch `vertexCollisionPairs_ssubset_MYD3` 对应物；`hmeet` 形）：`f'(D̄) ∩ τ f'(D̄) ≠ ∅` +
deck 数据（`p ∘ τ = p`、`τ` 无不动点）+ 同 `T, α` 的两层非退化 factorization ⇒ `P_T(f', α) ⊊ P_T(f, α)`。 -/
theorem vertexCollisionPairs_ssubset_R11PL {N N' : ℕ}
    (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    (hα : SurjOn α T.space (Metric.closedBall 0 1))
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M)
    (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M') (hτ₁ : ∀ x, pr (τ x) = pr x)
    (hτ₃ : ∀ x, τ x ≠ x)
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {A' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
    {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card)
    (hφ' : ∀ s ∈ T.faces, s.image φ' ∈ A'.faces ∧ (s.image φ').card = s.card)
    (hinj : InjOn h A.space) (hinj' : InjOn h' A'.space)
    (hfac : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z))
    (hfac' : ∀ z ∈ T.space, h' (simplicialMap T φ' z) = diskExtension f' (α z))
    (hmeet : ∃ x y : closedDisk, f' x = τ (f' y)) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) :=
  vertexCollisionPairs_ssubset_of_separated_R11PL T α hα pr hlift hφ hφ' hinj hinj' hfac hfac'
    (exists_separated_of_meet_R11PL pr hlift τ hτ₁ hτ₃ hmeet)

/-- **G1（connected-preimage 形，D-22 全链）**：genuine double cover 的输出形（`p ∘ τ = p`、`τ` 无不动点、
纤维 `{x, τ x}`、`τ` 连续、`p⁻¹(f(D̄))` 连通）直接给 `P_T(f', α) ⊊ P_T(f, α)`，同 `T, α`，不重细分。 -/
theorem vertexCollisionPairs_ssubset_of_isConnected_R11PL [T2Space M'] {N N' : ℕ}
    (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    (hα : SurjOn α T.space (Metric.closedBall 0 1))
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M)
    (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M') (hτc : Continuous τ)
    (hτ₁ : ∀ x, pr (τ x) = pr x) (hτ₃ : ∀ x, τ x ≠ x)
    (hfib : ∀ x y, pr x = pr y → y = x ∨ y = τ x)
    (hconn : IsConnected (pr ⁻¹' Set.range f))
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {A' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
    {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card)
    (hφ' : ∀ s ∈ T.faces, s.image φ' ∈ A'.faces ∧ (s.image φ').card = s.card)
    (hinj : InjOn h A.space) (hinj' : InjOn h' A'.space)
    (hfac : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z))
    (hfac' : ∀ z ∈ T.space, h' (simplicialMap T φ' z) = diskExtension f' (α z)) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) :=
  vertexCollisionPairs_ssubset_R11PL T α hα pr hlift τ hτ₁ hτ₃ hφ hφ' hinj hinj' hfac hfac'
    (exists_meet_of_isConnected_preimage_R11PL pr hlift τ hτc hτ₁ hfib hconn)

/-- **consumer（tower 测度）**：严格 `⊂` ⇒ `|P_T(f', α)| < |P_T(f, α)|`（总装归纳用的自然数测度）。 -/
theorem vertexCollisionPairs_card_lt_R11PL {N N' : ℕ}
    (T : Geometry.SimplicialComplex ℝ ℂ) [Finite T.faces] (α : ℂ → ℂ)
    (hα : SurjOn α T.space (Metric.closedBall 0 1))
    {f : C(closedDisk, M)} {f' : C(closedDisk, M')} (pr : M' → M)
    (hlift : ∀ z, pr (f' z) = f z)
    {A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {A' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
    {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hφ : ∀ s ∈ T.faces, s.image φ ∈ A.faces ∧ (s.image φ).card = s.card)
    (hφ' : ∀ s ∈ T.faces, s.image φ' ∈ A'.faces ∧ (s.image φ').card = s.card)
    (hinj : InjOn h A.space) (hinj' : InjOn h' A'.space)
    (hfac : ∀ z ∈ T.space, h (simplicialMap T φ z) = diskExtension f (α z))
    (hfac' : ∀ z ∈ T.space, h' (simplicialMap T φ' z) = diskExtension f' (α z))
    (hsep : ∃ x y : closedDisk, f x = f y ∧ f' x ≠ f' y) :
    (vertexCollisionPairs T (diskExtension f' ∘ α)).card <
      (vertexCollisionPairs T (diskExtension f ∘ α)).card :=
  Finset.card_lt_card
    (vertexCollisionPairs_ssubset_of_separated_R11PL T α hα pr hlift hφ hφ' hinj hinj' hfac hfac'
      hsep)

end Descent

end DifferentialGeometry.Topology.PiecewiseLinear
