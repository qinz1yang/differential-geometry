import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff Topology

/-!
# `PersistentCuspExterior.region` 与 `PrescribedCuspMeridian.transported` 的几何事实
（lane S-A14-STATIC，G3）

`E.region t = (⋃ i, cores.map i t '' (inclusion '' core.interior))ᶜ`（`t ≥ E.start`）。
`cores.map i t` 随 `t` 移动，所以不同 `t` 的 `region` **不**相等（也没有 G1 的 stage 等价把它们
对到一起）；这里给出每个 `t` 上 A14 kernel 的 hypothesis `range γ ⊆ frontier W` 需要的几何事实：

* `isClosed_region_ST`：`region t` 闭（`cuspPart_ST` 开：`interior_image` 开 + 在
  `domain` 内的 `cores.map i t` 单射连续 ⇒ invariance of domain（`isOpen_image_of_continuousOn_injOn`））；
* `frontier_region_eq_ST`：
  `frontier (region t) = ⋃ i, cores.map i t '' (inclusion '' (core.interior)ᶜ)`
  （`cores.disjoint` + 单射 + `ModelWithCorners.dense_interior`），
  `frontier_region_eq_torus_ST`：等于 cusp 边界环面的像 `⋃ i k, range (x ↦ map i t (cuspMap k (x, 0)))`；
* `isCompact_frontier_region_ST`；
* `range_transported_subset_frontier_region_ST`：
  `range (M.transported t ht) ⊆ frontier (M.exterior.region t)`
  （`prescribed` + `cusp_zero` + `boundary_zero`），以及 `range_transported_subset_region_ST`。
-/

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- 第 `i` 个 cusp 内部（`core.interior`）在 `cores.map i t ∘ inclusion` 下的像。 -/
def PersistentCuspExterior.cuspPart_ST (E : PersistentCuspExterior cores)
    (i : Fin cores.count) (t : ℝ) (ht : E.start ≤ t) : Set (postStage F.observation t).Carrier :=
  cores.map i t (E.after_cores.trans ht) ''
    ((E.truncation i).inclusion ''
      ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier))

/-- `t ≥ start` 时 `region t` 是 cusp 内部像的并集的补。 -/
theorem region_eq_compl_cuspPart_ST (E : PersistentCuspExterior cores) {t : ℝ} (ht : E.start ≤ t) :
    E.region t = (⋃ i, E.cuspPart_ST i t ht)ᶜ := by
  simp only [PersistentCuspExterior.region, dite_eq_left ht]
  rfl

/-- `t < start` 时 `region t = univ`。 -/
theorem region_eq_univ_of_lt_ST (E : PersistentCuspExterior cores) {t : ℝ} (ht : ¬ E.start ≤ t) :
    E.region t = univ := by
  simp only [PersistentCuspExterior.region, ht, dite_false]

/-- `range inclusion ⊆ domain i t`（`in_ball` + `advertised_ball`）。 -/
theorem range_inclusion_subset_domain_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t : ℝ} (ht : E.start ≤ t) :
    range (E.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier) :=
  (E.in_ball i t ht).trans (cores.advertised_ball i t (E.after_cores.trans ht))

/-- `cores.map i t` 在 `domain i t` 上单射（`embedding` 字段）。 -/
theorem injOn_map_domain_ST (i : Fin cores.count) {t : ℝ} (ht : cores.start ≤ t) :
    InjOn (cores.map i t ht) (cores.domain i t : Set (cores.model i).Carrier) := by
  intro x hx y hy hxy
  have := (cores.embedding i t ht).isEmbedding.injective
    (a₁ := (⟨x, hx⟩ : cores.domain i t)) (a₂ := ⟨y, hy⟩) hxy
  exact congrArg Subtype.val this

/-- `domain i t` 内的开集在 `cores.map i t` 下的像是开集（invariance of domain）。 -/
theorem isOpen_map_image_ST (i : Fin cores.count) {t : ℝ} (ht : cores.start ≤ t)
    {U : Set (cores.model i).Carrier} (hU : IsOpen U)
    (hUd : U ⊆ (cores.domain i t : Set (cores.model i).Carrier)) :
    IsOpen (cores.map i t ht '' U) :=
  isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hU
    ((cores.smooth i t ht).continuousOn.mono hUd) ((injOn_map_domain_ST i ht).mono hUd)

/-- cusp 内部的像是开集。 -/
theorem isOpen_cuspPart_ST (E : PersistentCuspExterior cores) (i : Fin cores.count) {t : ℝ}
    (ht : E.start ≤ t) : IsOpen (E.cuspPart_ST i t ht) :=
  isOpen_map_image_ST i (E.after_cores.trans ht) (E.truncation i).interior_image
    ((image_subset_range _ _).trans (range_inclusion_subset_domain_ST E i ht))

/-- **G3**：`region t` 是闭集（每个 `t`）。 -/
theorem isClosed_region_ST (E : PersistentCuspExterior cores) (t : ℝ) :
    IsClosed (E.region t) := by
  by_cases ht : E.start ≤ t
  · rw [region_eq_compl_cuspPart_ST E ht]
    exact (isOpen_iUnion fun i => isOpen_cuspPart_ST E i ht).isClosed_compl
  · rw [region_eq_univ_of_lt_ST E ht]
    exact isClosed_univ

/-- `cores.map i t '' range inclusion` 紧。 -/
theorem isCompact_map_range_inclusion_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t : ℝ} (ht : E.start ≤ t) :
    IsCompact (cores.map i t (E.after_cores.trans ht) '' range (E.truncation i).inclusion) :=
  (isCompact_range (E.truncation i).inclusion.continuous).image_of_continuousOn
    ((cores.smooth i t _).continuousOn.mono (range_inclusion_subset_domain_ST E i ht))

/-- `cores.map i t ∘ inclusion` 连续。 -/
theorem continuous_map_comp_inclusion_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t : ℝ} (ht : E.start ≤ t) :
    Continuous (fun c : (E.truncation i).core.Carrier =>
      cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c)) :=
  ((cores.smooth i t _).continuousOn).comp_continuous (E.truncation i).inclusion.continuous
    (fun c => range_inclusion_subset_domain_ST E i ht ⟨c, rfl⟩)

/-- core 的非内部点（边界点）的像不在任何 cusp 内部像里（单射 + `cores.disjoint`）。 -/
theorem not_mem_cuspPart_of_boundary_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t : ℝ} (ht : E.start ≤ t) {c : (E.truncation i).core.Carrier}
    (hc : c ∉ ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)) :
    cores.map i t (E.after_cores.trans ht) ((E.truncation i).inclusion c) ∉
      ⋃ j, E.cuspPart_ST j t ht := by
  intro hx
  obtain ⟨j, y, ⟨c', hc', rfl⟩, hy⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · subst hji
    have h1 := injOn_map_domain_ST j (E.after_cores.trans ht)
      (range_inclusion_subset_domain_ST E j ht ⟨c', rfl⟩)
      (range_inclusion_subset_domain_ST E j ht ⟨c, rfl⟩) hy
    have h2 := (E.truncation j).embedding.isEmbedding.injective h1
    exact hc (h2 ▸ hc')
  · exact Set.disjoint_left.1 (cores.disjoint t (E.after_cores.trans ht) hji)
      ⟨_, range_inclusion_subset_domain_ST E j ht ⟨c', rfl⟩, hy⟩
      ⟨_, range_inclusion_subset_domain_ST E i ht ⟨c, rfl⟩, rfl⟩

/-- **G3**：`frontier (region t)` 是 core 边界（`(interior)ᶜ`）在 `cores.map i t ∘ inclusion`
下的像的并。 -/
theorem frontier_region_eq_ST (E : PersistentCuspExterior cores) {t : ℝ} (ht : E.start ≤ t) :
    frontier (E.region t) = ⋃ i, cores.map i t (E.after_cores.trans ht) ''
      ((E.truncation i).inclusion ''
        ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)ᶜ) := by
  have hopen : IsOpen (⋃ j, E.cuspPart_ST j t ht) :=
    isOpen_iUnion fun j => isOpen_cuspPart_ST E j ht
  rw [region_eq_compl_cuspPart_ST E ht, frontier_compl, hopen.frontier_eq]
  ext x
  constructor
  · rintro ⟨hcl, hnot⟩
    rw [closure_iUnion_of_finite] at hcl
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hcl
    have hW : closure (E.cuspPart_ST i t ht) ⊆
        cores.map i t (E.after_cores.trans ht) '' range (E.truncation i).inclusion :=
      closure_minimal (image_mono (image_subset_range _ _))
        (isCompact_map_range_inclusion_ST E i ht).isClosed
    obtain ⟨y, ⟨c, rfl⟩, rfl⟩ := hW hi
    refine Set.mem_iUnion.2 ⟨i, _, ⟨c, ?_, rfl⟩, rfl⟩
    intro hc
    exact hnot (Set.mem_iUnion.2 ⟨i, ⟨_, ⟨c, hc, rfl⟩, rfl⟩⟩)
  · intro hx
    obtain ⟨i, y, ⟨c, hc, rfl⟩, rfl⟩ := Set.mem_iUnion.1 hx
    refine ⟨?_, not_mem_cuspPart_of_boundary_ST E i ht hc⟩
    have hdense : Dense ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier) :=
      ModelWithCorners.dense_interior (E.truncation i).core.model
    have himg := image_closure_subset_closure_image (continuous_map_comp_inclusion_ST E i ht)
      ⟨c, hdense c, rfl⟩
    refine closure_mono ?_ himg
    rintro _ ⟨c', hc', rfl⟩
    exact Set.mem_iUnion.2 ⟨i, ⟨_, ⟨c', hc', rfl⟩, rfl⟩⟩

/-- **G3**：`frontier (region t)` 是各 cusp 边界环面 `x ↦ cuspMap k (x, 0)` 在 `cores.map i t`
下的像的并（`boundary_exhausted` + `cusp_zero`）。 -/
theorem frontier_region_eq_torus_ST (E : PersistentCuspExterior cores) {t : ℝ}
    (ht : E.start ≤ t) :
    frontier (E.region t) = ⋃ i, ⋃ k : Fin (E.truncation i).count,
      range (fun x : Torus =>
        cores.map i t (E.after_cores.trans ht) ((E.truncation i).cuspMap k (x, halfZero))) := by
  rw [frontier_region_eq_ST E ht]
  refine iUnion_congr fun i => ?_
  have hb : ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)ᶜ =
      (E.truncation i).boundary.image := by
    have h := ((E.truncation i).core.model).compl_interior (M := (E.truncation i).core.Carrier)
    rw [← (E.truncation i).boundary_exhausted, ← h]
    rfl
  rw [hb, GC.GraphManifold.BoundaryTori.image, image_iUnion, image_iUnion]
  refine iUnion_congr fun k => ?_
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, by simp only [(E.truncation i).cusp_zero]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, by simp only [(E.truncation i).cusp_zero]⟩

/-- `frontier (region t)` 紧。 -/
theorem isCompact_frontier_region_ST (E : PersistentCuspExterior cores) {t : ℝ}
    (ht : E.start ≤ t) : IsCompact (frontier (E.region t)) := by
  rw [frontier_region_eq_ST E ht]
  refine isCompact_iUnion fun i => ?_
  rw [← image_comp]
  exact ((((E.truncation i).core.interior).isOpen.isClosed_compl).isCompact).image
    (continuous_map_comp_inclusion_ST E i ht)

/-- **G3 主定理**：`range (M.transported t ht) ⊆ frontier (M.exterior.region t)`——A14 kernel
的 hypothesis `range γ ⊆ frontier W`（每个 `t ≥ exterior.start`）。 -/
theorem range_transported_subset_frontier_region_ST (M : PrescribedCuspMeridian cores) {t : ℝ}
    (ht : M.exterior.start ≤ t) :
    range (M.transported t ht) ⊆ frontier (M.exterior.region t) := by
  rintro _ ⟨x, rfl⟩
  rw [frontier_region_eq_ST M.exterior ht, M.prescribed t ht x,
    ((M.exterior.truncation M.model)).cusp_zero]
  refine Set.mem_iUnion.2 ⟨M.model, _, ⟨_, ?_, rfl⟩, rfl⟩
  intro hc
  exact ((M.exterior.truncation M.model).core.model.isInteriorPoint_iff_not_isBoundaryPoint _).1
    hc ((M.exterior.truncation M.model).boundary.boundary_zero M.port _)

/-- G3 consumer：`region` 闭 ⇒ `frontier ⊆ region`，故 `range transported ⊆ region`。 -/
theorem range_transported_subset_region_ST (M : PrescribedCuspMeridian cores) {t : ℝ}
    (ht : M.exterior.start ≤ t) : range (M.transported t ht) ⊆ M.exterior.region t :=
  (range_transported_subset_frontier_region_ST M ht).trans
    (isClosed_region_ST M.exterior t).frontier_subset

end GC.LongTime
