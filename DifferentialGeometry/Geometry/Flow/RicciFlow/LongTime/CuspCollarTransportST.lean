import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorStaticST
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff Topology

/-!
# cusp collar 上的运输 `P_t := cores.map i t ∘ (cores.map i t₀)⁻¹`（lane S-A14-STATIC，G4）

`cores.map i t₀`、`cores.map i t` 在 `domain i t₀`、`domain i t` 上都是 smooth embedding
（`embedding` 字段）；`P_t` 定义在 `collarSet_ST = cores.map i t₀ '' (domain i t₀ ∩ domain i t)` 上。
`range inclusion ⊆ domain i t`（对所有 `t ≥ E.start`，G3），所以 core 以及它的 `cores.map` 像都
落在 collar 里。本文件（`t₀ t` 是任意 `≥ start` 的两个时刻，stage 可以不同，`P_t` 是不同 carrier
之间的 partial map）：

* `collarTransport_ST_map`：`P_t (cores.map i t₀ x) = cores.map i t x`（`x ∈ domain i t₀`）；
* `isOpen_collarSet_ST`、`injOn_collarTransport_ST`、`contMDiffOn_collarTransport_ST`
  （`C^∞`：`IsSmoothEmbedding.contMDiff_lift` 把 `(cores.map i t₀)⁻¹` 提升成 `↥W → ↥domain`）、
  `collarTransport_left_inv_ST`（`P_{t←t₀}` 与 `P_{t₀←t}` 互逆）、
  `mfderiv_map_injective_ST`、`mfderiv_collarTransport_injective_ST`；
* region：`collarTransport_mem_region_iff_ST`（collar 内 `y ∈ region t₀ ↔ P_t y ∈ region t`）、
  `collarTransport_cuspPart_ST`（cusp 内部像 ↦ cusp 内部像）、`collarTransport_frontierPart_ST`
  （core 边界像 ↦ core 边界像）；
* transported：`collarTransport_transported_ST`：`P_t ∘ transported t₀ = transported t`，
  `collarTransport_range_transported_ST`（consumer）。
-/

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- collar 运输 `P_t := cores.map i t ∘ (cores.map i t₀)⁻¹`（`invFunOn` 取 `domain i t₀` 内的逆）。 -/
def collarTransport_ST (cores : PersistentHyperbolicCores F K) (i : Fin cores.count)
    {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀) (ht : cores.start ≤ t) :
    (postStage F.observation t₀).Carrier → (postStage F.observation t).Carrier :=
  haveI : Nonempty (cores.model i).Carrier := ⟨(cores.model i).basepoint⟩
  fun y => cores.map i t ht
    (Function.invFunOn (cores.map i t₀ ht₀) (cores.domain i t₀) y)

/-- `P_t` 的定义域：`cores.map i t₀` 在 `domain i t₀ ∩ domain i t` 上的像。 -/
def collarSet_ST (cores : PersistentHyperbolicCores F K) (i : Fin cores.count)
    {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀) (_ht : cores.start ≤ t) :
    Set (postStage F.observation t₀).Carrier :=
  cores.map i t₀ ht₀ '' ((cores.domain i t₀ : Set (cores.model i).Carrier) ∩ cores.domain i t)

variable {cores : PersistentHyperbolicCores F K}

/-- `P_t (cores.map i t₀ x) = cores.map i t x`（`x ∈ domain i t₀`）。 -/
theorem collarTransport_ST_map (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀)
    (ht : cores.start ≤ t) {x : (cores.model i).Carrier}
    (hx : x ∈ (cores.domain i t₀ : Set (cores.model i).Carrier)) :
    collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x) = cores.map i t ht x := by
  have : Nonempty (cores.model i).Carrier := ⟨(cores.model i).basepoint⟩
  have := (injOn_map_domain_ST i ht₀).leftInvOn_invFunOn hx
  simp only [collarTransport_ST, this]

/-- `collarSet_ST` 是开集（invariance of domain）。 -/
theorem isOpen_collarSet_ST (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀)
    (ht : cores.start ≤ t) : IsOpen (collarSet_ST cores i ht₀ ht) :=
  isOpen_map_image_ST i ht₀ ((cores.domain i t₀).isOpen.inter (cores.domain i t).isOpen)
    inter_subset_left

/-- `P_t` 在 `collarSet_ST` 上单射。 -/
theorem injOn_collarTransport_ST (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀)
    (ht : cores.start ≤ t) :
    InjOn (collarTransport_ST cores i ht₀ ht) (collarSet_ST cores i ht₀ ht) := by
  rintro _ ⟨x, ⟨hx0, hx1⟩, rfl⟩ _ ⟨x', ⟨hx0', hx1'⟩, rfl⟩ h
  rw [collarTransport_ST_map i ht₀ ht hx0, collarTransport_ST_map i ht₀ ht hx0'] at h
  rw [injOn_map_domain_ST i ht hx1 hx1' h]

/-- **G4**：`P_t` 在开集 `collarSet_ST` 上 `C^∞`。 -/
theorem contMDiffOn_collarTransport_ST (i : Fin cores.count) {t₀ t : ℝ}
    (ht₀ : cores.start ≤ t₀) (ht : cores.start ≤ t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (collarTransport_ST cores i ht₀ ht)
      (collarSet_ST cores i ht₀ ht) := by
  intro y hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  let W : TopologicalSpace.Opens (postStage F.observation t₀).Carrier :=
    ⟨collarSet_ST cores i ht₀ ht, isOpen_collarSet_ST i ht₀ ht⟩
  rw [← contMDiffAt_subtype_iff (U := W) (x := ⟨y, hy⟩)]
  have hf := cores.embedding i t₀ ht₀
  have hgf : range (Subtype.val : W → (postStage F.observation t₀).Carrier) ⊆
      range (fun x : cores.domain i t₀ => cores.map i t₀ ht₀ x) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, ⟨hx0, _⟩, hxz⟩ := z.2
    exact ⟨⟨x, hx0⟩, hxz⟩
  have hL := hf.contMDiff_lift (contMDiff_subtype_val (U := W)) hgf
  have hcomp : ∀ z : W, cores.map i t₀ ht₀ (hf.lift Subtype.val hgf z).1 = z.1 :=
    fun z => hf.comp_lift hgf z
  have hLmem : ∀ z : W, (hf.lift Subtype.val hgf z).1 ∈
      (cores.domain i t₀ : Set (cores.model i).Carrier) ∩ cores.domain i t := by
    intro z
    obtain ⟨x, ⟨hx0, hx1⟩, hxz⟩ := z.2
    have hx : (hf.lift Subtype.val hgf z).1 = x :=
      (injOn_map_domain_ST i ht₀) (hf.lift Subtype.val hgf z).2 hx0 ((hcomp z).trans hxz.symm)
    exact hx ▸ ⟨hx0, hx1⟩
  have hfun : (fun z : W => collarTransport_ST cores i ht₀ ht z.1) =
      (fun x : cores.domain i t₀ => cores.map i t ht x.1) ∘ hf.lift Subtype.val hgf := by
    funext z
    have h := collarTransport_ST_map i ht₀ ht (hf.lift Subtype.val hgf z).2
    rw [hcomp z] at h
    exact h
  rw [hfun]
  refine ContMDiffAt.comp (⟨y, hy⟩ : W) ?_ hL.contMDiffAt
  rw [contMDiffAt_subtype_iff (U := cores.domain i t₀) (f := cores.map i t ht)]
  exact (cores.smooth i t ht).contMDiffAt
    ((cores.domain i t).isOpen.mem_nhds (hLmem ⟨y, hy⟩).2)

/-- `range inclusion ⊆ domain i t₀ ∩ domain i t`。 -/
theorem range_inclusion_subset_domain_both_ST (E : PersistentCuspExterior cores)
    (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : E.start ≤ t₀) (ht : E.start ≤ t) :
    range (E.truncation i).inclusion ⊆
      (cores.domain i t₀ : Set (cores.model i).Carrier) ∩ cores.domain i t :=
  subset_inter (range_inclusion_subset_domain_ST E i ht₀) (range_inclusion_subset_domain_ST E i ht)

/-- core 的 `cores.map i t₀` 像落在 collar 里。 -/
theorem map_inclusion_mem_collarSet_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t₀ t : ℝ} (ht₀ : E.start ≤ t₀) (ht : E.start ≤ t) (c : (E.truncation i).core.Carrier) :
    cores.map i t₀ (E.after_cores.trans ht₀) ((E.truncation i).inclusion c) ∈
      collarSet_ST cores i (E.after_cores.trans ht₀) (E.after_cores.trans ht) :=
  ⟨_, range_inclusion_subset_domain_both_ST E i ht₀ ht ⟨c, rfl⟩, rfl⟩

/-- `cores.map i t` 在 `domain` 内每点 `mfderiv` 单射（subtype 的 immersion 传回 ambient）。 -/
theorem mfderiv_map_injective_ST (i : Fin cores.count) {t : ℝ} (ht : cores.start ≤ t)
    {x : (cores.model i).Carrier} (hx : x ∈ (cores.domain i t : Set (cores.model i).Carrier)) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (cores.map i t ht) x) := by
  have hinj := ((cores.embedding i t ht).isImmersion.isImmersionAt (⟨x, hx⟩ : cores.domain i t)
    ).mfderiv_injective (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) (cores.map i t ht) x :=
    ((cores.smooth i t ht).contMDiffAt ((cores.domain i t).isOpen.mem_nhds hx)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : cores.domain i t → _) ⟨x, hx⟩ :=
    ((contMDiff_subtype_val (U := cores.domain i t)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp (⟨x, hx⟩ : cores.domain i t) hmd hval
  have hid := DifferentialGeometry.mfderiv_subtype_val (I := 𝓡 3) (cores.domain i t) ⟨x, hx⟩
  change mfderiv (𝓡 3) (𝓡 3) (fun y : cores.domain i t => cores.map i t ht y) ⟨x, hx⟩ = _ at hcomp
  rw [hid] at hcomp
  rw [hcomp] at hinj
  exact hinj

/-- `P_{t←t₀}` 与 `P_{t₀←t}` 在 collar 上互逆。 -/
theorem collarTransport_left_inv_ST (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : cores.start ≤ t₀)
    (ht : cores.start ≤ t) {y : (postStage F.observation t₀).Carrier}
    (hy : y ∈ collarSet_ST cores i ht₀ ht) :
    collarTransport_ST cores i ht ht₀ (collarTransport_ST cores i ht₀ ht y) = y := by
  obtain ⟨x, ⟨hx0, hx1⟩, rfl⟩ := hy
  rw [collarTransport_ST_map i ht₀ ht hx0, collarTransport_ST_map i ht ht₀ hx1]

/-- **G4**：`P_t` 在 collar 内每点 `mfderiv` 单射（左逆 + 链式法则）。 -/
theorem mfderiv_collarTransport_injective_ST (i : Fin cores.count) {t₀ t : ℝ}
    (ht₀ : cores.start ≤ t₀) (ht : cores.start ≤ t) {y : (postStage F.observation t₀).Carrier}
    (hy : y ∈ collarSet_ST cores i ht₀ ht) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht₀ ht) y) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hP : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (collarTransport_ST cores i ht₀ ht) y :=
    (contMDiffOn_collarTransport_ST i ht₀ ht).contMDiffAt
      ((isOpen_collarSet_ST i ht₀ ht).mem_nhds hy)
  obtain ⟨x, ⟨hx0, hx1⟩, rfl⟩ := hy
  have hy' : collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x) ∈
      collarSet_ST cores i ht ht₀ := by
    rw [collarTransport_ST_map i ht₀ ht hx0]
    exact ⟨x, ⟨hx1, hx0⟩, rfl⟩
  have hP' : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (collarTransport_ST cores i ht ht₀)
      (collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x)) :=
    (contMDiffOn_collarTransport_ST i ht ht₀).contMDiffAt
      ((isOpen_collarSet_ST i ht ht₀).mem_nhds hy')
  have hev : (collarTransport_ST cores i ht ht₀ ∘ collarTransport_ST cores i ht₀ ht)
      =ᶠ[𝓝 (cores.map i t₀ ht₀ x)] id := by
    filter_upwards [(isOpen_collarSet_ST i ht₀ ht).mem_nhds ⟨x, ⟨hx0, hx1⟩, rfl⟩] with z hz
    exact collarTransport_left_inv_ST i ht₀ ht hz
  have hcomp := mfderiv_comp (cores.map i t₀ ht₀ x) (hP'.mdifferentiableAt hne)
    (hP.mdifferentiableAt hne)
  rw [hev.mfderiv_eq, mfderiv_id] at hcomp
  intro v w hvw
  have := congrArg (mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht ht₀)
    (collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x))) hvw
  have h2 : v = (mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht ht₀)
      (collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x)))
      ((mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht₀ ht) (cores.map i t₀ ht₀ x)) v) :=
    congrArg (fun L => L v) hcomp
  have h3 : w = (mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht ht₀)
      (collarTransport_ST cores i ht₀ ht (cores.map i t₀ ht₀ x)))
      ((mfderiv (𝓡 3) (𝓡 3) (collarTransport_ST cores i ht₀ ht) (cores.map i t₀ ht₀ x)) w) :=
    congrArg (fun L => L w) hcomp
  rw [h2, h3]
  exact this

/-- `x ∈ domain i t` 的 `cores.map i t x` 落在某个 cusp 内部像里当且仅当 `x ∈ inclusion '' interior`。 -/
theorem mem_cuspUnion_iff_ST {E : PersistentCuspExterior cores} {i : Fin cores.count} {t : ℝ}
    (ht : E.start ≤ t) {x : (cores.model i).Carrier}
    (hx : x ∈ (cores.domain i t : Set (cores.model i).Carrier)) :
    cores.map i t (E.after_cores.trans ht) x ∈ ⋃ j, E.cuspPart_ST j t ht ↔
      x ∈ (E.truncation i).inclusion ''
        ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier) := by
  constructor
  · intro h
    obtain ⟨j, y, ⟨c, hc, rfl⟩, hy⟩ := Set.mem_iUnion.1 h
    by_cases hji : j = i
    · subst hji
      have := injOn_map_domain_ST j (E.after_cores.trans ht)
        (range_inclusion_subset_domain_ST E j ht ⟨c, rfl⟩) hx hy
      exact this ▸ ⟨c, hc, rfl⟩
    · exfalso
      exact Set.disjoint_left.1 (cores.disjoint t (E.after_cores.trans ht) hji)
        ⟨_, range_inclusion_subset_domain_ST E j ht ⟨c, rfl⟩, rfl⟩ ⟨x, hx, hy.symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, _, ⟨c, hc, rfl⟩, rfl⟩

/-- **G4**：collar 内 `P_t` 保持 `region`（双向）。 -/
theorem collarTransport_mem_region_iff_ST {E : PersistentCuspExterior cores}
    (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : E.start ≤ t₀) (ht : E.start ≤ t)
    {y : (postStage F.observation t₀).Carrier}
    (hy : y ∈ collarSet_ST cores i (E.after_cores.trans ht₀) (E.after_cores.trans ht)) :
    y ∈ E.region t₀ ↔
      collarTransport_ST cores i (E.after_cores.trans ht₀) (E.after_cores.trans ht) y ∈
        E.region t := by
  obtain ⟨x, ⟨hx0, hx1⟩, rfl⟩ := hy
  rw [collarTransport_ST_map i _ _ hx0, region_eq_compl_cuspPart_ST E ht₀,
    region_eq_compl_cuspPart_ST E ht, Set.mem_compl_iff, Set.mem_compl_iff,
    mem_cuspUnion_iff_ST ht₀ hx0, mem_cuspUnion_iff_ST ht hx1]

/-- **G4**：`P_t` 把第 `i` 个 cusp 内部像送到时刻 `t` 的 cusp 内部像。 -/
theorem collarTransport_cuspPart_ST (E : PersistentCuspExterior cores) (i : Fin cores.count)
    {t₀ t : ℝ} (ht₀ : E.start ≤ t₀) (ht : E.start ≤ t) :
    collarTransport_ST cores i (E.after_cores.trans ht₀) (E.after_cores.trans ht) ''
        E.cuspPart_ST i t₀ ht₀ = E.cuspPart_ST i t ht := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    rw [collarTransport_ST_map i _ _ (range_inclusion_subset_domain_ST E i ht₀ ⟨c, rfl⟩)]
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
    rw [collarTransport_ST_map i _ _ (range_inclusion_subset_domain_ST E i ht₀ ⟨c, rfl⟩)]

/-- **G4**：`P_t` 把 core 边界在 `t₀` 的像送到 `t` 的像（`frontier region` 的第 `i` 个部分）。 -/
theorem collarTransport_frontierPart_ST (E : PersistentCuspExterior cores)
    (i : Fin cores.count) {t₀ t : ℝ} (ht₀ : E.start ≤ t₀) (ht : E.start ≤ t) :
    collarTransport_ST cores i (E.after_cores.trans ht₀) (E.after_cores.trans ht) ''
        (cores.map i t₀ (E.after_cores.trans ht₀) ''
          ((E.truncation i).inclusion ''
            ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)ᶜ)) =
      cores.map i t (E.after_cores.trans ht)  ''
        ((E.truncation i).inclusion ''
          ((E.truncation i).core.interior : Set (E.truncation i).core.Carrier)ᶜ) := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    rw [collarTransport_ST_map i _ _ (range_inclusion_subset_domain_ST E i ht₀ ⟨c, rfl⟩)]
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
    rw [collarTransport_ST_map i _ _ (range_inclusion_subset_domain_ST E i ht₀ ⟨c, rfl⟩)]

/-- **G4**：`P_t ∘ transported t₀ = transported t`（`prescribed` + `cusp_zero`）。 -/
theorem collarTransport_transported_ST (M : PrescribedCuspMeridian cores) {t₀ t : ℝ}
    (ht₀ : M.exterior.start ≤ t₀) (ht : M.exterior.start ≤ t) (x : loopCircle) :
    collarTransport_ST cores M.model (M.exterior.after_cores.trans ht₀)
        (M.exterior.after_cores.trans ht) (M.transported t₀ ht₀ x) = M.transported t ht x := by
  have hmem : (M.exterior.truncation M.model).cuspMap M.port (M.loop x, halfZero) ∈
      (cores.domain M.model t₀ : Set (cores.model M.model).Carrier) := by
    rw [(M.exterior.truncation M.model).cusp_zero]
    exact range_inclusion_subset_domain_ST M.exterior M.model ht₀ ⟨_, rfl⟩
  rw [M.prescribed t₀ ht₀ x, M.prescribed t ht x, collarTransport_ST_map _ _ _ hmem]

/-- G4 consumer：`P_t '' range (transported t₀) = range (transported t)`。 -/
theorem collarTransport_range_transported_ST (M : PrescribedCuspMeridian cores) {t₀ t : ℝ}
    (ht₀ : M.exterior.start ≤ t₀) (ht : M.exterior.start ≤ t) :
    collarTransport_ST cores M.model (M.exterior.after_cores.trans ht₀)
        (M.exterior.after_cores.trans ht) '' range (M.transported t₀ ht₀) =
      range (M.transported t ht) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (collarTransport_transported_ST M ht₀ ht x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, collarTransport_transported_ST M ht₀ ht x⟩

end GC.LongTime
