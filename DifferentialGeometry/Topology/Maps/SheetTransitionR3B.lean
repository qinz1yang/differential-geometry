import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Maps.CoincidentGermPairs
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# O-MY-R3B G1：局部 sheet transition 与 coincident-germ 的 continuation（纯拓扑）

R3b（`no_open_sheet_coincidence`，rev2 §A-4）的拓扑半边，不含任何 analytic 输入：

* `exists_sheet_transition_of_image_subset_R3B`：`f '' V₁ ⊆ f '' V₂`（`V₁ V₂ ⊆ ℂ` 开、`f` 在两边
  各自单射）⇒ 存在非空开 `O ⊆ V₁` 和 transition `τ : O → V₂`，`f ∘ τ = f`，`τ` 连续单射且在每点
  `map τ (𝓝 z) = 𝓝 (τ z)`。证明把 `V₂` 用紧集 `K` 穷竭，**只在紧 patch `K` 上**用
  `K.restrict f` 是 closed embedding（不把 `V₂` 上的 injective map 当全局 embedding，D-R-MY2-4），
  Baire 选出 `O`，再用树里的 invariance of domain（`InvarianceOfDomainManifold.lean`）得 `τ` 局部开。
* `exists_coincident_germ_of_image_subset_R3B`：于是有一对真正的 coincident germ
  `map f (𝓝 a) = map f (𝓝 b)`，`a ∈ V₁`、`b ∈ V₂`。
* `sheet_transition_extends_R3B`：continuation（"全或无"）——紧、Hausdorff、preconnected source 上
  的连续局部单射，若 coincident-germ 关系在 collision space 里闭，则有 coincident partner 的点集
  要么空、要么是全体（树里 `isOpen_fst_image_coincidentGermPairs` + 紧性）。
* `coincidentGermPairs_eq_empty_of_singleton_R3B`：再加一个 singleton fiber ⇒ 关系为空
  （= 树里 `coincidentGermPairs_eq_empty_of_isClosed`，这里经由 continuation 重述）。

τ 的 conformal / anti-conformal 性不需要：MY-T §2 Lemma 3 的 "degree one 排除重覆盖" 在这里由
边界点的 singleton fiber 代替（全体点都有 partner 与 singleton fiber 矛盾）。
-/

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Topology

/-- `V₂ ⊆ ℂ` 开 ⇒ 可数个紧集 `K i ⊆ V₂` 覆盖 `V₂`（closed exhaustion ∩ closed balls）。 -/
theorem exists_compact_cover_of_isOpen_R3B {V : Set ℂ} (hV : IsOpen V) :
    ∃ K : ℕ × ℕ → Set ℂ, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ V) ∧ ⋃ i, K i = V := by
  obtain ⟨F, hFc, hFV, hFU, -⟩ := hV.exists_iUnion_isClosed
  refine ⟨fun i => F i.1 ∩ Metric.closedBall (0 : ℂ) i.2, fun i => ?_, fun i => ?_, ?_⟩
  · exact (isCompact_closedBall (0 : ℂ) (i.2 : ℝ)).inter_left (hFc i.1)
  · exact inter_subset_left.trans (hFV i.1)
  · apply subset_antisymm
    · exact iUnion_subset fun i => inter_subset_left.trans (hFV i.1)
    · intro z hz
      rw [← hFU] at hz
      obtain ⟨m, hm⟩ := mem_iUnion.mp hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      refine mem_iUnion.mpr ⟨(m, n), hm, ?_⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hn

/-- Baire 步：`f '' V₁ ⊆ ⋃ f '' K i`（`K i` 紧）⇒ 某个 `K i` 使 `V₁ ∩ f ⁻¹' (f '' K i)` 有内点。 -/
theorem exists_open_image_subset_compact_R3B
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : ℂ → Y} (hf : Continuous f)
    {V₁ : Set ℂ} (hV₁ : IsOpen V₁) (hne : V₁.Nonempty)
    {K : ℕ × ℕ → Set ℂ} (hK : ∀ i, IsCompact (K i)) (himg : f '' V₁ ⊆ ⋃ i, f '' K i) :
    ∃ (i : ℕ × ℕ) (O : Set ℂ), IsOpen O ∧ O.Nonempty ∧ O ⊆ V₁ ∧ f '' O ⊆ f '' K i := by
  classical
  let C : Option (ℕ × ℕ) → Set ℂ := fun j => match j with
    | none => V₁ᶜ
    | some i => f ⁻¹' (f '' K i)
  have hC : ∀ j, IsClosed (C j) := by
    intro j
    cases j with
    | none => exact hV₁.isClosed_compl
    | some i => exact ((hK i).image hf).isClosed.preimage hf
  have hCU : ⋃ j, C j = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ V₁
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (himg (mem_image_of_mem f hz))
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · exact mem_iUnion.mpr ⟨none, hz⟩
  have hdense := dense_iUnion_interior_of_closed hC hCU
  obtain ⟨z, hzV, hzI⟩ := hdense.inter_open_nonempty V₁ hV₁ hne
  obtain ⟨j, hj⟩ := mem_iUnion.mp hzI
  cases j with
  | none => exact absurd hzV (interior_subset hj)
  | some i =>
    refine ⟨i, V₁ ∩ interior (C (some i)), hV₁.inter isOpen_interior, ⟨z, hzV, hj⟩,
      inter_subset_left, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact interior_subset (s := C (some i)) hw.2

/-- **G1a 局部 sheet transition。** `f '' V₁ ⊆ f '' V₂`（开、`f` 在两边单射）⇒ 非空开 `O ⊆ V₁` 上
有 transition `τ`：落在 `V₂`、连续、单射、`f ∘ τ = f`，且 `τ` 在 `O` 的每点是局部同胚
（`map τ (𝓝 z) = 𝓝 (τ z)`，invariance of domain）。 -/
theorem exists_sheet_transition_of_image_subset_R3B
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : ℂ → Y} (hf : Continuous f)
    {V₁ V₂ : Set ℂ} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hne : V₁.Nonempty)
    (hinj₁ : InjOn f V₁) (hinj₂ : InjOn f V₂) (himg : f '' V₁ ⊆ f '' V₂) :
    ∃ (O : Set ℂ) (τ : ℂ → ℂ), IsOpen O ∧ O.Nonempty ∧ O ⊆ V₁ ∧ MapsTo τ O V₂ ∧
      ContinuousOn τ O ∧ InjOn τ O ∧ (∀ z ∈ O, f (τ z) = f z) ∧
      ∀ z ∈ O, Filter.map τ (𝓝 z) = 𝓝 (τ z) := by
  classical
  obtain ⟨K, hKc, hKV, hKU⟩ := exists_compact_cover_of_isOpen_R3B hV₂
  have himg' : f '' V₁ ⊆ ⋃ i, f '' K i := by
    rw [← image_iUnion, hKU]
    exact himg
  obtain ⟨i, O, hO, hOne, hOV, hOK⟩ :=
    exists_open_image_subset_compact_R3B hf hV₁ hne hKc himg'
  let L : Set ℂ := K i
  let τ : ℂ → ℂ := fun z => Function.invFunOn f L (f z)
  have hτspec (z : ℂ) (hz : z ∈ O) : τ z ∈ L ∧ f (τ z) = f z := by
    obtain ⟨w, hwL, hw⟩ := hOK (mem_image_of_mem f hz)
    exact Function.invFunOn_pos ⟨w, hwL, hw⟩
  have : CompactSpace L := isCompact_iff_compactSpace.mp (hKc i)
  have hLinj : Function.Injective (L.domRestrict f) :=
    injOn_iff_injective.mp (hinj₂.mono (hKV i))
  have hemb : IsClosedEmbedding (L.domRestrict f) :=
    (hf.comp continuous_subtype_val).isClosedEmbedding hLinj
  let σ : O → L := fun z => ⟨τ z, (hτspec z z.2).1⟩
  have hσ : Continuous σ := by
    apply hemb.isInducing.continuous_iff.mpr
    have hcomp : L.domRestrict f ∘ σ = fun z : O => f z := by
      funext z
      exact (hτspec z z.2).2
    rw [hcomp]
    exact hf.comp continuous_subtype_val
  have hτc : ContinuousOn τ O := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp hσ
  have hτi : InjOn τ O := by
    intro a ha b hb hab
    apply hinj₁ (hOV ha) (hOV hb)
    rw [← (hτspec a ha).2, ← (hτspec b hb).2, hab]
  refine ⟨O, τ, hO, hOne, hOV, fun z hz => hKV i (hτspec z hz).1, hτc, hτi,
    fun z hz => (hτspec z hz).2, ?_⟩
  intro z hz
  apply le_antisymm
  · exact (hτc.continuousAt (hO.mem_nhds hz)).tendsto
  · intro S hS
    obtain ⟨N, hNS, hN, hzN⟩ := mem_nhds_iff.mp (Filter.mem_map.mp hS)
    have hopen : IsOpen (τ '' (N ∩ O)) :=
      invariance_of_domain_isOpen_image_of_finrank_eq rfl (hN.inter hO)
        (hτc.mono inter_subset_right) (hτi.mono inter_subset_right)
    apply Filter.mem_of_superset (hopen.mem_nhds (mem_image_of_mem τ ⟨hzN, hz⟩))
    rintro _ ⟨w, hw, rfl⟩
    exact hNS hw.1

/-- **G1b coincident germ 种子。** `f '' V₁ ⊆ f '' V₂` ⇒ 存在 `a ∈ V₁`、`b ∈ V₂`，`f a = f b` 且
image germ 相等。（若 `V₁ ∩ V₂ = ∅`，自动 `a ≠ b`。） -/
theorem exists_coincident_germ_of_image_subset_R3B
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : ℂ → Y} (hf : Continuous f)
    {V₁ V₂ : Set ℂ} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hne : V₁.Nonempty)
    (hinj₁ : InjOn f V₁) (hinj₂ : InjOn f V₂) (himg : f '' V₁ ⊆ f '' V₂) :
    ∃ a ∈ V₁, ∃ b ∈ V₂, f a = f b ∧ Filter.map f (𝓝 a) = Filter.map f (𝓝 b) := by
  obtain ⟨O, τ, hO, ⟨z, hz⟩, hOV, hτV, -, -, hfτ, hmap⟩ :=
    exists_sheet_transition_of_image_subset_R3B hf hV₁ hV₂ hne hinj₁ hinj₂ himg
  refine ⟨z, hOV hz, τ z, hτV hz, (hfτ z hz).symm, ?_⟩
  rw [← hmap z hz, Filter.map_map]
  apply Filter.map_congr
  filter_upwards [hO.mem_nhds hz] with w hw
  exact (hfτ w hw).symm

/-- **G1 continuation（全或无）。** 紧、Hausdorff、preconnected source 上的连续局部单射 `f`，
若 coincident-germ 关系在 ordered collision space 里闭，则有 coincident partner 的点集
`Prod.fst '' coincidentGermPairs f` 要么是空集要么是全体。 -/
theorem sheet_transition_extends_R3B
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    (hclosed : IsClosed {p : orderedCollisionPairs f |
      Filter.map f (𝓝 p.1.1) = Filter.map f (𝓝 p.1.2)}) :
    Prod.fst '' coincidentGermPairs f = ∅ ∨ Prod.fst '' coincidentGermPairs f = univ := by
  classical
  let C := orderedCollisionPairs f
  let E : Set C := {p | Filter.map f (𝓝 p.1.1) = Filter.map f (𝓝 p.1.2)}
  have : CompactSpace C :=
    isCompact_iff_compactSpace.mp (isCompact_orderedCollisionPairs f hf hloc)
  have himage : (Subtype.val : C → X × X) '' E = coincidentGermPairs f := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property.1, q.property.2, hq⟩
    · intro hp
      exact ⟨⟨p, hp.1, hp.2.1⟩, hp.2.2, rfl⟩
  have hcompact : IsCompact (coincidentGermPairs f) := by
    rw [← himage]
    exact hclosed.isCompact.image continuous_subtype_val
  have hS : IsClopen (Prod.fst '' coincidentGermPairs f) :=
    ⟨(hcompact.image continuous_fst).isClosed, isOpen_fst_image_coincidentGermPairs hf hloc⟩
  rcases (Prod.fst '' coincidentGermPairs f).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr (hS.eq_univ h)

/-- G1 + singleton fiber ⇒ coincident-germ 关系为空（"全"被 singleton fiber 排除）。 -/
theorem coincidentGermPairs_eq_empty_of_singleton_R3B
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hloc : IsLocallyInjective f)
    (hclosed : IsClosed {p : orderedCollisionPairs f |
      Filter.map f (𝓝 p.1.1) = Filter.map f (𝓝 p.1.2)})
    (hsingle : ∃ x₀ : X, ∀ x : X, f x = f x₀ → x = x₀) :
    coincidentGermPairs f = ∅ := by
  rcases sheet_transition_extends_R3B hf hloc hclosed with h | h
  · exact image_eq_empty.mp h
  · obtain ⟨x₀, hx₀⟩ := hsingle
    have hx : x₀ ∈ Prod.fst '' coincidentGermPairs f := h ▸ mem_univ x₀
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hx
    exact absurd (hx₀ y hxy.2.1.symm).symm hxy.1

end DifferentialGeometry.Topology
