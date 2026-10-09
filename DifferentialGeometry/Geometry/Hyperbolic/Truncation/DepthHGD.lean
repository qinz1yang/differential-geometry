import DifferentialGeometry.Geometry.Hyperbolic.Truncation.DepthTowerGlobalHGD
import DifferentialGeometry.Geometry.Hyperbolic.TruncationEnds

/-!
# HG03 派生项 G1：截断深度 ∀ S ≥ 0（S-HG-DERIV G1，后缀 `_HGD`）

`HyperbolicTruncation` 没有深度字段；深度 = 相对参考截断 `Tr₀` 的 cusp 坐标深度 `S`
（cusp 坐标 = H 里到边界环面的距离，`TruncationDistance`）。输入 `exists_depth_tower_HGD`：

* `range_inclusion_eq_of_compl_tail_HGD`：核心的补 = 深度 `> S` 的尾部 ⇒
  核心 = `Tr₀` 的核心 ∪ cusp 深度 `≤ S` 的 collar（`cusp_zero / intersection / exhausts / 单射`）；
* `exists_truncation_depth_HGD`：对每个 `S ≥ 0`（含所有 `R > 0`）有截断，形状同 ch12
  `exists_truncation_at_level_C1`（`range T'.inclusion = range T.inclusion ∪ ⋃ T.cuspMap i '' …`），
  cusp 个数不变（两边都 = `endCount`）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open Set MeasureTheory Filter GC.Endpoint

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- 深度 tower 的两种写法等价：核心 = 参考核心 ∪ 深度 `≤ S` 的 cusp 区域。 -/
theorem range_inclusion_eq_of_compl_tail_HGD {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr₀ Tr : HyperbolicTruncation H) {S : ℝ} (hS : 0 ≤ S)
    (h : (range Tr.inclusion)ᶜ =
      ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0}) :
    range Tr.inclusion =
      range Tr₀.inclusion ∪ ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | p.2.val 0 ≤ S} := by
  rw [← compl_compl (range Tr.inclusion), h]
  ext x
  simp only [mem_compl_iff, mem_iUnion, mem_image, mem_ofPred_eq, mem_union, not_exists, not_and]
  constructor
  · intro hx
    have hx' : x ∈ range Tr₀.inclusion ∪ ⋃ i, range (Tr₀.cuspMap i) := by
      rw [Tr₀.exhausts]
      exact mem_univ x
    rcases hx' with hcore | hcusp
    · exact Or.inl hcore
    · obtain ⟨i, p, rfl⟩ := mem_iUnion.mp hcusp
      exact Or.inr ⟨i, p, not_lt.mp (fun hp => hx i p hp rfl), rfl⟩
  · rintro (hcore | ⟨i, p, hp, rfl⟩) j q hq hqx
    · have hint : x ∈ range Tr₀.inclusion ∩ range (Tr₀.cuspMap j) :=
        ⟨hcore, ⟨q, hqx⟩⟩
      rw [Tr₀.intersection j] at hint
      obtain ⟨t, ht⟩ := hint
      have heq := (Tr₀.cuspEmbedding j).isEmbedding.injective (ht.trans hqx.symm)
      have hz : q.2.val 0 = 0 := by
        rw [← heq]
        rfl
      linarith
    · have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (Tr₀.cusp_disjoint hne) ⟨p, rfl⟩ ⟨q, hqx⟩
      subst hij
      have hpq := (Tr₀.cuspEmbedding i).isEmbedding.injective hqx
      subst hpq
      linarith

/-- **G1（ch12 `exists_truncation_at_level_C1` 同形，对所有深度 `S ≥ 0`）**：存在参考截断 `Tr₀`，
对每个 `S ≥ 0` 有截断 `Tr`，核心 = `Tr₀` 的核心 ∪ cusp 深度 `≤ S` 的 collar，补 = 深度 `> S` 的尾部，
cusp 个数不变。 -/
theorem exists_truncation_depth_HGD (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ Tr₀ : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      Tr.count = Tr₀.count ∧
      (range Tr.inclusion)ᶜ = ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | S < p.2.val 0} ∧
      range Tr.inclusion =
        range Tr₀.inclusion ∪ ⋃ i, Tr₀.cuspMap i '' {p : CuspHalfSpace | p.2.val 0 ≤ S} := by
  obtain ⟨Tr₀, hT⟩ := exists_depth_tower_HGD H
  refine ⟨Tr₀, fun S hS => ?_⟩
  obtain ⟨Tr, hTr⟩ := hT S hS
  refine ⟨Tr, ?_, hTr, range_inclusion_eq_of_compl_tail_HGD Tr₀ Tr hS hTr⟩
  have h := Tr.endCount_eq_count.symm.trans Tr₀.endCount_eq_count
  exact_mod_cast h

/-- consumer：ch12 `exists_truncation_at_level_C1` 的结论形状（`univ ×ˢ {z ≤ S}`），
对每个 `S ≥ 0`，相对同一个 `T`，不假设 `2 ≤ S`。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ T : HyperbolicTruncation H, ∀ S : ℝ, 0 ≤ S → ∃ T' : HyperbolicTruncation H,
      ∃ _ : T'.count = T.count,
        range T'.inclusion = range T.inclusion ∪
          ⋃ i, T.cuspMap i '' (univ ×ˢ {u : EuclideanHalfSpace 1 | u.val 0 ≤ S}) := by
  obtain ⟨T, hT⟩ := exists_truncation_depth_HGD H
  refine ⟨T, fun S hS => ?_⟩
  obtain ⟨T', hc, -, hrange⟩ := hT S hS
  have hset : {p : CuspHalfSpace | p.2.val 0 ≤ S} =
      univ ×ˢ {u : EuclideanHalfSpace 1 | u.val 0 ≤ S} := by
    ext p
    simp
  rw [hset] at hrange
  exact ⟨T', hc, hrange⟩

end DifferentialGeometry.Geometry.Hyperbolic
