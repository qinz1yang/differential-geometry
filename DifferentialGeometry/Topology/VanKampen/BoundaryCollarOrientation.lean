import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation
import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section

open Set Filter Topology

namespace Poincare.Topology.ThreeManifold.TwoSidedCollar

private theorem side_subset_interior_or_compl
    {X : Type*} [TopologicalSpace X] {A K : Set X} (hA : IsPreconnected A)
    (havoid : Disjoint A (frontier K)) : A ⊆ interior K ∨ A ⊆ Kᶜ := by
  by_cases hm : (A ∩ interior K).Nonempty
  · exact Or.inl (Poincare.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hA havoid hm)
  · right
    intro x hx hxK
    have hxi : x ∉ interior K := fun hi ↦ hm ⟨x, hx, hi⟩
    exact disjoint_left.mp havoid hx ⟨subset_closure hxK, hxi⟩

theorem domain_side_of_frontier_zero
    {B X : Type*} [TopologicalSpace B] [ConnectedSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) {K : Set X}
    (hregular : closure (interior K) = K)
    (hfront : ∀ p : B × ℝ, c.toFun p ∈ frontier K ↔ p.2 = 0) :
    (∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) ∨
      (∀ p : B × ℝ, c.toFun p ∈ K ↔ 0 ≤ p.2) := by
  have hclosed : IsClosed K := hregular ▸ isClosed_closure
  let P := c.toFun '' ((univ : Set B) ×ˢ Ioi (0 : ℝ))
  let N := c.toFun '' ((univ : Set B) ×ˢ Iio (0 : ℝ))
  have hP : IsPreconnected P :=
    ((isConnected_univ.prod isConnected_Ioi).image c.toFun
      c.isOpenEmbedding_toFun.continuous.continuousOn).isPreconnected
  have hN : IsPreconnected N :=
    ((isConnected_univ.prod isConnected_Iio).image c.toFun
      c.isOpenEmbedding_toFun.continuous.continuousOn).isPreconnected
  have hPavoid : Disjoint P (frontier K) := by
    rw [disjoint_left]
    rintro x ⟨p, hp, rfl⟩ hf
    exact (ne_of_gt hp.2) ((hfront p).mp hf)
  have hNavoid : Disjoint N (frontier K) := by
    rw [disjoint_left]
    rintro x ⟨p, hp, rfl⟩ hf
    exact (ne_of_lt hp.2) ((hfront p).mp hf)
  have hzero (p : B × ℝ) (hp : p.2 = 0) : c.toFun p ∈ K :=
    hclosed.frontier_subset ((hfront p).mpr hp)
  let b₀ : B := Classical.arbitrary B
  let z := c.toFun (b₀, 0)
  have hzfront : z ∈ frontier K := (hfront (b₀, 0)).mpr rfl
  have hzrange : z ∈ c.range := ⟨(b₀, 0), rfl⟩
  rcases side_subset_interior_or_compl hP hPavoid with hPi | hPo <;>
    rcases side_subset_interior_or_compl hN hNavoid with hNi | hNo
  · have hsub : c.range ⊆ K := by
      rintro x ⟨p, rfl⟩
      rcases lt_trichotomy p.2 0 with hn | he | hp
      · exact interior_subset (hNi ⟨p, ⟨mem_univ _, hn⟩, rfl⟩)
      · exact hzero p he
      · exact interior_subset (hPi ⟨p, ⟨mem_univ _, hp⟩, rfl⟩)
    exact False.elim (hzfront.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (c.isOpen_range.mem_nhds hzrange) hsub)))
  · right
    intro p
    constructor
    · intro hp
      by_contra ht
      exact hNo ⟨p, ⟨mem_univ _, lt_of_not_ge ht⟩, rfl⟩ hp
    · intro ht
      rcases eq_or_lt_of_le ht with he | hp
      · exact hzero p he.symm
      · exact interior_subset (hPi ⟨p, ⟨mem_univ _, hp⟩, rfl⟩)
  · left
    intro p
    constructor
    · intro hp
      by_contra ht
      exact hPo ⟨p, ⟨mem_univ _, lt_of_not_ge ht⟩, rfl⟩ hp
    · intro ht
      rcases lt_or_eq_of_le ht with hn | he
      · exact interior_subset (hNi ⟨p, ⟨mem_univ _, hn⟩, rfl⟩)
      · exact hzero p he
  · have hzcl : z ∈ closure (interior K) := hregular.symm ▸ hzero (b₀, 0) rfl
    obtain ⟨x, ⟨p, rfl⟩, hx⟩ := mem_closure_iff.mp hzcl c.range c.isOpen_range hzrange
    rcases lt_trichotomy p.2 0 with hn | he | hp
    · exact False.elim (hNo ⟨p, ⟨mem_univ _, hn⟩, rfl⟩ (interior_subset hx))
    · exact False.elim (((hfront p).mpr he).2 hx)
    · exact False.elim (hPo ⟨p, ⟨mem_univ _, hp⟩, rfl⟩ (interior_subset hx))

theorem frontier_zero_of_disjoint_rest
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) {K R : Set X}
    (hfront : frontier K = Set.range e ∪ R) (havoid : Disjoint c.range R)
    (p : B × ℝ) : c.toFun p ∈ frontier K ↔ p.2 = 0 := by
  constructor
  · intro hp
    rw [hfront] at hp
    rcases hp with ⟨b, hb⟩ | hr
    · have heq : p = (b, 0) := c.isOpenEmbedding_toFun.injective
        (hb.symm.trans (c.zero_eq b).symm)
      exact congrArg Prod.snd heq
    · exact False.elim (disjoint_left.mp havoid ⟨p, rfl⟩ hr)
  · intro hp
    rw [hfront]
    left
    exact ⟨p.1, by rw [← c.zero_eq p.1]; congr 1; exact Prod.ext rfl hp.symm⟩

def reverse
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) : TwoSidedCollar e where
  toFun p := c.toFun (p.1, -p.2)
  isOpenEmbedding_toFun := c.isOpenEmbedding_toFun.comp
    ((Homeomorph.refl B).prodCongr (Homeomorph.neg ℝ)).isOpenEmbedding
  zero_eq b := by simpa using c.zero_eq b

theorem exists_outward_collar_of_frontier_zero
    {B X : Type*} [TopologicalSpace B] [ConnectedSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) {K : Set X}
    (hregular : closure (interior K) = K)
    (hfront : ∀ p : B × ℝ, c.toFun p ∈ frontier K ↔ p.2 = 0) :
    ∃ d : TwoSidedCollar e, d.range ⊆ c.range ∧
      ∀ p : B × ℝ, d.toFun p ∈ K ↔ p.2 ≤ 0 := by
  rcases c.domain_side_of_frontier_zero hregular hfront with hneg | hpos
  · exact ⟨c, subset_rfl, hneg⟩
  · refine ⟨c.reverse, ?_, ?_⟩
    · rintro x ⟨p, rfl⟩
      exact ⟨(p.1, -p.2), rfl⟩
    · intro p
      change c.toFun (p.1, -p.2) ∈ K ↔ p.2 ≤ 0
      rw [hpos]
      exact neg_nonneg

end Poincare.Topology.ThreeManifold.TwoSidedCollar
