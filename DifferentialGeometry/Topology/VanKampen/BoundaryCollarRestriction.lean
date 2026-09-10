import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale
import Mathlib.Topology.Compactness.Compact

noncomputable section

open Set Topology

namespace Poincare.Topology.ThreeManifold.TwoSidedCollar

def inl
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar (Sum.elim e f)) : TwoSidedCollar e where
  toFun p := c.toFun (Sum.inl p.1, p.2)
  isOpenEmbedding_toFun := c.isOpenEmbedding_toFun.comp
    (_root_.Topology.IsOpenEmbedding.inl.prodMap _root_.Topology.IsOpenEmbedding.id)
  zero_eq b := c.zero_eq (Sum.inl b)

def inr
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar (Sum.elim e f)) : TwoSidedCollar f where
  toFun p := c.toFun (Sum.inr p.1, p.2)
  isOpenEmbedding_toFun := c.isOpenEmbedding_toFun.comp
    (_root_.Topology.IsOpenEmbedding.inr.prodMap _root_.Topology.IsOpenEmbedding.id)
  zero_eq b := c.zero_eq (Sum.inr b)

theorem exists_subcollar_subset_open
    {B X : Type*} [TopologicalSpace B] [CompactSpace B] [TopologicalSpace X]
    {e : B → X} (c : TwoSidedCollar e) {U : Set X} (hU : IsOpen U)
    (hzero : Set.range e ⊆ U) :
    ∃ d : TwoSidedCollar e, d.range ⊆ U ∧ d.range ⊆ c.range := by
  have hpre : IsOpen (c.toFun ⁻¹' U) := hU.preimage c.isOpenEmbedding_toFun.continuous
  have hprod : (univ : Set B) ×ˢ ({0} : Set ℝ) ⊆ c.toFun ⁻¹' U := by
    rintro ⟨b, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero ⟨b, (c.zero_eq b).symm⟩
  obtain ⟨A, V, _, hV, hA, h₀, hAV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hpre hprod
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h₀ (mem_singleton 0)))
  let φ : B × Ioo (-r) r → X := fun p ↦ c.toFun (p.1, p.2.val)
  have hφ : IsOpenEmbedding φ :=
    c.isOpenEmbedding_toFun.comp
      (_root_.Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)
  let d := ofOpenInterval hr φ hφ (fun b ↦ c.zero_eq b)
  refine ⟨d, ?_, ?_⟩
  · rintro x ⟨p, rfl⟩
    change c.toFun (p.1, (realHomeomorphIoo r hr p.2).val) ∈ U
    apply hAV
    refine ⟨hA (mem_univ _), hball ?_⟩
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using (realHomeomorphIoo r hr p.2).property
  · rintro x ⟨p, rfl⟩
    exact ⟨(p.1, (realHomeomorphIoo r hr p.2).val), rfl⟩

def sum
    {B C X : Type*} [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
    {e : B → X} {f : C → X} (c : TwoSidedCollar e) (d : TwoSidedCollar f)
    (hd : Disjoint c.range d.range) : TwoSidedCollar (Sum.elim e f) := by
  let φ := Sum.elim c.toFun d.toFun
  have hφinj : Function.Injective φ := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (c.isOpenEmbedding_toFun.injective hxy)
      | inr y => exact False.elim (disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, hxy.symm⟩)
    | inr x =>
      cases y with
      | inl y => exact False.elim (disjoint_left.mp hd ⟨y, hxy.symm⟩ ⟨x, rfl⟩)
      | inr y => exact congrArg Sum.inr (d.isOpenEmbedding_toFun.injective hxy)
  exact {
    toFun := φ ∘ Homeomorph.sumProdDistrib
    isOpenEmbedding_toFun :=
      (c.isOpenEmbedding_toFun.sumElim d.isOpenEmbedding_toFun hφinj).comp
        Homeomorph.sumProdDistrib.isOpenEmbedding
    zero_eq := fun b ↦ by cases b <;> simp [φ, c.zero_eq, d.zero_eq] }

end Poincare.Topology.ThreeManifold.TwoSidedCollar
