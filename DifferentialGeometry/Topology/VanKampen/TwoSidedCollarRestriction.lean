import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

open Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

section

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e) (U : Set X) (hU : c.range ⊆ U)

def codRestrict :
    TwoSidedCollar (U.codRestrict e (fun s ↦ hU ⟨(s, 0), c.zero_eq s⟩)) where
  toFun := U.codRestrict c.toFun (fun p ↦ hU ⟨p, rfl⟩)
  isOpenEmbedding_toFun := .of_isEmbedding_isOpenMap
    (c.isOpenEmbedding_toFun.toIsEmbedding.codRestrict U (fun p ↦ hU ⟨p, rfl⟩))
    (c.isOpenEmbedding_toFun.isOpenMap.codRestrict (fun p ↦ hU ⟨p, rfl⟩))
  zero_eq s := Subtype.ext (c.zero_eq s)

@[simp]
theorem codRestrict_toFun_val (p : S × ℝ) :
    ((c.codRestrict U hU).toFun p).val = c.toFun p := rfl

@[simp]
theorem codRestrict_range :
    (c.codRestrict U hU).range = Subtype.val ⁻¹' c.range := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

theorem image_codRestrict_range :
    Subtype.val '' (c.codRestrict U hU).range = c.range := by
  ext x
  constructor
  · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(c.codRestrict U hU).toFun p, ⟨p, rfl⟩, rfl⟩

theorem codRestrict_toFun_zero_val (s : S) :
    ((c.codRestrict U hU).toFun (s, 0)).val = e s := c.zero_eq s

theorem codRestrict_complement :
    (c.codRestrict U hU).complement = Subtype.val ⁻¹' c.complement := by
  ext x
  change (¬ ∃ s : S, (⟨e s, hU ⟨(s, 0), c.zero_eq s⟩⟩ : U) = x) ↔
    ¬ ∃ s : S, e s = x.val
  constructor
  · intro hx hs
    obtain ⟨s, hs⟩ := hs
    exact hx ⟨s, Subtype.ext hs⟩
  · intro hx hs
    obtain ⟨s, hs⟩ := hs
    exact hx ⟨s, congrArg Subtype.val hs⟩

end

section

universe u v w

variable {X : Type u} [TopologicalSpace X] {S : Type v} [TopologicalSpace S]
  {ι : Type w} {e : ι → S → X}

theorem range_subset_connectedComponentIn_complement
    [PreconnectedSpace S] (c : ∀ i, TwoSidedCollar (e i))
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (J : Set ι) {i : ι} (hi : i ∉ J) {x : X} (hx : x ∈ (c i).range) :
    (c i).range ⊆ connectedComponentIn (⋃ j ∈ J, Set.range (e j))ᶜ x := by
  have hsub : (c i).range ⊆ (⋃ j ∈ J, Set.range (e j))ᶜ := by
    intro y hy hyJ
    obtain ⟨j, hjJ, s, hs⟩ := by simpa only [mem_iUnion, mem_range] using hyJ
    have hij : i ≠ j := fun hij => hi (hij.symm ▸ hjJ)
    exact Set.disjoint_left.mp (hdisj hij) hy
      ⟨(s, 0), ((c j).zero_eq s).trans hs⟩
  exact IsPreconnected.subset_connectedComponentIn
    (isPreconnected_range (c i).isOpenEmbedding_toFun.continuous) hx hsub

end

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
