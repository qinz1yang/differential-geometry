import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import DifferentialGeometry.Topology.Attachment.TransitionGluing

section

open Set Topology

namespace OpenPartialHomeomorph

variable {ι E M : Type*} [TopologicalSpace E] [TopologicalSpace M]

theorem apply_eq_iff_transition_eq
    (c : ι → OpenPartialHomeomorph E M) (U : Set E)
    (hU : ∀ i, U ⊆ (c i).source) (near : ι → ι → Bool)
    (hfar : ∀ i j, near i j = false → Disjoint ((c i) '' U) ((c j) '' U))
    (hover : ∀ i j, near i j = true → MapsTo (c i) U (c j).target)
    (i j : ι) (x y : U) :
    c i x = c j y ↔ ∃ _ : near i j = true, (c j).symm (c i x) = y := by
  constructor
  · intro h
    have hn : near i j = true := by
      by_contra hn
      have hfalse : near i j = false := Bool.eq_false_iff.mpr hn
      exact Set.disjoint_left.mp (hfar i j hfalse) ⟨x, x.property, rfl⟩ ⟨y, y.property, h.symm⟩
    refine ⟨hn, ?_⟩
    rw [h]
    exact (c j).left_inv (hU j y.property)
  · rintro ⟨hn, h⟩
    rw [← h]
    exact ((c j).right_inv (hover i j hn x.property)).symm

end OpenPartialHomeomorph


end

section

open Set Topology

universe u v

noncomputable section

namespace TopCat.GlueData

variable {ι E : Type u} {M : Type v} [TopologicalSpace E] [TopologicalSpace M]
    (c : ι → OpenPartialHomeomorph E M) (U : Set E)
    (hUopen : IsOpen U) (hU : ∀ i, U ⊆ (c i).source)
    (near : ι → ι → Bool) (hrefl : ∀ i, near i i = true)
    (hsymm : ∀ i j, near i j = true → near j i = true)
    (hfar : ∀ i j, near i j = false → Disjoint ((c i) '' U) ((c j) '' U))
    (hover : ∀ i j, near i j = true → MapsTo (c i) U (c j).target)

include hU hover in
private theorem chartTransition_continuousOn (a : {a : ι × ι // near a.1 a.2 = true}) :
    ContinuousOn ((c a.val.2).symm ∘ c a.val.1) U :=
  (c a.val.2).continuousOn_symm.comp ((c a.val.1).continuousOn.mono (hU a.val.1))
    (hover a.val.1 a.val.2 a.property)

include hU in
private theorem chartTransition_self (i : ι) (x : E) (hx : x ∈ U) :
    (c i).symm (c i x) = x :=
  (c i).left_inv (hU i hx)

include hU hover in
private theorem chartTransition_inv (i j : ι) (h : near i j = true) (x : E)
    (hx : x ∈ U) : (c i).symm (c j ((c j).symm (c i x))) = x := by
  rw [(c j).right_inv (hover i j h hx), (c i).left_inv (hU i hx)]

include hU hover hfar in
private theorem chartTransition_trans (i j k : ι)
    (hij : near i j = true) (hjk : near j k = true) (x : E)
    (hx : x ∈ U) (hxj : (c j).symm (c i x) ∈ U)
    (hxk : (c k).symm (c j ((c j).symm (c i x))) ∈ U) :
    ∃ _ : near i k = true,
      (c k).symm (c i x) = (c k).symm (c j ((c j).symm (c i x))) := by
  have heq : c i x = c k ((c k).symm (c j ((c j).symm (c i x)))) := by
    rw [(c k).right_inv (hover j k hjk hxj), (c j).right_inv (hover i j hij hx)]
  have hnear := (OpenPartialHomeomorph.apply_eq_iff_transition_eq c U hU near hfar hover
    i k ⟨x, hx⟩ ⟨_, hxk⟩).mp heq
  exact hnear

def ofOpenPartialHomeomorphs : TopCat.GlueData.{u} :=
  ofTransitionMaps U hUopen near
    (fun a => (c a.val.2).symm ∘ c a.val.1)
    (chartTransition_continuousOn c U hU near hover) hrefl hsymm
    (chartTransition_self c U hU)
    (fun i j h x hx _ => chartTransition_inv c U hU near hover i j h x hx)
    (chartTransition_trans c U hU near hfar hover)

theorem rel_ofOpenPartialHomeomorphs_iff (i j : ι) (x y : U) :
    (ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover).Rel
      ⟨i, x⟩ ⟨j, y⟩ ↔ c i x = c j y := by
  unfold ofOpenPartialHomeomorphs
  rw [rel_iff_graph]
  exact (OpenPartialHomeomorph.apply_eq_iff_transition_eq c U hU near hfar hover i j x y).symm

include hUopen hU in
private theorem chartCore_isOpenEmbedding (i : ι) :
    IsOpenEmbedding (fun x : U => c i x) :=
  (c i).isOpenEmbedding_restrict.comp
    (Topology.IsOpenEmbedding.inclusion (hU i) (hUopen.preimage continuous_subtype_val))

def homeomorphUnionImage :
    (ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover).toGlueData.glued ≃ₜ
      (⋃ i, (c i) '' U : Set M) :=
  ((ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover).homeomorphUnion
    (fun i (x : U) => c i x)
    (fun i j x y => (rel_ofOpenPartialHomeomorphs_iff c U hUopen hU near hrefl hsymm hfar hover i j x y).symm)
    (chartCore_isOpenEmbedding c U hUopen hU)).trans
    (Homeomorph.setCongr (by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, ⟨x, rfl⟩⟩
        exact mem_iUnion.mpr ⟨i, ⟨(x : U).val, (x : U).property, rfl⟩⟩
      · rintro ⟨_, ⟨i, rfl⟩, ⟨x, hx, rfl⟩⟩
        exact mem_iUnion.mpr ⟨i, ⟨⟨x, hx⟩, rfl⟩⟩))

@[simp]
theorem homeomorphUnionImage_ι (i : ι) (x : U) :
    ↑(homeomorphUnionImage c U hUopen hU near hrefl hsymm hfar hover
      ((ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover).toGlueData.ι i x)) =
      c i x := by
  unfold homeomorphUnionImage
  exact homeomorphUnion_ι
    (ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover)
    (fun i (x : U) => c i x)
    (fun i j x y => (rel_ofOpenPartialHomeomorphs_iff c U hUopen hU near hrefl hsymm hfar hover i j x y).symm)
    (chartCore_isOpenEmbedding c U hUopen hU) i x

@[simp]
theorem homeomorphUnionImage_symm_apply (i : ι) (x : U) :
    (homeomorphUnionImage c U hUopen hU near hrefl hsymm hfar hover).symm
      ⟨c i x, mem_iUnion.mpr ⟨i, ⟨x, x.property, rfl⟩⟩⟩ =
      (ofOpenPartialHomeomorphs c U hUopen hU near hrefl hsymm hfar hover).toGlueData.ι i x := by
  apply (homeomorphUnionImage c U hUopen hU near hrefl hsymm hfar hover).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (homeomorphUnionImage_ι c U hUopen hU near hrefl hsymm hfar hover i x).symm

end TopCat.GlueData

end

end
