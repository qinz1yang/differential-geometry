import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Set
namespace Poincare.TopCat
universe u
variable {X : Type u} [TopologicalSpace X]


def subspaceInclusion {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_subtype_val.subtype_mk _⟩

theorem isQuotientMap_closedUnion {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    IsQuotientMap (Sum.elim (Set.inclusion (subset_union_left : A ⊆ A ∪ B))
      (Set.inclusion (subset_union_right : B ⊆ A ∪ B))) := by
  apply ((IsClosedEmbedding.inclusion subset_union_left
    (hA.preimage continuous_subtype_val)).isClosedMap.sumElim
    (IsClosedEmbedding.inclusion subset_union_right
      (hB.preimage continuous_subtype_val)).isClosedMap).isQuotientMap
  · exact (continuous_subtype_val.subtype_mk _).sumElim (continuous_subtype_val.subtype_mk _)
  · rintro ⟨x, hx | hx⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

theorem closedUnion_isPushout {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    IsPushout (subspaceInclusion (inter_subset_left : A ∩ B ⊆ A))
      (subspaceInclusion (inter_subset_right : A ∩ B ⊆ B))
      (subspaceInclusion (subset_union_left : A ⊆ A ∪ B))
      (subspaceInclusion (subset_union_right : B ⊆ A ∪ B)) := by
  refine ⟨⟨rfl⟩, ⟨?_⟩⟩
  apply PushoutCocone.isColimitAux'
  intro s
  let g : C(A ⊕ B, s.pt) :=
    ⟨Sum.elim s.inl s.inr, s.inl.hom.continuous.sumElim s.inr.hom.continuous⟩
  let q : C(A ⊕ B, ↥(A ∪ B)) :=
    ⟨Sum.elim (Set.inclusion (subset_union_left : A ⊆ A ∪ B))
      (Set.inclusion (subset_union_right : B ⊆ A ∪ B)),
      (continuous_subtype_val.subtype_mk _).sumElim (continuous_subtype_val.subtype_mk _)⟩
  have hf : Function.FactorsThrough g q := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg s.inl (Subtype.ext (congrArg (fun z : ↥(A ∪ B) => z.val) h))
      | inr b =>
        have he : a.val = b.val := congrArg (fun z : ↥(A ∪ B) => z.val) h
        let z : ↥(A ∩ B) := ⟨a.val, a.prop, he.symm ▸ b.prop⟩
        have hh := ConcreteCategory.congr_hom s.condition z
        change s.inl a = s.inr ⟨a.val, he.symm ▸ b.prop⟩ at hh
        exact hh.trans (congrArg s.inr (Subtype.ext he))
    | inr b =>
      cases y with
      | inl a =>
        have he : a.val = b.val := (congrArg (fun z : ↥(A ∪ B) => z.val) h).symm
        let z : ↥(A ∩ B) := ⟨a.val, a.prop, he.symm ▸ b.prop⟩
        have hh := ConcreteCategory.congr_hom s.condition z
        change s.inl a = s.inr ⟨a.val, he.symm ▸ b.prop⟩ at hh
        exact ((congrArg s.inr (Subtype.ext he)).symm.trans hh.symm)
      | inr b' => exact congrArg s.inr (Subtype.ext (congrArg (fun z : ↥(A ∪ B) => z.val) h))
  let hq := isQuotientMap_closedUnion hA hB
  let l := TopCat.ofHom (hq.lift g hf)
  have hl (z : A ⊕ B) : l (q z) = g z :=
    ContinuousMap.congr_fun (hq.lift_comp g hf) z
  refine ⟨l, ?_, ?_, ?_⟩
  · ext a
    exact hl (Sum.inl a)
  · ext b
    exact hl (Sum.inr b)
  · intro m hm hn
    ext x
    obtain ⟨z, rfl⟩ := hq.surjective x
    cases z with
    | inl a => exact (ConcreteCategory.congr_hom hm a).trans (hl (Sum.inl a)).symm
    | inr b => exact (ConcreteCategory.congr_hom hn b).trans (hl (Sum.inr b)).symm

end Poincare.TopCat
