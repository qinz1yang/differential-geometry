import DifferentialGeometry.Topology.SphereSeparation.ComplementPair
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.Topology.SphereSeparation

theorem closure_image_subtype_val_positive_product
    {A : Type*} [TopologicalSpace A]
    (B : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) (a : ℝ) (ha : 0 < a)
    (hlow : ∀ q : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)), q.val.2 < a → q ∈ B) :
    closure ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' B) =
      (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' closure B ∪
        range (fun q : A => (q,(0 : ℝ))) := by
  have hnonneg : closure ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' B) ⊆
      univ ×ˢ Ici (0 : ℝ) := by
    apply closure_minimal
    · rintro q ⟨z,_,rfl⟩
      exact ⟨mem_univ _,(show 0 < z.val.2 from z.property.2).le⟩
    · exact isClosed_univ.prod isClosed_Ici
  have hbase : range (fun q : A => (q,(0 : ℝ))) ⊆
      closure ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' B) := by
    rintro _ ⟨q,rfl⟩
    have hmap : (fun t : ℝ => (q,t)) '' Ioo 0 a ⊆
        (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' B := by
      rintro _ ⟨t,ht,rfl⟩
      exact ⟨⟨(q,t),mem_univ _,ht.1⟩,hlow _ ht.2,rfl⟩
    have hz : (0 : ℝ) ∈ closure (Ioo 0 a) := by rw [closure_Ioo ha.ne]; exact ⟨le_rfl,ha.le⟩
    exact closure_mono hmap (image_closure_subset_closure_image
      (continuous_const.prodMk continuous_id) ⟨0,hz,rfl⟩)
  apply Subset.antisymm
  · intro q hq
    rcases (show 0 ≤ q.2 from (hnonneg hq).2).eq_or_lt with hz | hz
    · exact Or.inr ⟨q.1,Prod.ext rfl hz⟩
    · left
      refine ⟨⟨q,mem_univ _,hz⟩,?_,rfl⟩
      rw [_root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      exact hq
  · exact union_subset (image_closure_subset_closure_image continuous_subtype_val) hbase


theorem frontier_image_subtype_val_positive_product
    {A : Type*} [TopologicalSpace A]
    {S : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))}
    (p : DifferentialGeometry.Topology.SphereSeparation.ComplementPair S)
    (hfront : frontier p.left = S) (a : ℝ) (ha : 0 < a)
    (hlow : ∀ q : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)), q.val.2 < a → q ∈ p.left) :
    frontier ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' p.left) =
      (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' S ∪
        range (fun q : A => (q,(0 : ℝ))) := by
  have hopen : IsOpen ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' p.left) :=
    (isOpen_univ.prod isOpen_Ioi).isOpenEmbedding_subtypeVal.isOpenMap _ p.isOpen_left
  rw [hopen.frontier_eq,closure_image_subtype_val_positive_product p.left a ha hlow,
    union_sdiff_distrib]
  have hdiff : (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' closure p.left \
      (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' p.left =
        (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' S := by
    rw [← image_sdiff Subtype.val_injective,← p.isOpen_left.frontier_eq,hfront]
  rw [hdiff]
  have hbase : range (fun q : A => (q,(0 : ℝ))) \
      (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (A × ℝ)) '' p.left =
        range (fun q : A => (q,(0 : ℝ))) := by
    apply sdiff_eq_left.mpr
    rw [disjoint_left]
    rintro q ⟨y,rfl⟩ ⟨z,_,hz⟩
    have h := congrArg Prod.snd hz
    have hzpos : 0 < z.val.2 := z.property.2
    change z.val.2 = 0 at h
    exact (ne_of_gt hzpos) h
  rw [hbase]


theorem interior_closure_image_subtype_val_positive_product
    {A : Type*} [TopologicalSpace A]
    {B : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))} (hB : interior (closure B) = B) :
    interior (closure ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ) '' B)) =
      (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ) '' B := by
  let f : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ := Subtype.val
  have hf : _root_.Topology.IsOpenEmbedding f := (isOpen_univ.prod isOpen_Ioi).isOpenEmbedding_subtypeVal
  have hnonneg : closure (f '' B) ⊆ univ ×ˢ Ici (0 : ℝ) := by
    apply closure_minimal
    · rintro q ⟨z,_,rfl⟩
      exact ⟨mem_univ _,(show 0 < z.val.2 from z.property.2).le⟩
    · exact isClosed_univ.prod isClosed_Ici
  have hpos : interior (closure (f '' B)) ⊆ univ ×ˢ Ioi (0 : ℝ) := by
    have h := interior_mono hnonneg
    simpa only [interior_prod_eq,interior_univ,interior_Ici] using h
  have hpre : f ⁻¹' interior (closure (f '' B)) = B := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      ← hf.isEmbedding.closure_eq_preimage_closure_image,hB]
  apply Subset.antisymm
  · intro q hq
    refine ⟨⟨q,hpos hq⟩,?_,rfl⟩
    exact hpre ▸ hq
  · rintro q ⟨z,hz,rfl⟩
    change z ∈ f ⁻¹' interior (closure (f '' B))
    rw [hpre]
    exact hz

end DifferentialGeometry.Topology.SphereSeparation
