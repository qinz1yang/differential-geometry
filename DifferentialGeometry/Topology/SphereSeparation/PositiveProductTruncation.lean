import DifferentialGeometry.Topology.SphereSeparation.PositiveProductFrontier
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.Topology.SphereSeparation

variable {X : Type*} [TopologicalSpace X]

theorem isPreconnected_inter_positive_product_tail [PreconnectedSpace X] [Nonempty X]
    {B : Set (X × ℝ)} (hB : IsPreconnected B) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hband : univ ×ˢ Ioo (0 : ℝ) b ⊆ B) :
    IsPreconnected (B ∩ (univ ×ˢ Ioi a)) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  let f : X × ℝ → X × ℝ := fun q => (q.1,max c q.2)
  have hf : Continuous f := continuous_fst.prodMk (continuous_const.max continuous_snd)
  have heq : B ∩ (univ ×ˢ Ioi a) = f '' B ∪ (univ ×ˢ Ioc a c) := by
    ext q
    constructor
    · rintro ⟨hq,hqa⟩
      by_cases hcq : c ≤ q.2
      · exact Or.inl ⟨q,hq,Prod.ext rfl (max_eq_right hcq)⟩
      · exact Or.inr ⟨mem_univ _,hqa.2,(le_of_not_ge hcq)⟩
    · rintro (⟨z,hz,rfl⟩ | hq)
      · refine ⟨?_,mem_univ _,lt_of_lt_of_le hac (le_max_left _ _)⟩
        by_cases hcz : c ≤ z.2
        · simpa only [f,max_eq_right hcz,Prod.mk.eta] using hz
        · exact hband ⟨mem_univ _,by change 0 < max c z.2; rw [max_eq_left (le_of_not_ge hcz)]; exact ha.trans hac,
            by change max c z.2 < b; rw [max_eq_left (le_of_not_ge hcz)]; exact hcb⟩
      · exact ⟨hband ⟨mem_univ _,ha.trans hq.2.1,hq.2.2.trans_lt hcb⟩,mem_univ _,hq.2.1⟩
  rw [heq]
  apply IsPreconnected.union' _ (hB.image f hf.continuousOn)
    (isPreconnected_univ.prod isPreconnected_Ioc)
  let x : X := Classical.arbitrary X
  refine ⟨(x,c),?_,mem_univ _,hac,le_rfl⟩
  exact ⟨(x,c),hband ⟨mem_univ _,ha.trans hac,hcb⟩,Prod.ext rfl (max_self _)⟩

theorem closure_inter_positive_product_tail
    {B : Set (X × ℝ)} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hband : univ ×ˢ Ioo (0 : ℝ) b ⊆ B) :
    closure (B ∩ (univ ×ˢ Ioi a)) = closure B ∩ (univ ×ˢ Ici a) := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact fun q hq => ⟨subset_closure hq.1,mem_univ _,(show a < q.2 from hq.2.2).le⟩
    · exact isClosed_closure.inter (isClosed_univ.prod isClosed_Ici)
  · intro q hq
    rcases (show a ≤ q.2 from hq.2.2).eq_or_lt with hqa | hqa
    · have hline : (fun t : ℝ => (q.1,t)) '' Ioo a b ⊆ B ∩ (univ ×ˢ Ioi a) := by
        rintro _ ⟨t,ht,rfl⟩
        exact ⟨hband ⟨mem_univ _,ha.trans ht.1,ht.2⟩,mem_univ _,ht.1⟩
      have hacl : a ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl,hab.le⟩
      have hmem : (q.1,a) ∈ closure ((fun t : ℝ => (q.1,t)) '' Ioo a b) :=
        image_closure_subset_closure_image (continuous_const.prodMk continuous_id) ⟨a,hacl,rfl⟩
      have hqeq : (q.1,a) = q := Prod.ext rfl hqa
      exact hqeq ▸ closure_mono hline hmem
    · have h := (isOpen_univ.prod (isOpen_Ioi (a := a))).inter_closure
        ⟨⟨mem_univ q.1,hqa⟩,hq.1⟩
      simpa only [inter_comm] using h

end DifferentialGeometry.Topology.SphereSeparation
