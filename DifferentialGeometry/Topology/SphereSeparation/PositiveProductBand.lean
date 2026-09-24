import DifferentialGeometry.Topology.SphereSeparation.ComplementPair
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.Topology.SphereSeparation

theorem ComplementPair.lower_band_subset_left_of_separator_above
    {A : Type*} [TopologicalSpace A] [ConnectedSpace A]
    {S : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))} (p : ComplementPair S)
    {a r : ℝ} (ha : 0 < a)
    (hlow : ∀ q : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)), q.val.2 < a → q ∈ p.left)
    (hS : ∀ q ∈ S, r < q.val.2) :
    ∀ q : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)), q.val.2 ≤ r → q ∈ p.left := by
  intro q hq
  let C : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) := {z | z.val.2 ≤ r}
  have hC : IsPreconnected C := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have him : (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ) '' C =
        univ ×ˢ Ioc (0 : ℝ) r := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨mem_univ _,w.property.2,hw⟩
      · intro hz
        exact ⟨⟨z,hz.1,hz.2.1⟩,hz.2.2,rfl⟩
    rw [him]
    exact isPreconnected_univ.prod isPreconnected_Ioc
  have hCS : C ⊆ Sᶜ := by
    intro z hz hs
    exact (not_lt_of_ge hz) (hS z hs)
  let t := min a q.val.2 / 2
  have ht : 0 < t := div_pos (lt_min ha q.property.2) (by norm_num)
  have hta : t < a := by dsimp [t]; linarith [min_le_left a q.val.2]
  have htq : t ≤ q.val.2 := by dsimp [t]; linarith [min_le_right a q.val.2,show 0 < q.val.2 from q.property.2]
  let z : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) := ⟨(q.val.1,t),mem_univ _,ht⟩
  have hzC : z ∈ C := htq.trans hq
  have hzL : z ∈ p.left := hlow z hta
  rcases p.subset_left_or_subset_right hC hCS with h | h
  · exact h hq
  · exact False.elim (p.disjoint.le_bot ⟨hzL,h hzC⟩)


private theorem vertical_band_image
    {A : Type*} (x : A) (a : ℝ) :
    (Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ) '' {q | q.val.1 = x ∧ q.val.2 < a} =
      {x} ×ˢ Ioo (0 : ℝ) a := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, q.property.2, hq.2⟩
  · intro hz
    exact ⟨⟨z, mem_univ _, hz.2.1⟩, ⟨hz.1, hz.2.2⟩, rfl⟩

private theorem image_vertical_band_subset_left
    {A : Type*} [TopologicalSpace A]
    {S : Set ((univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)))} (p : ComplementPair S)
    (f : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) (hf : Continuous f)
    (hfinj : Function.Injective f)
    {a r b : ℝ} (ha : 0 < a) (hr : 0 < r) (hb : 0 < b)
    (hfix : ∀ q, q.val.2 ≤ r → f q = q)
    (hlow : ∀ q, q.val.2 < b → q ∈ p.left)
    (hseparator : S ⊆ f '' {q | q.val.2 = a}) (x : A) :
    f '' {q | q.val.1 = x ∧ q.val.2 < a} ⊆ p.left := by
  let C : Set ((univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) := {q | q.val.1 = x ∧ q.val.2 < a}
  have hC : IsPreconnected C := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [vertical_band_image x a]
    exact isPreconnected_singleton.prod isPreconnected_Ioo
  have hCcomp : f '' C ⊆ Sᶜ := by
    rintro z ⟨q, hq, rfl⟩ hz
    obtain ⟨q', hq'a, hfq'⟩ := hseparator hz
    have hqq' : q' = q := hfinj hfq'
    subst q'
    exact (show q.val.2 < a from hq.2).ne hq'a
  let t := min a (min r b) / 2
  have ht : 0 < t := div_pos (lt_min ha (lt_min hr hb)) (by norm_num)
  have hta : t < a := by dsimp [t] at *; linarith [min_le_left a (min r b)]
  have htr : t < r := by
    have hmin : min a (min r b) ≤ r := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [t] at *
    linarith
  have htb : t < b := by
    have hmin : min a (min r b) ≤ b := (min_le_right _ _).trans (min_le_right _ _)
    dsimp [t] at *
    linarith
  let z : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) := ⟨(x, t), mem_univ _, ht⟩
  have hzC : z ∈ C := ⟨rfl, hta⟩
  have hFzleft : f z ∈ p.left := by rw [hfix z htr.le]; exact hlow z htb
  rcases p.subset_left_or_subset_right (hC.image f hf.continuousOn) hCcomp with h | h
  · exact h
  · exact fun _ _ => False.elim (p.disjoint.le_bot ⟨hFzleft, h ⟨z, hzC, rfl⟩⟩)

theorem ComplementPair.image_lower_band_subset_left
    {A : Type*} [TopologicalSpace A]
    {S : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))} (p : ComplementPair S)
    (f : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) →
      (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) (hf : Continuous f)
    (hfinj : Function.Injective f)
    {a r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfix : ∀ q, q.val.2 ≤ r → f q = q)
    (hlow : ∀ q, q.val.2 < b → q ∈ p.left)
    (hseparator : S ⊆ f '' {q | q.val.2 = a}) :
    ∀ q, q.val.2 < a → f q ∈ p.left := by
  intro q hqa
  exact image_vertical_band_subset_left p f hf hfinj
    (q.property.2.trans hqa) hr hb hfix hlow hseparator q.val.1 ⟨q, ⟨rfl, hqa⟩, rfl⟩

theorem ComplementPair.image_lower_band_subset_closure_left
    {A : Type*} [TopologicalSpace A]
    {S : Set (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))} (p : ComplementPair S)
    (f : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) →
      (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) (hf : Continuous f)
    (hfinj : Function.Injective f)
    {a r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfix : ∀ q, q.val.2 ≤ r → f q = q)
    (hlow : ∀ q, q.val.2 < b → q ∈ p.left)
    (hseparator : S ⊆ f '' {q | q.val.2 = a}) :
    ∀ q, q.val.2 ≤ a → f q ∈ closure p.left := by
  intro q hqa
  have ha : 0 < a := q.property.2.trans_le hqa
  let C : Set ((univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ))) := {z | z.val.1 = q.val.1 ∧ z.val.2 < a}
  have hsub : f '' C ⊆ p.left :=
    image_vertical_band_subset_left p f hf hfinj ha hr hb hfix hlow hseparator q.val.1
  have hqC : q ∈ closure C := by
    rw [_root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change q.val ∈ closure ((Subtype.val : (univ ×ˢ Ioi (0 : ℝ) : Set (A × ℝ)) → A × ℝ) '' C)
    rw [vertical_band_image q.val.1 a, closure_prod_eq, closure_Ioo ha.ne]
    exact ⟨subset_closure (mem_singleton _), q.property.2.le, hqa⟩
  exact closure_mono hsub (image_closure_subset_closure_image hf ⟨q, hqC, rfl⟩)

end DifferentialGeometry.Topology.SphereSeparation
