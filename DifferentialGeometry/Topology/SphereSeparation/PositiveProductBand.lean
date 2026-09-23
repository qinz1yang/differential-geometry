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

end DifferentialGeometry.Topology.SphereSeparation
