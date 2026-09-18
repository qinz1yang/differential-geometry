import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Finset

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_max (r : LinearOrder E) {t : Finset E} {m : E}
    (hm : ∀ x ∈ t, r.lt x m) :
    incidenceIndex r (insert m t) m = t.card := by
  let _ := r
  classical
  have h : (insert m t).filter (fun w => w < m) = t := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hlt⟩
      · exact absurd (hw ▸ hlt) (lt_irrefl m)
      · exact hw
    · exact fun hw => ⟨Or.inr hw, hm w hw⟩
  change ((insert m t).filter (fun w => w < m)).card = t.card
  rw [h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem incidenceIndex_insert_of_lt (r : LinearOrder E) {t : Finset E} {m v : E}
    (hm : ∀ x ∈ t, r.lt x m) (hv : v ∈ t) :
    incidenceIndex r (insert m t) v = incidenceIndex r t v := by
  let _ := r
  classical
  have h : (insert m t).filter (fun w => w < v) = t.filter (fun w => w < v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hlt⟩
      · exact absurd (lt_trans (hw ▸ hlt) (hm v hv)) (lt_irrefl m)
      · exact ⟨hw, hlt⟩
    · rintro ⟨hw, hlt⟩
      exact ⟨Or.inr hw, hlt⟩
  change ((insert m t).filter (fun w => w < v)).card = (t.filter (fun w => w < v)).card
  rw [h]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem prod_incidenceSign (r : LinearOrder E) (s : Finset E) :
    ∏ v ∈ s, incidenceSign r s v = (-1 : ℤ) ^ s.card.choose 2 := by
  let _ := r
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert m t hm ih =>
      have hmt : m ∉ t := fun h => lt_irrefl m (hm m h)
      rw [Finset.prod_insert hmt, incidenceSign, incidenceIndex_max r hm]
      have hrest : ∏ v ∈ t, incidenceSign r (insert m t) v = ∏ v ∈ t, incidenceSign r t v :=
        Finset.prod_congr rfl fun v hv => by
          rw [incidenceSign, incidenceSign, incidenceIndex_insert_of_lt r hm hv]
      rw [hrest, ih, Finset.card_insert_of_notMem hmt, ← pow_add, Nat.choose_succ_succ,
        Nat.choose_one_right]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem prod_incidenceSign_triple (r : LinearOrder E) {a b c : E} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    incidenceSign r ({a, b, c} : Finset E) a * incidenceSign r ({a, b, c} : Finset E) b *
        incidenceSign r ({a, b, c} : Finset E) c = -1 := by
  let _ := r
  classical
  have hcard : ({a, b, c} : Finset E).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hprod := prod_incidenceSign r ({a, b, c} : Finset E)
  rw [hcard] at hprod
  rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
    Finset.prod_singleton] at hprod
  rw [mul_assoc, hprod]
  norm_num

end DifferentialGeometry.Topology.PiecewiseLinear
