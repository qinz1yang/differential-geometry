import DifferentialGeometry.Topology.Double.Basic

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace DifferentialGeometry.Topology
variable {X : Type*} [TopologicalSpace X]


theorem double_cases (B : Set X) (z : Double B) :
    (∃ x, doublePositive B x = z) ∨ ∃ x, doubleNegative B x = z := by
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr x => exact Or.inr ⟨x, rfl⟩


theorem double_positive_eq_negative_iff (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hz : ∀ x, r x = 0 → x ∈ B) (x y : X) :
    doublePositive B x = doubleNegative B y ↔ x = y ∧ x ∈ B := by
  constructor
  · intro h
    have hxy : x = y := congrArg (doubleFold B) h
    have hh : r x = -r y := congrArg (doubleHeight B r hr) h
    refine ⟨hxy, hz x ?_⟩
    rw [← hxy] at hh
    linarith
  · rintro ⟨rfl, hx⟩
    exact double_seam B ⟨x, hx⟩


theorem double_copies_cover (B : Set X) :
    range (doublePositive B) ∪ range (doubleNegative B) = univ := by
  exact eq_univ_of_forall (double_cases B)


theorem abs_doubleHeight (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x) (z : Double B) :
    |doubleHeight B r hr z| = r (doubleFold B z) := by
  rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact abs_of_nonneg (hn x)
  · exact (abs_neg _).trans (abs_of_nonneg (hn x))


theorem range_doublePositive (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x)
    (hz : ∀ x, r x = 0 → x ∈ B) :
    range (doublePositive B) = {z | 0 ≤ doubleHeight B r hr z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact hn x
  · intro h
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨x, rfl⟩
    · have hx : r x = 0 := by change 0 ≤ -r x at h; linarith [hn x]
      exact ⟨x, double_seam B ⟨x, hz x hx⟩⟩


theorem range_doubleNegative (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x)
    (hz : ∀ x, r x = 0 → x ∈ B) :
    range (doubleNegative B) = {z | doubleHeight B r hr z ≤ 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact neg_nonpos.mpr (hn x)
  · intro h
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have hx : r x = 0 := le_antisymm h (hn x)
      exact ⟨x, (double_seam B ⟨x, hz x hx⟩).symm⟩
    · exact ⟨x, rfl⟩


theorem isClosedEmbedding_doublePositive [CompactSpace X] [T2Space X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) : IsClosedEmbedding (doublePositive B) := by
  let _ : T2Space (Double B) := t2Space_double B r hr hz
  exact (doublePositive B).continuous.isClosedEmbedding (isEmbedding_doublePositive B).injective


theorem isClosedEmbedding_doubleNegative [CompactSpace X] [T2Space X]
    (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) : IsClosedEmbedding (doubleNegative B) := by
  let _ : T2Space (Double B) := t2Space_double B r hr hz
  exact (doubleNegative B).continuous.isClosedEmbedding (isEmbedding_doubleNegative B).injective


theorem range_doubleRealization (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x) :
    range (doubleRealization B r hr) = {q : X × ℝ | |q.2| = r q.1} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact abs_doubleHeight B r hr hn z
  · intro hq
    by_cases ht : 0 ≤ q.2
    · refine ⟨doublePositive B q.1, Prod.ext rfl ?_⟩
      change r q.1 = q.2
      exact ((abs_of_nonneg ht).symm.trans hq).symm
    · refine ⟨doubleNegative B q.1, Prod.ext rfl ?_⟩
      change -r q.1 = q.2
      have hh := (abs_of_neg (lt_of_not_ge ht)).symm.trans hq
      linarith

end DifferentialGeometry.Topology
