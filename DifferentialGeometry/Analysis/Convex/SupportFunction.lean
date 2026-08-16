import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Convex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def supportFunction (C : Set F) (v : F) : ℝ :=
  sSup {x : ℝ | ∃ c : F, c ∈ C ∧ x = inner ℝ v c}

def finiteSupportDirections (C : Set F) : Set F :=
  {v : F | BddAbove {x : ℝ | ∃ c : F, c ∈ C ∧ x = inner ℝ v c}}

omit [CompleteSpace F] in
theorem supportFunction_le_of_mem {C : Set F} {v c : F}
    (hv : v ∈ finiteSupportDirections C) (hc : c ∈ C) :
    inner ℝ v c ≤ supportFunction C v := by
  unfold supportFunction
  exact le_csSup hv ⟨c, hc, rfl⟩

omit [CompleteSpace F] in
theorem mem_finiteSupportDirections_of_normal
    {C : Set F} {v p : F}
    (hnormal : ∀ q : F, q ∈ C → inner ℝ v (q - p) ≤ 0) :
    v ∈ finiteSupportDirections C := by
  unfold finiteSupportDirections
  refine ⟨inner ℝ v p, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  have hqle : inner ℝ v q - inner ℝ v p ≤ 0 := by
    have h := hnormal q hq
    rw [show inner ℝ v (q - p) = inner ℝ v q - inner ℝ v p by
      rw [inner_sub_right]] at h
    exact h
  linarith

theorem mem_of_forall_support_le
    {C : Set F} {p : F}
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCconvex : Convex ℝ C)
    (hp : ∀ v : F, v ∈ finiteSupportDirections C → inner ℝ v p ≤ supportFunction C v) :
    p ∈ C := by
  by_contra hnot
  obtain ⟨q, hqC, hqmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hCne hCclosed.isComplete hCconvex p
  let v : F := p - q
  have hnormal : ∀ c ∈ C, inner ℝ v (c - q) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hCconvex hqC).mp hqmin
  have hbdd : BddAbove {x : ℝ | ∃ c : F, c ∈ C ∧ x = inner ℝ v c} := by
    refine ⟨inner ℝ v q, ?_⟩
    rintro x ⟨c, hc, rfl⟩
    have hqle : inner ℝ v c - inner ℝ v q ≤ 0 := by
      have h := hnormal c hc
      rw [show inner ℝ v (c - q) = inner ℝ v c - inner ℝ v q by
        rw [inner_sub_right]] at h
      exact h
    linarith
  have hv : v ∈ finiteSupportDirections C := hbdd
  have hle := hp v hv
  have hsup_le : supportFunction C v ≤ inner ℝ v q := by
    unfold supportFunction
    refine csSup_le ?_ ?_
    · rcases hCne with ⟨w, hw⟩
      refine ⟨inner ℝ v w, ?_⟩
      exact ⟨w, hw, rfl⟩
    · rintro x ⟨c, hc, rfl⟩
      have hqle : inner ℝ v c - inner ℝ v q ≤ 0 := by
        have h := hnormal c hc
        rw [show inner ℝ v (c - q) = inner ℝ v c - inner ℝ v q by
          rw [inner_sub_right]] at h
        exact h
      linarith
  have hmain : inner ℝ v p ≤ inner ℝ v q := le_trans hle hsup_le
  have hgt : inner ℝ v q < inner ℝ v p := by
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro hpq
      have : p ∈ C := by simpa [hpq] using hqC
      exact hnot this))
    have hval : inner ℝ v p - inner ℝ v q = ‖v‖ ^ 2 := by
      rw [← inner_sub_right]
      rw [show p - q = v from rfl, real_inner_self_eq_norm_sq]
    nlinarith [hpos]
  exact (not_lt_of_ge hmain) hgt

theorem mem_iff_support_le
    {C : Set F} {p : F}
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCconvex : Convex ℝ C) :
    p ∈ C ↔ ∀ v : F, v ∈ finiteSupportDirections C → inner ℝ v p ≤ supportFunction C v := by
  constructor
  · intro hp v hv
    exact supportFunction_le_of_mem hv hp
  · exact mem_of_forall_support_le hCclosed hCne hCconvex

end DifferentialGeometry.Analysis.Convex

end
