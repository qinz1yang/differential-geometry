import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace DifferentialGeometry.Topology.Flow

theorem exists_minimal_pos_period
    {X : Type*} [TopologicalSpace X] [T2Space X] (φ : _root_.Flow ℝ X) {x : X}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ T > 0, Function.Periodic (fun t ↦ φ t x) T ∧
      InjOn (fun t ↦ φ t x) (Ico 0 T) ∧ ∀ t > 0, φ t x = x → T ≤ t := by
  let S : AddSubgroup ℝ := {
    carrier := {t | φ t x = x}
    zero_mem' := φ.map_zero_apply x
    add_mem' := by
      intro s t hs ht
      change φ (s + t) x = x
      rw [φ.map_add, ht, hs]
    neg_mem' := by
      intro t ht
      have he := congrArg (φ (-t)) ht
      rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply] at he
      exact he.symm }
  have hclosed : IsClosed (S : Set ℝ) :=
    isClosed_eq (φ.continuous continuous_id continuous_const) continuous_const
  have hnotdense : ¬ Dense (S : Set ℝ) := by
    intro hdense
    obtain ⟨s, hs⟩ := hnon
    have he : (S : Set ℝ) = univ := hclosed.closure_eq.symm.trans hdense.closure_eq
    apply hs
    change s ∈ (S : Set ℝ)
    rw [he]
    exact mem_univ s
  have hbot : S ≠ ⊥ := by
    intro he
    obtain ⟨t, ht, hret⟩ := hreturn
    have hmem : t ∈ S := hret
    rw [he, AddSubgroup.mem_bot] at hmem
    exact ht.ne' hmem
  obtain ⟨T, hT⟩ : ∃ T, IsLeast {t : ℝ | t ∈ S ∧ 0 < t} T := by
    by_contra h
    exact hnotdense (S.dense_of_no_min hbot h)
  have hperiodic : Function.Periodic (fun t ↦ φ t x) T := by
    intro t
    change φ (t + T) x = φ t x
    rw [φ.map_add, show φ T x = x from hT.1.1]
  have horder (s t : ℝ) (hs : s ∈ Ico 0 T) (ht : t ∈ Ico 0 T)
      (hst : s < t) (he : φ s x = φ t x) : False := by
    have hret : t - s ∈ S := by
      change φ (t - s) x = x
      calc
        φ (t - s) x = φ (-s) (φ t x) := by rw [← φ.map_add]; congr 1; ring
        _ = φ (-s) (φ s x) := congrArg (φ (-s)) he.symm
        _ = x := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
    have hmin := hT.2 ⟨hret, sub_pos.mpr hst⟩
    linarith [hs.1, ht.2]
  refine ⟨T, hT.1.2, hperiodic, ?_, fun t ht hret ↦ hT.2 ⟨hret, ht⟩⟩
  intro s hs t ht he
  rcases lt_trichotomy s t with h | h | h
  · exact (horder s t hs ht h he).elim
  · exact h
  · exact (horder t s ht hs h he.symm).elim

theorem exists_simple_closed_curve_of_periodic_orbit
    {X : Type*} [TopologicalSpace X] [T2Space X] (φ : _root_.Flow ℝ X) {x : X}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = γ 1 ∧ InjOn γ (Ico 0 1) ∧
      γ '' Icc 0 1 = φ.orbit x := by
  obtain ⟨T, hT, hper, hinj, _⟩ :=
    exists_minimal_pos_period φ hnon hreturn
  let γ : ℝ → X := fun t ↦ φ (T * t) x
  have hγ : Continuous γ := φ.continuous (continuous_const.mul continuous_id) continuous_const
  have hclose : γ 0 = γ 1 := by
    simpa only [γ, mul_zero, mul_one, zero_add] using (hper 0).symm
  have hsimple : InjOn γ (Ico 0 1) := by
    intro s hs t ht he
    have hm (r : ℝ) (hr : r ∈ Ico 0 1) : T * r ∈ Ico 0 T :=
      ⟨mul_nonneg hT.le hr.1, by nlinarith [hr.2]⟩
    exact mul_left_cancel₀ hT.ne' (hinj (hm s hs) (hm t ht) he)
  have himage : γ '' Icc 0 1 = φ.orbit x := by
    apply Subset.antisymm
    · rintro z ⟨t, _, rfl⟩
      exact φ.mem_orbit x (T * t)
    · rintro z ⟨s, rfl⟩
      obtain ⟨r, hr, he⟩ := hper.exists_mem_Ico₀ hT s
      refine ⟨r / T, ⟨div_nonneg hr.1 hT.le, (div_le_one hT).mpr hr.2.le⟩, ?_⟩
      change φ (T * (r / T)) x = φ s x
      have hcancel : T * (r / T) = r := by field_simp
      rw [hcancel]
      exact he.symm
  exact ⟨γ, hγ, hclose, hsimple, himage⟩

end DifferentialGeometry.Topology.Flow
