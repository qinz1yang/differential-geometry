import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

variable {X : Type*} [TopologicalSpace X]

theorem isCompact_closure_moved_trans (H G : X ≃ₜ X)
    (hH : IsCompact (closure {x | H x ≠ x}))
    (hG : IsCompact (closure {x | G x ≠ x})) :
    IsCompact (closure {x | (H.trans G) x ≠ x}) := by
  apply (hH.union hG).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.union isClosed_closure)
  intro x hx
  by_cases hHx : H x = x
  · right
    apply subset_closure
    change G x ≠ x
    change G (H x) ≠ x at hx
    rwa [hHx] at hx
  · exact Or.inl (subset_closure hHx)

theorem exists_engulfing_of_finite_steps {U : Set X} (hU : IsOpen U)
    (A W : ℕ → Set X) (hmono : Monotone A) (hstart : A 0 ⊆ U) (N : ℕ)
    (hstep : ∀ i < N, ∀ V : Set X, IsOpen V → A i ⊆ V →
      ∃ H : X ≃ₜ X, (∀ x ∉ W i, H x = x) ∧ (∀ x ∈ A i, H x = x) ∧
        A (i + 1) ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x})) :
    ∃ H : X ≃ₜ X, (∀ x ∉ ⋃ i < N, W i, H x = x) ∧
      (∀ x ∈ A 0, H x = x) ∧ A N ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  induction N with
  | zero =>
      refine ⟨Homeomorph.refl X, ?_, ?_, ?_, ?_⟩
      · intros; rfl
      · intros; rfl
      · exact fun x hx => ⟨x, hstart hx, rfl⟩
      · simp
  | succ n ih =>
      obtain ⟨H, hfixH, hkeepH, hincH, hcompactH⟩ :=
        ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      obtain ⟨G, hfixG, hkeepG, hincG, hcompactG⟩ :=
        hstep n (Nat.lt_succ_self n) (H '' U) (H.isOpenMap _ hU) hincH
      refine ⟨H.trans G, ?_, ?_, ?_, isCompact_closure_moved_trans H G hcompactH hcompactG⟩
      · intro x hx
        have hxH : x ∉ ⋃ i < n, W i := by
          intro hm
          obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hm
          exact hx (mem_iUnion₂.mpr ⟨i, Nat.lt_succ_of_lt hi, hix⟩)
        have hxG : x ∉ W n :=
          fun hn => hx (mem_iUnion₂.mpr ⟨n, Nat.lt_succ_self n, hn⟩)
        rw [Homeomorph.trans_apply, hfixH x hxH, hfixG x hxG]
      · intro x hx
        rw [Homeomorph.trans_apply, hkeepH x hx, hkeepG x (hmono (Nat.zero_le n) hx)]
      · intro x hx
        obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hincG hx
        exact ⟨z, hz, hy⟩

theorem exists_engulfing_of_finite_steps_supported {U W : Set X} (hU : IsOpen U)
    (A : ℕ → Set X) (hmono : Monotone A) (hstart : A 0 ⊆ U) (N : ℕ)
    (hstep : ∀ i < N, ∀ V : Set X, IsOpen V → A i ⊆ V →
      ∃ H : X ≃ₜ X, (∀ x ∉ W, H x = x) ∧ (∀ x ∈ A i, H x = x) ∧
        A (i + 1) ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x})) :
    ∃ H : X ≃ₜ X, (∀ x ∉ W, H x = x) ∧
      (∀ x ∈ A 0, H x = x) ∧ A N ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨H, hfix, hkeep, hinc, hcompact⟩ :=
    exists_engulfing_of_finite_steps hU A (fun _ => W) hmono hstart N hstep
  refine ⟨H, ?_, hkeep, hinc, hcompact⟩
  intro x hx
  apply hfix x
  intro hm
  obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hm
  exact hx hix

def engulfingStage (A : Set X) (K : ℕ → Set X) (n : ℕ) : Set X :=
  A ∪ ⋃ i < n, K i

omit [TopologicalSpace X] in
@[simp] theorem engulfingStage_zero (A : Set X) (K : ℕ → Set X) :
    engulfingStage A K 0 = A := by
  simp [engulfingStage]

omit [TopologicalSpace X] in
theorem monotone_engulfingStage (A : Set X) (K : ℕ → Set X) :
    Monotone (engulfingStage A K) := by
  intro m n hmn x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨i, hi.trans_le hmn, hix⟩)

omit [TopologicalSpace X] in
theorem engulfingStage_succ (A : Set X) (K : ℕ → Set X) (n : ℕ) :
    engulfingStage A K (n + 1) = engulfingStage A K n ∪ K n := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl (Or.inl hx)
    · obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨i, hlt, hix⟩))
      · exact Or.inr hix
  · rintro (hx | hx)
    · exact monotone_engulfingStage A K (Nat.le_succ n) hx
    · exact Or.inr (mem_iUnion₂.mpr ⟨n, Nat.lt_succ_self n, hx⟩)

theorem isClosed_engulfingStage {A : Set X} {K : ℕ → Set X} (hA : IsClosed A)
    (n : ℕ) (hK : ∀ i < n, IsClosed (K i)) : IsClosed (engulfingStage A K n) := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
      rw [engulfingStage_succ]
      exact (ih (fun i hi => hK i (Nat.lt_succ_of_lt hi))).union (hK n (Nat.lt_succ_self n))

theorem isCompact_engulfingStage {A : Set X} {K : ℕ → Set X} (hA : IsCompact A)
    (n : ℕ) (hK : ∀ i < n, IsCompact (K i)) : IsCompact (engulfingStage A K n) := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
      rw [engulfingStage_succ]
      exact (ih (fun i hi => hK i (Nat.lt_succ_of_lt hi))).union (hK n (Nat.lt_succ_self n))

theorem exists_engulfing_of_finite_attachments {U A : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (K W : ℕ → Set X) (N : ℕ)
    (hstep : ∀ i < N, ∀ V : Set X, IsOpen V → engulfingStage A K i ⊆ V →
      ∃ H : X ≃ₜ X, (∀ x ∉ W i, H x = x) ∧
        (∀ x ∈ engulfingStage A K i, H x = x) ∧
        engulfingStage A K i ∪ K i ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x})) :
    ∃ H : X ≃ₜ X, (∀ x ∉ ⋃ i < N, W i, H x = x) ∧
      (∀ x ∈ A, H x = x) ∧ (A ∪ ⋃ i < N, K i) ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  have hstart : engulfingStage A K 0 ⊆ U := by simpa using hAU
  have hsteps : ∀ i < N, ∀ V : Set X, IsOpen V → engulfingStage A K i ⊆ V →
      ∃ H : X ≃ₜ X, (∀ x ∉ W i, H x = x) ∧
        (∀ x ∈ engulfingStage A K i, H x = x) ∧
        engulfingStage A K (i + 1) ⊆ H '' V ∧ IsCompact (closure {x | H x ≠ x}) := by
    intro i hi V hV hinc
    simpa only [engulfingStage_succ] using hstep i hi V hV hinc
  simpa [engulfingStage] using
    exists_engulfing_of_finite_steps hU (engulfingStage A K) W
      (monotone_engulfingStage A K) hstart N hsteps

end DifferentialGeometry.Topology.Engulfing
