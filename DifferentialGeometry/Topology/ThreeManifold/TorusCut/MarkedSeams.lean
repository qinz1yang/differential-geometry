import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Card

namespace GC.Topology
universe u v w

theorem finite_tagged_indices {I : Type u} {J : I → Type v}
    [Finite I] [∀ i, Finite (J i)] : Finite (Sigma J) := inferInstance

def reindex {I I' : Type u} {J : I → Type v} {J' : I' → Type v}
    (e : I ≃ I') (f : ∀ i, J i ≃ J' (e i)) : Sigma J ≃ Sigma J' :=
  Equiv.sigmaCongr e f

theorem reindex_payload {I I' : Type u} {J : I → Type v} {J' : I' → Type v}
    (e : I ≃ I') (f : ∀ i, J i ≃ J' (e i))
    {A : Type w} (payload : Sigma J → A) (x : Sigma J) :
    payload ((reindex e f).symm (reindex e f x)) = payload x := by simp

structure PairedSides (S : Type u) where
  mate : S → S
  involutive : Function.Involutive mate
  no_fixed : ∀ s, mate s ≠ s

namespace PairedSides
variable {S : Type u} (P : PairedSides S)

def sideSetoid : Setoid S where
  r s t := s = t ∨ P.mate s = t
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro s t h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [← h, P.involutive])
    trans := by
      intro s t u h k
      rcases h with h | h
      · simpa [h] using k
      · rcases k with k | k
        · exact Or.inr (h.trans k)
        · exact Or.inl (by rw [← k, ← h, P.involutive]) }

abbrev Seam := Quotient P.sideSetoid

def seam (s : S) : P.Seam := Quotient.mk P.sideSetoid s

instance [Finite S] : Finite P.Seam := inferInstance

theorem seam_eq_iff (s t : S) : P.seam s = P.seam t ↔ s = t ∨ P.mate s = t :=
  Quotient.eq

theorem seam_mate (s : S) : P.seam (P.mate s) = P.seam s :=
  (P.seam_eq_iff _ _).2 (Or.inr (P.involutive s))

theorem seam_fiber (s : S) : {t | P.seam t = P.seam s} = {s, P.mate s} := by
  ext t
  rw [Set.mem_ofPred_eq, P.seam_eq_iff]
  constructor
  · rintro (h | h)
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · have ht : t = P.mate s := by rw [← h, P.involutive]
      simp [ht]
  · intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [Set.mem_singleton_iff.mp h, P.involutive])

theorem seam_pair_card [DecidableEq S] (s : S) :
    ({s, P.mate s} : Finset S).card = 2 :=
  Finset.card_pair ((P.no_fixed s).symm)

theorem paired_range {T : Type v} {A : Type w}
    (e : S → T → A) (φ : S → T ≃ T)
    (commute : ∀ s x, e (P.mate s) (φ s x) = e s x) (s : S) :
    Set.range (e (P.mate s)) = Set.range (e s) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(φ s).symm x, ?_⟩
    simpa using (commute s ((φ s).symm x)).symm
  · rintro ⟨x, rfl⟩
    exact ⟨φ s x, commute s x⟩

def seamImage {T : Type v} {A : Type w}
    (e : S → T → A) (φ : S → T ≃ T)
    (commute : ∀ s x, e (P.mate s) (φ s x) = e s x) : P.Seam → Set A :=
  Quotient.lift (fun s => Set.range (e s)) (by
    intro s t h
    rcases h with h | h
    · exact congrArg (fun s => Set.range (e s)) h
    · rw [← h, P.paired_range e φ commute])

theorem seamImage_side {T : Type v} {A : Type w}
    (e : S → T → A) (φ : S → T ≃ T)
    (commute : ∀ s x, e (P.mate s) (φ s x) = e s x) (s : S) :
    P.seamImage e φ commute (P.seam s) = Set.range (e s) := rfl
end PairedSides
end GC.Topology
