import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

namespace Finsupp

section

variable {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

noncomputable def lcomapDomainOfFiniteFibers (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) : (β →₀ M) →ₗ[R] α →₀ M where
  toFun v := ofSupportFinite (v ∘ p) (v.hasFiniteSupport.preimage' fun b _ => hfin b)
  map_add' v w := by ext a; rfl
  map_smul' r v := by ext a; rfl

@[simp] theorem lcomapDomainOfFiniteFibers_apply (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (v : β →₀ M) (a : α) :
    lcomapDomainOfFiniteFibers (R := R) p hfin v a = v (p a) := rfl

theorem lcomapDomainOfFiniteFibers_eq_lcomapDomain (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (hp : Function.Injective p) :
    lcomapDomainOfFiniteFibers (R := R) (M := M) p hfin = lcomapDomain p hp := by
  ext v a
  rfl

theorem lcomapDomainOfFiniteFibers_injective (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (hp : Function.Surjective p) :
    Function.Injective (lcomapDomainOfFiniteFibers (R := R) (M := M) p hfin) := by
  intro v w h
  ext b
  obtain ⟨a, rfl⟩ := hp b
  exact congrArg (fun z : α →₀ M => z a) h

theorem lcomapDomainOfFiniteFibers_single (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (b : β) (m : M) :
    lcomapDomainOfFiniteFibers (R := R) p hfin (single b m) =
      ∑ a ∈ (hfin b).toFinset, single a m := by
  classical
  ext a
  simp [Finset.sum_apply, single_apply, eq_comm]

theorem mem_range_lcomapDomainOfFiniteFibers_iff (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (v : α →₀ M) :
    v ∈ Set.range (lcomapDomainOfFiniteFibers (R := R) p hfin) ↔
      ∀ a a', p a = p a' → v a = v a' := by
  classical
  constructor
  · rintro ⟨w, rfl⟩ a a' haa'
    simp only [lcomapDomainOfFiniteFibers_apply, haa']
  · intro hv
    let w : β → M := fun b => if h : ∃ a, p a = b then v h.choose else 0
    have hw : (Function.support w).Finite := by
      apply (v.hasFiniteSupport.image p).subset
      intro b hb
      by_cases h : ∃ a, p a = b
      · exact ⟨h.choose, by simpa only [Function.mem_support, w, dif_pos h] using hb,
          h.choose_spec⟩
      · simp [Function.mem_support, w, h] at hb
    refine ⟨ofSupportFinite w hw, ?_⟩
    ext a
    change w (p a) = v a
    dsimp only [w]
    rw [dif_pos ⟨a, rfl⟩]
    exact hv _ a (Exists.choose_spec (show ∃ a', p a' = p a from ⟨a, rfl⟩))

end

section

variable {α β M : Type*} [AddCommMonoid M]

theorem mapDomain_apply_of_fiber_eq_pair (p : α → β) (b : β) (a₁ a₂ : α)
    (hne : a₁ ≠ a₂) (hfiber : ∀ a, p a = b ↔ a = a₁ ∨ a = a₂) (v : α →₀ M) :
    mapDomain p v b = v a₁ + v a₂ := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [mapDomain_add, add_apply, hv, hw]; abel
  | single a m =>
    by_cases h₁ : a = a₁
    · subst a
      simp [mapDomain_single, (hfiber a₁).2 (Or.inl rfl), hne.symm]
    · by_cases h₂ : a = a₂
      · subst a
        simp [mapDomain_single, (hfiber a₂).2 (Or.inr rfl), hne]
      · have hp : p a ≠ b := by simp [hfiber, h₁, h₂]
        simp [mapDomain_single, hp, h₁, h₂]

end

private theorem fiber_pair {α β : Type*} (p : α → β) (b : β)
    (hcard : Nat.card (p ⁻¹' {b}) = 2) :
    ∃ a₁ a₂, a₁ ≠ a₂ ∧ ∀ a, p a = b ↔ a = a₁ ∨ a = a₂ := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  refine ⟨x.val, y.val, fun h => hxy (Subtype.ext h), ?_⟩
  intro a
  constructor
  · intro ha
    have hmem : (⟨a, ha⟩ : p ⁻¹' {b}) ∈ ({x, y} : Set (p ⁻¹' {b})) := by
      rw [huniv]
      trivial
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff] using hmem
  · rintro (rfl | rfl)
    · exact x.property
    · exact y.property

private theorem module_add_self {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (m : M) : m + m = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

variable {α β M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]

theorem mapDomain_eq_zero_iff_of_card_fiber_eq_two (p : α → β)
    (hcard : ∀ b, Nat.card (p ⁻¹' {b}) = 2) (v : α →₀ M) :
    mapDomain p v = 0 ↔ ∀ a a', p a = p a' → v a = v a' := by
  constructor
  · intro hv a a' haa'
    obtain ⟨a₁, a₂, hne, hfiber⟩ := fiber_pair p (p a) (hcard (p a))
    have hsum : v a₁ + v a₂ = 0 := by
      rw [← mapDomain_apply_of_fiber_eq_pair p (p a) a₁ a₂ hne hfiber v, hv]
      rfl
    have heq : v a₁ = v a₂ := by
      calc
        v a₁ = v a₁ + (v a₂ + v a₂) := by rw [module_add_self, add_zero]
        _ = (v a₁ + v a₂) + v a₂ := (add_assoc _ _ _).symm
        _ = v a₂ := by rw [hsum, zero_add]
    rcases (hfiber a).mp rfl with h | h <;>
      rcases (hfiber a').mp haa'.symm with h' | h' <;> simp_all
  · intro hv
    ext b
    obtain ⟨a₁, a₂, hne, hfiber⟩ := fiber_pair p b (hcard b)
    rw [mapDomain_apply_of_fiber_eq_pair p b a₁ a₂ hne hfiber v]
    rw [hv a₁ a₂ ((hfiber a₁).mpr (Or.inl rfl) |>.trans
      ((hfiber a₂).mpr (Or.inr rfl)).symm)]
    exact module_add_self _

theorem exact_lcomapDomainOfFiniteFibers_lmapDomain_of_card_fiber_eq_two (p : α → β)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) (hcard : ∀ b, Nat.card (p ⁻¹' {b}) = 2) :
    Function.Exact (lcomapDomainOfFiniteFibers (R := ZMod 2) (M := M) p hfin)
      (lmapDomain M (ZMod 2) p) := by
  intro v
  exact (mapDomain_eq_zero_iff_of_card_fiber_eq_two p hcard v).trans
    (mem_range_lcomapDomainOfFiniteFibers_iff p hfin v).symm

end Finsupp
