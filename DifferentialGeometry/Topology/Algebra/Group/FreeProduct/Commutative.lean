import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FiniteFreeFactors
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct
set_option autoImplicit false
noncomputable section
universe u v w
namespace GC.Group
open Monoid.CoprodI

theorem coprodI_noncommuting_letters {ι : Type u} (M : ι → Type v)
    [∀ i, Monoid (M i)] {i j : ι} (hij : i ≠ j)
    (a : M i) (ha : a ≠ 1) (b : M j) (hb : b ≠ 1) :
    of a * of b ≠ of b * of a := by
  classical
  let wa := Word.cons a (Word.cons b Word.empty (by simp [Word.fstIdx, Word.empty]) hb)
    (by change some j ≠ some i; exact fun h => hij (Option.some.inj h).symm) ha
  let wb := Word.cons b (Word.cons a Word.empty (by simp [Word.fstIdx, Word.empty]) ha)
    (by change some i ≠ some j; exact fun h => hij (Option.some.inj h)) hb
  intro h
  have hp : wa.prod = wb.prod := by
    change of a * (of b * 1) = of b * (of a * 1)
    simpa only [mul_one] using h
  have hw : wa = wb := (Word.equiv (M := M)).symm.injective hp
  have hi := congrArg Word.fstIdx hw
  change (some i : Option ι) = some j at hi
  exact hij (Option.some.inj hi)

theorem subsingleton_factor_of_commutative_coprod (G : Type u) (H : Type v)
    [Group G] [Group H]
    (hc : ∀ x y : Monoid.Coprod G H, x * y = y * x) :
    Subsingleton G ∨ Subsingleton H := by
  classical
  by_contra h
  have hG : ¬ Subsingleton G := fun hs => h (Or.inl hs)
  have hH : ¬ Subsingleton H := fun hs => h (Or.inr hs)
  let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hG
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨b, hb⟩ := exists_ne (1 : H)
  let M := DifferentialGeometry.Algebra.Group.boolCoprodFamily G H
  let e := DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod G H
  apply coprodI_noncommuting_letters M Bool.false_ne_true
    (ULift.up a) (fun h => ha (congrArg ULift.down h))
    (ULift.up b) (fun h => hb (congrArg ULift.down h))
  apply e.injective
  simpa only [map_mul] using hc (e (of (i := false) (ULift.up a)))
    (e (of (i := true) (ULift.up b)))

theorem commutative_freelyIndecomposable (G : Type u) [Group G]
    (hc : ∀ x y : G, x * y = y * x) : FreelyIndecomposable G := by
  intro A B _ _ he
  obtain ⟨e⟩ := he
  apply subsingleton_factor_of_commutative_coprod A B
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using hc (e.symm x) (e.symm y)

end GC.Group
