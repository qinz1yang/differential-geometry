import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.SetTheory.Cardinal.Finite

namespace Nat

theorem card_le_card_quot_add_card
    {V I : Type*} [Finite V] [Finite I] (a b : I → V) :
    Nat.card V ≤
      Nat.card (Quot (fun u v : V => ∃ i, u = a i ∧ v = b i)) + Nat.card I := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite I
  let r : V → V → Prop := fun u v => ∃ i, u = a i ∧ v = b i
  let _ := Fintype.ofFinite (Quot r)
  let d : (V → ℚ) →ₗ[ℚ] (I → ℚ) :=
    LinearMap.pi fun i =>
      (LinearMap.proj (R := ℚ) (φ := fun _ : V => ℚ) (a i)) -
        (LinearMap.proj (R := ℚ) (φ := fun _ : V => ℚ) (b i))
  have hd (f : LinearMap.ker d) (i : I) : f.val (a i) = f.val (b i) := by
    have hz := congrFun (LinearMap.mem_ker.mp f.property) i
    change f.val (a i) - f.val (b i) = 0 at hz
    exact sub_eq_zero.mp hz
  let L : LinearMap.ker d →ₗ[ℚ] (Quot r → ℚ) :=
    { toFun := fun f => Quot.lift f.val (by
        rintro x y ⟨i, rfl, rfl⟩
        exact hd f i)
      map_add' := by
        intro f g
        funext q
        refine Quot.induction_on q ?_
        intro x
        rfl
      map_smul' := by
        intro c f
        funext q
        refine Quot.induction_on q ?_
        intro x
        rfl }
  have hL : Function.Injective L := by
    intro f g h
    apply Subtype.ext
    funext x
    exact congrFun h (Quot.mk r x)
  have hker : Module.finrank ℚ (LinearMap.ker d) ≤ Nat.card (Quot r) := by
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using
      LinearMap.finrank_le_finrank_of_injective hL
  have hrange : Module.finrank ℚ (LinearMap.range d) ≤ Nat.card I := by
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using
      LinearMap.finrank_le_finrank_of_injective (LinearMap.range d).injective_subtype
  calc
    Nat.card V = Module.finrank ℚ (V → ℚ) := by
      simp only [Module.finrank_pi, Nat.card_eq_fintype_card]
    _ = Module.finrank ℚ (LinearMap.range d) + Module.finrank ℚ (LinearMap.ker d) :=
      d.finrank_range_add_finrank_ker.symm
    _ ≤ Nat.card I + Nat.card (Quot r) := add_le_add hrange hker
    _ = Nat.card (Quot (fun u v : V => ∃ i, u = a i ∧ v = b i)) + Nat.card I :=
      Nat.add_comm _ _

end Nat
