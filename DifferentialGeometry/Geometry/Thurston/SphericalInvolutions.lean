import DifferentialGeometry.Geometry.Thurston.OrthogonalCyclicPlane
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
A finite free spherical action has a unique involution, necessarily antipodal. Even cardinality
forces this central antipodal element, and a Klein four group cannot embed in the actual action.
These restrictions use the actual free sphere action rather than a classification premise.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology

namespace GC.Geometry.SphericalCyclic

theorem spherical_involution_unique (G : SphericalSpaceFormGroup) (γ δ : G.group)
    (hγ : γ ≠ 1) (hγ2 : γ ^ 2 = 1) (hδ : δ ≠ 1) (hδ2 : δ ^ 2 = 1) : γ = δ := by
  apply Subtype.ext
  exact (free_involution_eq_neg G γ hγ hγ2).trans
    (free_involution_eq_neg G δ hδ hδ2).symm

theorem sphericalAntipodal_mem_of_even (G : SphericalSpaceFormGroup)
    (hcard : Even (Nat.card G.group)) : LinearIsometryEquiv.neg ℝ ∈ G.group := by
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hcard)
  have hn : γ ≠ 1 := by
    intro he
    simp only [he, orderOf_one] at hγ
    norm_num at hγ
  have hpow : γ ^ 2 = 1 := by
    rw [← hγ]
    exact pow_orderOf_eq_one γ
  rw [← free_involution_eq_neg G γ hn hpow]
  exact γ.property

theorem spherical_involution_central (G : SphericalSpaceFormGroup) (γ : G.group)
    (hγ : γ ≠ 1) (hγ2 : γ ^ 2 = 1) : γ ∈ Subgroup.center G.group := by
  rw [Subgroup.mem_center_iff]
  intro δ
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  change δ.val (γ.val x) = γ.val (δ.val x)
  rw [free_involution_eq_neg G γ hγ hγ2]
  exact map_neg δ.val x

theorem spherical_no_klein_embedding (G : SphericalSpaceFormGroup) :
    ¬ ∃ f : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* G.group,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  let a : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)
  let b : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)
  have ha : a ≠ 1 := by decide
  have hb : b ≠ 1 := by decide
  have hab : a ≠ b := by decide
  have ha2 : a ^ 2 = 1 := by decide
  have hb2 : b ^ 2 = 1 := by decide
  have hfa : f a ≠ 1 := by
    intro h
    exact ha (hf (h.trans f.map_one.symm))
  have hfb : f b ≠ 1 := by
    intro h
    exact hb (hf (h.trans f.map_one.symm))
  have hfa2 : (f a) ^ 2 = 1 := by rw [← f.map_pow, ha2, f.map_one]
  have hfb2 : (f b) ^ 2 = 1 := by rw [← f.map_pow, hb2, f.map_one]
  exact hab (hf (spherical_involution_unique G (f a) (f b) hfa hfa2 hfb hfb2))

end GC.Geometry.SphericalCyclic
