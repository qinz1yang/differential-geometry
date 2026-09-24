import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

namespace DifferentialGeometry.Algebra.Module

universe u

variable {A : Type u} [AddCommGroup A] [Module ℤ A]

theorem nonempty_linearEquiv_int_of_bijective_toSpanSingleton {c : A}
    (h : Function.Bijective (LinearMap.toSpanSingleton ℤ A c)) :
    Nonempty (A ≃ₗ[ℤ] ℤ) :=
  ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ A c) h).symm⟩

theorem nonempty_linearEquiv_int_of_injective_of_surjective (f g : A →ₗ[ℤ] ℤ)
    (hf : Function.Injective f) (hg : Function.Surjective g) : Nonempty (A ≃ₗ[ℤ] ℤ) := by
  obtain ⟨a, ha⟩ := hg 1
  refine ⟨LinearEquiv.ofBijective g ⟨fun x y hxy => ?_, hg⟩⟩
  set d : A := x - y with hd
  have hgd : g d = 0 := by rw [hd, map_sub, hxy, sub_self]
  have hkey : f a • d = f d • a := by
    apply hf
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm]
  have hs : f d = 0 := by
    have h := congrArg g hkey
    rw [map_zsmul, map_zsmul, hgd, smul_zero, ha, smul_eq_mul, mul_one] at h
    exact h.symm
  have hd0 : d = 0 := hf (hs.trans (map_zero f).symm)
  rw [hd] at hd0
  exact sub_eq_zero.mp hd0

theorem nonempty_linearEquiv_int_of_injective_of_exists_ne_zero (f : A →ₗ[ℤ] ℤ)
    (hf : Function.Injective f) (h : ∃ a : A, a ≠ 0) : Nonempty (A ≃ₗ[ℤ] ℤ) := by
  obtain ⟨a, ha⟩ := h
  have hfa : f a ≠ 0 := fun hc => ha (hf (hc.trans (map_zero f).symm))
  have hne : LinearMap.range f ≠ ⊥ := by
    intro hbot
    have hmem : f a ∈ LinearMap.range f := LinearMap.mem_range_self f a
    rw [hbot] at hmem
    exact hfa (by simpa using hmem)
  obtain ⟨m, hm⟩ := IsPrincipalIdealRing.principal (LinearMap.range f)
  have hm0 : m ≠ 0 := by
    intro h0
    apply hne
    rw [hm, h0]
    simp
  let e₁ : A ≃ₗ[ℤ] LinearMap.range f := LinearEquiv.ofInjective f hf
  let e₂ : LinearMap.range f ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofEq (LinearMap.range f) (Submodule.span ℤ ({m} : Set ℤ)) hm).trans
      (LinearEquiv.toSpanNonzeroSingleton ℤ ℤ m hm0).symm
  exact ⟨e₁.trans e₂⟩

theorem nonempty_linearEquiv_int_iff_nontrivial_of_injective (f : A →ₗ[ℤ] ℤ)
    (hf : Function.Injective f) : Nonempty (A ≃ₗ[ℤ] ℤ) ↔ Nontrivial A := by
  constructor
  · rintro ⟨e⟩
    refine ⟨0, e.symm 1, fun h => ?_⟩
    have hone : (1 : ℤ) = 0 := by
      calc (1 : ℤ) = e (e.symm 1) := (e.apply_symm_apply 1).symm
        _ = e 0 := by rw [h.symm]
        _ = 0 := map_zero e
    exact one_ne_zero hone
  · intro h
    obtain ⟨a, b, hab⟩ := h
    refine nonempty_linearEquiv_int_of_injective_of_exists_ne_zero f hf ⟨a - b, ?_⟩
    intro h0
    exact hab (sub_eq_zero.mp h0)

theorem nonempty_linearEquiv_int_iff_exists_injective_and_exists_surjective :
    Nonempty (A ≃ₗ[ℤ] ℤ) ↔
      (∃ f : A →ₗ[ℤ] ℤ, Function.Injective f) ∧
        ∃ g : A →ₗ[ℤ] ℤ, Function.Surjective g := by
  constructor
  · rintro ⟨e⟩
    exact ⟨⟨e.toLinearMap, e.injective⟩, ⟨e.toLinearMap, e.surjective⟩⟩
  · rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    exact nonempty_linearEquiv_int_of_injective_of_surjective f g hf hg

theorem not_nonempty_linearEquiv_int_of_subsingleton [Subsingleton A] :
    ¬ Nonempty (A ≃ₗ[ℤ] ℤ) := by
  rintro ⟨e⟩
  have hone : (1 : ℤ) = 0 := by
    calc (1 : ℤ) = e (e.symm 1) := (e.apply_symm_apply 1).symm
      _ = e 0 := by rw [Subsingleton.elim (e.symm 1) 0]
      _ = 0 := map_zero e
  exact one_ne_zero hone

theorem nonempty_linearEquiv_int_int : Nonempty (ℤ ≃ₗ[ℤ] ℤ) := ⟨LinearEquiv.refl ℤ ℤ⟩

theorem exists_surjective_linearMap_prod_int_int :
    ∃ g : (ℤ × ℤ) →ₗ[ℤ] ℤ, Function.Surjective g :=
  ⟨LinearMap.fst ℤ ℤ ℤ, fun y => ⟨(y, 0), rfl⟩⟩

theorem not_exists_injective_linearMap_prod_int_int :
    ¬ ∃ f : (ℤ × ℤ) →ₗ[ℤ] ℤ, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h2 : f ((f (1, 0)) • (0, 1)) = f ((f (0, 1)) • (1, 0)) := by
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, mul_comm]
  have h1 := hf h2
  have hzero : f (1, 0) = 0 := by
    have hsnd := congrArg Prod.snd h1
    rw [Prod.smul_snd, Prod.smul_snd, smul_eq_mul, mul_one, smul_eq_mul, mul_zero] at hsnd
    exact hsnd
  refine absurd (hf (hzero.trans (map_zero f).symm)) ?_
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

theorem not_nonempty_linearEquiv_int_prod_int_int : ¬ Nonempty ((ℤ × ℤ) ≃ₗ[ℤ] ℤ) :=
  fun ⟨e⟩ => not_exists_injective_linearMap_prod_int_int ⟨e.toLinearMap, e.injective⟩

theorem exists_injective_linearMap_botSubmodule :
    ∃ f : (⊥ : Submodule ℤ ℤ) →ₗ[ℤ] ℤ, Function.Injective f :=
  ⟨0, fun a b _ => Subsingleton.elim a b⟩

theorem not_nonempty_linearEquiv_int_botSubmodule :
    ¬ Nonempty ((⊥ : Submodule ℤ ℤ) ≃ₗ[ℤ] ℤ) :=
  not_nonempty_linearEquiv_int_of_subsingleton

end DifferentialGeometry.Algebra.Module

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.Algebra.Module
  let decls : List String :=
    ["nonempty_linearEquiv_int_of_bijective_toSpanSingleton",
      "nonempty_linearEquiv_int_of_injective_of_surjective",
      "nonempty_linearEquiv_int_of_injective_of_exists_ne_zero",
      "nonempty_linearEquiv_int_iff_nontrivial_of_injective",
      "nonempty_linearEquiv_int_iff_exists_injective_and_exists_surjective",
      "not_nonempty_linearEquiv_int_of_subsingleton",
      "nonempty_linearEquiv_int_int",
      "exists_surjective_linearMap_prod_int_int",
      "not_exists_injective_linearMap_prod_int_int",
      "not_nonempty_linearEquiv_int_prod_int_int",
      "exists_injective_linearMap_botSubmodule",
      "not_nonempty_linearEquiv_int_botSubmodule"]
  for d in decls do
    let n := ns.str d
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
