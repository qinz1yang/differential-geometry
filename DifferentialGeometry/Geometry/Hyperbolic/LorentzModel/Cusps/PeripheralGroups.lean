/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.AxialGroups
import Mathlib.Algebra.Module.ZLattice.Basic

noncomputable section

open Set
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.PeripheralGroups

open Hyperbolic HyperbolicAction HyperbolicBoundary Horospherical
open BusemannCocycle AxialGroups

section Rank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finrank_le_one_of_finiteIndex_zpowers (D : Submodule ℤ E)
    [DiscreteTopology D] [IsZLattice ℝ D] (a : Multiplicative D)
    (ha : (Subgroup.zpowers a).FiniteIndex) :
    Module.finrank ℝ E ≤ 1 := by
  let V := Submodule.span ℝ ({(a.toAdd : E)} : Set E)
  have hspan : Submodule.span ℝ (D : Set E) ≤ V := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨k, hk, _, hkpow⟩ :=
      (Subgroup.zpowers a).exists_pow_mem_of_index_ne_zero ha.index_ne_zero
        (Multiplicative.ofAdd (⟨v, hv⟩ : D))
    obtain ⟨j, hj⟩ := hkpow
    have hj' : (j : ℝ) • (a.toAdd : E) = (k : ℝ) • v := by
      have he := congrArg (fun u : Multiplicative D => (u.toAdd : E)) hj
      change j • (a.toAdd : E) = k • v at he
      simpa only [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul] using he
    have hmem : (k : ℝ) • v ∈ V := by
      rw [← hj']
      exact V.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
    exact (V.smul_mem_iff (Nat.cast_ne_zero.mpr hk.ne')).mp hmem
  rw [IsZLattice.span_top (K := ℝ) (L := D)] at hspan
  have hV : V = ⊤ := top_unique hspan
  have hdim := finrank_span_le_card (R := ℝ) ({(a.toAdd : E)} : Set E)
  change Module.finrank ℝ V ≤ _ at hdim
  rw [hV, finrank_top] at hdim
  simpa only [Set.toFinset_singleton, Finset.card_singleton] using hdim

theorem not_virtualCyclic_lattice (D : Submodule ℤ E)
    [DiscreteTopology D] [IsZLattice ℝ D] (hdim : 2 ≤ Module.finrank ℝ E) :
    ¬∃ a : Multiplicative D, (Subgroup.zpowers a).FiniteIndex := by
  rintro ⟨a, ha⟩
  have := finrank_le_one_of_finiteIndex_zpowers D a ha
  omega

end Rank

theorem parabolic_of_translation_lattice_iso {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (D : Submodule ℤ (Horizontal m)) [DiscreteTopology D] [IsZLattice ℝ D]
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (f : Multiplicative D ≃* Γ) :
    ∃ ξ : BoundaryH n,
      (∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (γ : PO n 1) ξ = 1) ∧
      ∀ γ : Γ, γ ≠ 1 →
        ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η → η = ξ := by
  let : AddGroup.FG D := Module.Finite.iff_addGroup_fg.mp inferInstance
  let : IsAddTorsionFree D := .of_isTorsionFree ℤ D
  let : Group.FG Γ := Group.fg_of_surjective (f := f.toMonoidHom) f.surjective
  let : Group.IsNilpotent Γ := (Group.isNilpotent_congr f).mp inferInstance
  have hnot : ¬∃ a : Γ, (Subgroup.zpowers a).FiniteIndex := by
    intro h
    exact not_virtualCyclic_lattice D (by simpa [Horizontal] using hm)
      (exists_finiteIndex_zpowers_of_mulEquiv f.symm h)
  obtain ⟨ξ, hξ, huniq⟩ := parabolic_of_fg_virtuallyNilpotent_not_virtualCyclic hn Γ hΓ
    (Group.IsNilpotent.isVirtuallyNilpotent inferInstance) hnot
  refine ⟨ξ, hξ, fun γ hγ => huniq γ ?_⟩
  intro hfin
  have hfinΓ : IsOfFinOrder γ :=
    (Γ.subtype_injective.isOfFinOrder_iff (f := Γ.subtype)).mp hfin
  have hu : f.symm γ = 1 := (f.symm.toMonoidHom.isOfFinOrder hfinΓ).eq_one'
  exact hγ (f.symm.injective (hu.trans (map_one f.symm).symm))

theorem parabolic_of_virtual_translation_lattice {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (D : Submodule ℤ (Horizontal m)) [DiscreteTopology D] [IsZLattice ℝ D]
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (H : Subgroup Γ) [H.FiniteIndex] (e : Multiplicative D ≃* H) :
    ∃ ξ : BoundaryH n,
      (∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (γ : PO n 1) ξ = 1) ∧
      ∀ γ : Γ, ¬IsOfFinOrder (γ : PO n 1) →
        ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η → η = ξ := by
  have hnot : ¬∃ a : Γ, (Subgroup.zpowers a).FiniteIndex := by
    intro h
    exact not_virtualCyclic_lattice D (by simpa [Horizontal] using hm)
      (exists_finiteIndex_zpowers_of_mulEquiv e.symm (exists_finiteIndex_zpowers_subgroup H h))
  rcases finite_or_infinite Γ with hfinite | hinfinite
  · let := hfinite
    exact (hnot ⟨1, inferInstance⟩).elim
  let := hinfinite
  let P := H.map Γ.subtype
  let eH := H.equivMapOfInjective Γ.subtype Subtype.coe_injective
  have hPΓ : P ≤ Γ := by
    rintro _ ⟨γ, _, rfl⟩
    exact γ.property
  obtain ⟨ξ, hξ, _⟩ := parabolic_of_translation_lattice_iso hm hn D P
    (hΓ.mono hPΓ) (e.trans eH)
  let := poBoundaryMulAction hn
  let : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  have horbit : (ElementaryGroups.boundaryOrbit hn Γ ξ).Finite :=
    ElementaryGroups.finite_orbit_of_finiteIndex_fixed H ξ (fun h => (hξ (eH h)).1)
  have helem : ElementaryGroups.IsElementary hn Γ :=
    Or.inr ⟨ξ, horbit, ElementaryGroups.ncard_boundaryOrbit_le_two hn Γ hΓ horbit⟩
  obtain ⟨ζ, hζ⟩ := horospherical_of_not_virtualCyclic hn Γ hΓ helem hnot
  exact ⟨ζ, hζ, unique_boundary_fixed_of_horospherical hn Γ hΓ ζ hζ⟩

theorem parabolic_image_of_iso {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (D : Submodule ℤ (Horizontal m)) [DiscreteTopology D] [IsZLattice ℝ D]
    (Γ Λ : Subgroup (PO n 1)) (hΛ : IsDiscrete (SetLike.coe Λ)) (f : Γ ≃* Λ)
    (H : Subgroup Γ) [H.FiniteIndex] (e : Multiplicative D ≃* H) :
    ∃ ξ : BoundaryH n,
      (∀ γ : Γ, (poBoundaryMulAction hn).smul (f γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (f γ : PO n 1) ξ = 1) ∧
      ∀ γ : Γ, ¬IsOfFinOrder (γ : PO n 1) →
        ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (f γ : PO n 1) η = η → η = ξ := by
  let H' := H.map f.toMonoidHom
  let : H'.FiniteIndex := ⟨by
    have heq : H'.index = H.index := H.index_map_equiv f
    rw [heq]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  obtain ⟨ξ, hξ, huniq⟩ := parabolic_of_virtual_translation_lattice hm hn D Λ hΛ H'
    (e.trans (f.subgroupMap H))
  refine ⟨ξ, fun γ => hξ (f γ), fun γ hγ => huniq (f γ) ?_⟩
  intro hfin
  have hfinΛ : IsOfFinOrder (f γ) :=
    (Λ.subtype_injective.isOfFinOrder_iff (f := Λ.subtype)).mp hfin
  have hfinΓ : IsOfFinOrder γ := by
    have h := f.symm.toMonoidHom.isOfFinOrder hfinΛ
    change IsOfFinOrder (f.symm (f γ)) at h
    rwa [f.symm_apply_apply] at h
  exact hγ (Γ.subtype.isOfFinOrder hfinΓ)

end DifferentialGeometry.PeripheralGroups
