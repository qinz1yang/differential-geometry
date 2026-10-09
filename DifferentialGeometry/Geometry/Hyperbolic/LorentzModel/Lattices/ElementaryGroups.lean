/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Accumulation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Homeomorphism
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.Margulis
import DifferentialGeometry.Topology.Algebra.Group.NilpotentCenter
import Mathlib.GroupTheory.Schreier

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.ElementaryGroups

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology BoundaryAccumulation

variable {n : ℕ}

theorem finite_smallElements (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    (Margulis.smallElements hn Γ ε x).Finite := by
  let := poMulAction hn
  let S : Set Γ := {γ | dist ((γ : PO n 1) • x) x < ε}
  have hS : S.Finite :=
    (DirichletDomain.finite_setOf_coe_le hn Γ hΓ (2 * dist x basepointH + ε)).subset (by
      intro γ hγ
      have hd := (dist_triangle ((γ : PO n 1) • basepointH)
        ((γ : PO n 1) • x) basepointH).trans
          (add_le_add le_rfl (dist_triangle ((γ : PO n 1) • x) x basepointH))
      rw [po_dist_smul hn (γ : PO n 1) basepointH x, dist_comm basepointH x] at hd
      have hshort : dist ((γ : PO n 1) • x) x < ε := hγ
      change dist ((γ : PO n 1) • basepointH) basepointH ≤ _
      linarith)
  apply (hS.image ((↑) : Γ → PO n 1)).subset
  intro g hg
  exact ⟨⟨g, hg.1⟩, hg.2, rfl⟩

theorem fg_smallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    Group.FG (Margulis.smallSubgroup hn Γ ε x) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  exact (Subgroup.fg_iff _).mpr
    ⟨Margulis.smallElements hn Γ ε x, rfl, finite_smallElements hn Γ hΓ ε x⟩

theorem exists_boundary_fixed_of_nilpotent (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) [Group.FG Γ] [Group.IsNilpotent Γ] [Infinite Γ] :
    ∃ ξ : BoundaryH n, ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ := by
  let C := (Subgroup.center Γ).map Γ.subtype
  let e := (Subgroup.center Γ).equivMapOfInjective Γ.subtype Subtype.coe_injective
  let : Infinite (Subgroup.center Γ) := NilpotentCenter.infinite_center
  let : Infinite C := e.toEquiv.infinite_iff.mp inferInstance
  have hCΓ : C ≤ Γ := by
    rintro _ ⟨γ, _, rfl⟩
    exact γ.property
  obtain ⟨ξ, hξ⟩ := exists_boundary_fixed_by_centralizer hn C (hΓ.mono hCΓ)
  refine ⟨ξ, fun γ => hξ γ ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨z, hz, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz γ).symm

section FiniteIndexAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem finite_orbit_of_finiteIndex_fixed (H : Subgroup G) [H.FiniteIndex]
    (x : X) (hx : ∀ h : H, (h : G) • x = x) : (MulAction.orbit G x).Finite := by
  have hle : H ≤ MulAction.stabilizer G x := fun h hh => hx ⟨h, hh⟩
  let : (MulAction.stabilizer G x).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv (G ⧸ MulAction.stabilizer G x)
    (MulAction.orbitEquivQuotientStabilizer G x).symm

end FiniteIndexAction

def boundaryOrbit (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ξ : BoundaryH n) :
    Set (BoundaryH n) :=
  Set.range (fun γ : Γ => (poBoundaryMulAction hn).smul (γ : PO n 1) ξ)

theorem self_mem_boundaryOrbit (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ξ : BoundaryH n) :
    ξ ∈ boundaryOrbit hn Γ ξ :=
  ⟨1, (poBoundaryMulAction hn).one_smul _⟩

theorem smul_mem_boundaryOrbit (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ξ : BoundaryH n)
    (γ : Γ) {η : BoundaryH n} (hη : η ∈ boundaryOrbit hn Γ ξ) :
    (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ boundaryOrbit hn Γ ξ := by
  obtain ⟨δ, rfl⟩ := hη
  exact ⟨γ * δ, (poBoundaryMulAction hn).mul_smul _ _ _⟩

theorem exists_finite_boundaryOrbit_of_virtuallyNilpotent (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [Group.FG Γ] [Infinite Γ] (hvirt : Group.IsVirtuallyNilpotent Γ) :
    ∃ ξ : BoundaryH n, (boundaryOrbit hn Γ ξ).Finite := by
  obtain ⟨H, hHnil, hHindex⟩ := hvirt
  let := hHnil
  let := hHindex
  let : Infinite H := not_finite_iff_infinite.mp (fun h =>
    ((Subgroup.finite_iff_finite_and_finiteIndex H).mpr ⟨h, hHindex⟩).false)
  let H' := H.map Γ.subtype
  let e := H.equivMapOfInjective Γ.subtype Subtype.coe_injective
  let : Group.FG H' := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsNilpotent H' := (Group.isNilpotent_congr e).mp hHnil
  let : Infinite H' := e.toEquiv.infinite_iff.mp inferInstance
  have hH'Γ : H' ≤ Γ := by
    rintro _ ⟨γ, _, rfl⟩
    exact γ.property
  obtain ⟨ξ, hξ⟩ := exists_boundary_fixed_of_nilpotent hn H' (hΓ.mono hH'Γ)
  let := poBoundaryMulAction hn
  let : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  refine ⟨ξ, finite_orbit_of_finiteIndex_fixed H ξ (fun h => ?_)⟩
  exact hξ (e h)

theorem lorB_boundary_neg_of_ne {ξ η : BoundaryH n} (hne : ξ ≠ η) :
    lorB ξ.val η.val < 0 := by
  have h := BoundaryHomeomorph.bratioB_nonneg ξ η
  change 0 ≤ -lorB ξ.val η.val at h
  have hzero : lorB ξ.val η.val ≠ 0 := by
    intro he
    apply hne
    apply BoundaryHomeomorph.boundary_eq_of_bratioB_eq_zero
    change -lorB ξ.val η.val = 0
    rw [he, neg_zero]
  exact lt_of_le_of_ne (by linarith) hzero

def boundaryPairPoint (ξ η : BoundaryH n) (hne : ξ ≠ η) : HUpper n where
  val := (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ • (ξ.val + η.val)
  is_unit := by
    have hpos : 0 < -2 * lorB ξ.val η.val := by
      have := lorB_boundary_neg_of_ne hne
      linarith
    have hs := Real.sq_sqrt hpos.le
    have hs0 := (Real.sqrt_pos.mpr hpos).ne'
    have hsum : lorB (ξ.val + η.val) (ξ.val + η.val) = 2 * lorB ξ.val η.val := by
      rw [lorB_add_left, lorB_add_right, lorB_add_right, ξ.is_null, η.is_null,
        lorB_comm η.val ξ.val]
      ring
    rw [lorB_smul_left, lorB_smul_right, hsum]
    calc
      (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ *
          ((Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ * (2 * lorB ξ.val η.val)) =
          (2 * lorB ξ.val η.val) / (Real.sqrt (-2 * lorB ξ.val η.val)) ^ 2 := by
            rw [div_eq_mul_inv, ← inv_pow]
            ring
      _ = -1 := (div_eq_iff (pow_ne_zero 2 hs0)).mpr (by nlinarith)
  future := by
    have hpos : 0 < -2 * lorB ξ.val η.val := by
      have := lorB_boundary_neg_of_ne hne
      linarith
    simp only [tc_smul, tc_add, ξ.tc_eq, η.tc_eq]
    positivity

theorem boundary_eigenvalue_mul (A : LorGrp n) {ξ η : BoundaryH n}
    (hne : ξ ≠ η) (hξ : A • ξ = ξ) (hη : A • η = η) :
    tc (matOf A *ᵥ ξ.val) * tc (matOf A *ᵥ η.val) = 1 := by
  have h := lorB_matOf_mulVec A ξ.val η.val
  rw [eigen_of_boundary_fixed hξ, eigen_of_boundary_fixed hη,
    lorB_smul_left, lorB_smul_right] at h
  apply mul_right_cancel₀ (lorB_boundary_neg_of_ne hne).ne
  simpa only [mul_assoc, one_mul] using h

theorem smul_boundaryPairPoint_of_three_fixed (hn : 1 ≤ n) (g : PO n 1)
    {ξ η ζ : BoundaryH n} (hξη : ξ ≠ η) (hξζ : ξ ≠ ζ) (hηζ : η ≠ ζ)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η)
    (hζ : (poBoundaryMulAction hn).smul g ζ = ζ) :
    (poMulAction hn).smul g (boundaryPairPoint ξ η hξη) = boundaryPairPoint ξ η hξη := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hAξ : A • ξ = ξ := (po_boundary_smul_mk hn A ξ).symm.trans hξ
  have hAη : A • η = η := (po_boundary_smul_mk hn A η).symm.trans hη
  have hAζ : A • ζ = ζ := (po_boundary_smul_mk hn A ζ).symm.trans hζ
  have hξη' := boundary_eigenvalue_mul A hξη hAξ hAη
  have hξζ' := boundary_eigenvalue_mul A hξζ hAξ hAζ
  have hηζ' := boundary_eigenvalue_mul A hηζ hAη hAζ
  have he : tc (matOf A *ᵥ ξ.val) = tc (matOf A *ᵥ η.val) :=
    mul_right_cancel₀ (tc_matOf_mulVec_ne_zero A ζ) (hξζ'.trans hηζ'.symm)
  have hs : tc (matOf A *ᵥ ξ.val) ^ 2 = 1 := by
    rw [← he, ← pow_two] at hξη'
    exact hξη'
  let p := boundaryPairPoint ξ η hξη
  have hAp : matOf A *ᵥ p.val = tc (matOf A *ᵥ ξ.val) • p.val := by
    change matOf A *ᵥ ((Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ • (ξ.val + η.val)) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, eigen_of_boundary_fixed hAξ,
      eigen_of_boundary_fixed hAη, ← he, ← smul_add]
    simp only [tc_smul, ξ.tc_eq, mul_one]
    exact smul_comm (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹
      (tc (matOf A *ᵥ ξ.val)) (ξ.val + η.val)
  apply (po_smul_mk hn A p).trans
  apply HUpper.ext
  change upperize (matOf A *ᵥ p.val) = p.val
  rw [hAp]
  rcases sq_eq_one_iff.mp hs with h | h
  · rw [h, one_smul]
    exact ite_eq_left p.future
  · rw [h, neg_one_smul, upperize_neg p.future.ne']
    exact ite_eq_left p.future

theorem finite_of_three_boundary_fixed (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ξ η ζ : BoundaryH n}
    (hξη : ξ ≠ η) (hξζ : ξ ≠ ζ) (hηζ : η ≠ ζ)
    (hfix : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η = η ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) ζ = ζ) : Finite Γ := by
  let p := boundaryPairPoint ξ η hξη
  let := EquivariantMap.subAction hn Γ
  let : Finite (MulAction.stabilizer Γ p) :=
    EquivariantMap.finite_stabilizer hn Γ hΓ p
  let j : Γ → MulAction.stabilizer Γ p := fun γ =>
    ⟨γ, smul_boundaryPairPoint_of_three_fixed hn γ hξη hξζ hηζ
      (hfix γ).1 (hfix γ).2.1 (hfix γ).2.2⟩
  exact Finite.of_injective j (fun _ _ h => congrArg Subtype.val h)

theorem finite_of_finite_invariant_boundary_set_three (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {S : Set (BoundaryH n)} (hS : S.Finite)
    (hinv : ∀ (γ : Γ) (ξ : BoundaryH n), ξ ∈ S →
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ S)
    {ξ η ζ : BoundaryH n} (hξ : ξ ∈ S) (hη : η ∈ S) (hζ : ζ ∈ S)
    (hξη : ξ ≠ η) (hξζ : ξ ≠ ζ) (hηζ : η ≠ ζ) : Finite Γ := by
  let := poBoundaryMulAction hn
  let : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  have hindex (u : BoundaryH n) (hu : u ∈ S) : (MulAction.stabilizer Γ u).FiniteIndex := by
    have ho : (MulAction.orbit Γ u).Finite := hS.subset (by
      rintro _ ⟨γ, rfl⟩
      exact hinv γ u hu)
    let : Finite (MulAction.orbit Γ u) := ho
    apply Subgroup.finiteIndex_iff_finite_quotient.mpr
    exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer Γ u)
  let := hindex ξ hξ
  let := hindex η hη
  let := hindex ζ hζ
  let H := MulAction.stabilizer Γ ξ ⊓ MulAction.stabilizer Γ η ⊓ MulAction.stabilizer Γ ζ
  let D := H.map Γ.subtype
  let e := H.equivMapOfInjective Γ.subtype Subtype.coe_injective
  have hDΓ : D ≤ Γ := by
    rintro _ ⟨γ, _, rfl⟩
    exact γ.property
  have hDfix (d : D) :
      (d : PO n 1) • ξ = ξ ∧ (d : PO n 1) • η = η ∧ (d : PO n 1) • ζ = ζ := by
    obtain ⟨γ, hγ, hγd⟩ := d.property
    rw [← hγd]
    exact ⟨hγ.1.1, hγ.1.2, hγ.2⟩
  have hDfin : Finite D :=
    finite_of_three_boundary_fixed hn D (hΓ.mono hDΓ) hξη hξζ hηζ hDfix
  let := hDfin
  have hHfin : Finite H := Finite.of_equiv D e.symm.toEquiv
  exact (Subgroup.finite_iff_finite_and_finiteIndex H).mpr ⟨hHfin, inferInstance⟩

theorem ncard_boundaryOrbit_le_two (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) [Infinite Γ] {ξ : BoundaryH n}
    (hfin : (boundaryOrbit hn Γ ξ).Finite) : (boundaryOrbit hn Γ ξ).ncard ≤ 2 := by
  by_contra h
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
    (Set.two_lt_ncard_iff hfin).mp (not_le.mp h)
  exact (finite_of_finite_invariant_boundary_set_three hn Γ hΓ hfin
    (fun γ _ hη => smul_mem_boundaryOrbit hn Γ ξ γ hη) hu hv hw huv huw hvw).false

def IsElementary (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Prop :=
  (Finite Γ ∧ ∃ p : HUpper n, ∀ γ : Γ, (poMulAction hn).smul (γ : PO n 1) p = p) ∨
    ∃ ξ : BoundaryH n, (boundaryOrbit hn Γ ξ).Finite ∧ (boundaryOrbit hn Γ ξ).ncard ≤ 2

theorem isElementary_of_fg_virtuallyNilpotent (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [Group.FG Γ] (hvirt : Group.IsVirtuallyNilpotent Γ) : IsElementary hn Γ := by
  rcases finite_or_infinite Γ with hfinite | hinfinite
  · let := hfinite
    let := Fintype.ofFinite Γ
    obtain ⟨p, hp, _⟩ := EquivariantMap.exists_fixed_point_of_finite_subgroup hn Γ
    exact Or.inl ⟨hfinite, p, fun γ => hp γ γ.property⟩
  · let := hinfinite
    obtain ⟨ξ, hξ⟩ := exists_finite_boundaryOrbit_of_virtuallyNilpotent hn Γ hΓ hvirt
    exact Or.inr ⟨ξ, hξ, ncard_boundaryOrbit_le_two hn Γ hΓ hξ⟩

theorem fixed_point_or_pair_of_finite_boundaryOrbit (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) [Infinite Γ]
    {ξ : BoundaryH n} (hfin : (boundaryOrbit hn Γ ξ).Finite) :
    (∃ u : BoundaryH n, ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) u = u) ∨
      ∃ u v : BoundaryH n, u ≠ v ∧ ∀ γ : Γ,
        (poBoundaryMulAction hn).smul (γ : PO n 1) u ∈ ({u, v} : Set (BoundaryH n)) ∧
        (poBoundaryMulAction hn).smul (γ : PO n 1) v ∈ ({u, v} : Set (BoundaryH n)) := by
  have htwo := ncard_boundaryOrbit_le_two hn Γ hΓ hfin
  by_cases hone : (boundaryOrbit hn Γ ξ).ncard ≤ 1
  · refine Or.inl ⟨ξ, fun γ => ?_⟩
    exact (Set.ncard_le_one_iff hfin).mp hone ⟨γ, rfl⟩ (self_mem_boundaryOrbit hn Γ ξ)
  · obtain ⟨u, v, huv, hpair⟩ := Set.ncard_eq_two.mp (show (boundaryOrbit hn Γ ξ).ncard = 2 by omega)
    have hu : u ∈ boundaryOrbit hn Γ ξ := by rw [hpair]; simp
    have hv : v ∈ boundaryOrbit hn Γ ξ := by rw [hpair]; simp
    exact Or.inr ⟨u, v, huv, fun γ => ⟨hpair ▸ smul_mem_boundaryOrbit hn Γ ξ γ hu,
      hpair ▸ smul_mem_boundaryOrbit hn Γ ξ γ hv⟩⟩

theorem isElementary_smallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n)
    (hvirt : Group.IsVirtuallyNilpotent (Margulis.smallSubgroup hn Γ ε x)) :
    IsElementary hn (Margulis.smallSubgroup hn Γ ε x) := by
  let := fg_smallSubgroup hn Γ hΓ ε x
  exact isElementary_of_fg_virtuallyNilpotent hn _
    (hΓ.mono (Margulis.smallSubgroup_le hn Γ ε x)) hvirt

theorem exists_elementary_margulis_constant (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ x : HUpper n, IsElementary hn (Margulis.smallSubgroup hn Γ ε x) := by
  obtain ⟨ε, hε, hMargulis⟩ := Margulis.exists_margulis_constant hn
  exact ⟨ε, hε, fun Γ hΓ x => isElementary_smallSubgroup hn Γ hΓ ε x (hMargulis Γ hΓ x)⟩

end DifferentialGeometry.ElementaryGroups
