/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Stabilizer
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.AxialGroups

open Hyperbolic HyperbolicAction HyperbolicBoundary AsymptoticRays
open ElementaryGroups BoundaryStabilizer BusemannCocycle

variable {n : ℕ}

def shiftHom (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ξ : BoundaryH n)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) :
    Γ →* Multiplicative ℝ where
  toFun γ := Multiplicative.ofAdd (Real.log (poConfFactor hn γ ξ))
  map_one' := by
    change Real.log (poConfFactor hn 1 ξ) = 0
    rw [poConfFactor_one, Real.log_one]
  map_mul' γ δ := by
    let := poBoundaryMulAction hn
    change ∀ γ : Γ, (γ : PO n 1) • ξ = ξ at hξ
    change Real.log (poConfFactor hn (γ * δ) ξ) =
      Real.log (poConfFactor hn γ ξ) + Real.log (poConfFactor hn δ ξ)
    rw [poConfFactor_mul, hξ δ,
      Real.log_mul (poConfFactor_pos hn δ ξ).ne' (poConfFactor_pos hn γ ξ).ne',
      add_comm]

theorem dist_boundaryPairPoint_eq_abs_shift (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η) :
    dist ((poMulAction hn).smul g (boundaryPairPoint ξ η hne))
      (boundaryPairPoint ξ η hne) = |Real.log (poConfFactor hn g ξ)| := by
  have h := smul_axis_ray hn g ξ η hne hξ hη 0
  rw [rayTo_zero, zero_add] at h
  calc
    _ = dist (rayTo (boundaryPairPoint ξ η hne) ξ (Real.log (poConfFactor hn g ξ)))
        (rayTo (boundaryPairPoint ξ η hne) ξ 0) := by rw [h, rayTo_zero]
    _ = _ := by rw [dist_rayTo, sub_zero]

theorem finite_shift_bounded (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) (B : ℝ) :
    {γ : Γ | |(shiftHom hn Γ ξ hξ γ).toAdd| ≤ B}.Finite := by
  apply (finite_setOf_displacement_le hn Γ hΓ (boundaryPairPoint ξ η hne) B).subset
  intro γ hγ
  change dist ((poMulAction hn).smul (γ : PO n 1) (boundaryPairPoint ξ η hne))
    (boundaryPairPoint ξ η hne) ≤ B
  rwa [dist_boundaryPairPoint_eq_abs_shift hn γ ξ η hne (hξ γ) (hη γ)]

theorem finite_shiftHom_ker (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    Finite (shiftHom hn Γ ξ hξ).ker := by
  apply (finite_shift_bounded hn Γ hΓ ξ η hne hξ hη 0).subset
  intro γ hγ
  change |(shiftHom hn Γ ξ hξ γ).toAdd| ≤ 0
  change shiftHom hn Γ ξ hξ γ = 1 at hγ
  rw [hγ]
  norm_num

theorem discrete_shiftHom_range (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    DiscreteTopology (shiftHom hn Γ ξ hξ).range := by
  let τ := shiftHom hn Γ ξ hξ
  let S : Set τ.range := {a | |(a : Multiplicative ℝ).toAdd| ≤ 1}
  have hS : S.Finite := by
    apply ((finite_shift_bounded hn Γ hΓ ξ η hne hξ hη 1).image τ.rangeRestrict).subset
    intro a ha
    obtain ⟨γ, hγ⟩ := a.property
    refine ⟨γ, ?_, Subtype.ext hγ⟩
    change |(τ γ).toAdd| ≤ 1
    rw [hγ]
    exact ha
  have hc : Continuous (fun a : τ.range => |(a : Multiplicative ℝ).toAdd|) := by
    fun_prop
  apply discreteTopology_iff_isOpen_singleton_one.mpr
  apply isOpen_singleton_of_finite_mem_nhds (1 : τ.range) _ hS
  exact hc.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by norm_num))

theorem cyclic_shiftHom_range (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    IsCyclic (shiftHom hn Γ ξ hξ).range := by
  let : OrderTopology (Multiplicative ℝ) := inferInstanceAs (OrderTopology ℝ)
  exact Subgroup.discrete_iff_cyclic.mpr (discrete_shiftHom_range hn Γ hΓ ξ η hne hξ hη)

theorem exists_finiteIndex_zpowers_of_finite_ker_cyclic_range
    {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    [Finite f.ker] [IsCyclic f.range] :
    ∃ a : G, (Subgroup.zpowers a).FiniteIndex := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := f.range)
  obtain ⟨a, ha⟩ := b.property
  let C := Subgroup.zpowers a
  have hsurj : Function.Surjective (fun k : f.ker => (QuotientGroup.mk (k : G) : G ⧸ C)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨j, hj⟩ := hb (f.rangeRestrict g)
      have hj' : f (a ^ j) = f g := by
        rw [map_zpow, ha]
        exact congrArg Subtype.val hj
      let k : f.ker := ⟨g * (a ^ j)⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hj', mul_inv_cancel]⟩
      refine ⟨k, QuotientGroup.eq.mpr ?_⟩
      change (g * (a ^ j)⁻¹)⁻¹ * g ∈ C
      simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using
        (Subgroup.zpowers a).zpow_mem (Subgroup.mem_zpowers a) j
  let : Finite (G ⧸ C) := Finite.of_surjective _ hsurj
  exact ⟨a, Subgroup.finiteIndex_of_finite_quotient⟩

theorem exists_finiteIndex_zpowers_of_two_fixed (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (hη : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    ∃ a : Γ, (Subgroup.zpowers a).FiniteIndex := by
  let := finite_shiftHom_ker hn Γ hΓ ξ η hne hξ hη
  let := cyclic_shiftHom_range hn Γ hΓ ξ η hne hξ hη
  exact exists_finiteIndex_zpowers_of_finite_ker_cyclic_range (shiftHom hn Γ ξ hξ)

theorem exists_finiteIndex_zpowers_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (h : ∃ a : G, (Subgroup.zpowers a).FiniteIndex) :
    ∃ a : G', (Subgroup.zpowers a).FiniteIndex := by
  obtain ⟨a, ha⟩ := h
  refine ⟨e a, ⟨?_⟩⟩
  change (Subgroup.zpowers (e.toMonoidHom a)).index ≠ 0
  rw [← MonoidHom.map_zpowers e.toMonoidHom a,
    Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  exact ha.index_ne_zero

theorem exists_finiteIndex_zpowers_of_finiteIndex_subgroup
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (h : ∃ a : H, (Subgroup.zpowers a).FiniteIndex) :
    ∃ a : G, (Subgroup.zpowers a).FiniteIndex := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ⟨?_⟩⟩
  change (Subgroup.zpowers (H.subtype a)).index ≠ 0
  rw [← MonoidHom.map_zpowers H.subtype a, Subgroup.index_map_subtype]
  exact mul_ne_zero ha.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

theorem exists_finiteIndex_zpowers_subgroup {G : Type*} [Group G]
    (H : Subgroup G) (h : ∃ a : G, (Subgroup.zpowers a).FiniteIndex) :
    ∃ a : H, (Subgroup.zpowers a).FiniteIndex := by
  obtain ⟨a, ha⟩ := h
  let := ha
  let C := (Subgroup.zpowers a).subgroupOf H
  let j : C →* Subgroup.zpowers a :=
    (H.subtype.comp C.subtype).codRestrict _ (fun c => c.property)
  have hj : Function.Injective j := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.zpowers a => (z : G)) hcd
  let : IsCyclic C := isCyclic_of_injective j hj
  obtain ⟨b, hb⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top C).mp inferInstance
  refine ⟨b, ?_⟩
  rw [hb]
  exact inferInstanceAs (((Subgroup.zpowers a).subgroupOf H).FiniteIndex)

theorem exists_finiteIndex_zpowers_of_pair (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : ∀ γ : Γ,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) :
    ∃ a : Γ, (Subgroup.zpowers a).FiniteIndex := by
  let := poBoundaryMulAction hn
  let : MulAction Γ (BoundaryH n) := MulAction.compHom _ Γ.subtype
  let H := MulAction.stabilizer Γ ξ
  have horbit : (MulAction.orbit Γ ξ).Finite :=
    (Set.toFinite ({ξ, η} : Set (BoundaryH n))).subset (by
      rintro _ ⟨γ, rfl⟩
      exact (hpair γ).1)
  let : Finite (MulAction.orbit Γ ξ) := horbit
  let : H.FiniteIndex := Subgroup.finiteIndex_iff_finite_quotient.mpr
    (Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer Γ ξ))
  let D := H.map Γ.subtype
  let e := H.equivMapOfInjective Γ.subtype Subtype.coe_injective
  have hDΓ : D ≤ Γ := by
    rintro _ ⟨γ, _, rfl⟩
    exact γ.property
  have hDξ (d : D) : (poBoundaryMulAction hn).smul (d : PO n 1) ξ = ξ := by
    obtain ⟨γ, hγ, hγd⟩ := d.property
    rw [← hγd]
    exact hγ
  have hDη (d : D) : (poBoundaryMulAction hn).smul (d : PO n 1) η = η := by
    have hp := (hpair ⟨d, hDΓ d.property⟩).2
    rcases hp with hp | hp
    · have he : (d : PO n 1) • η = (d : PO n 1) • ξ := hp.trans (hDξ d).symm
      exact (hne ((MulAction.toPerm (d : PO n 1)).injective he).symm).elim
    · exact hp
  apply exists_finiteIndex_zpowers_of_finiteIndex_subgroup H
  exact exists_finiteIndex_zpowers_of_mulEquiv e.symm
    (exists_finiteIndex_zpowers_of_two_fixed hn D (hΓ.mono hDΓ) ξ η hne hDξ hDη)

def ElementaryStructure (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Prop :=
  (Finite Γ ∧ ∃ p : HUpper n, ∀ γ : Γ, (poMulAction hn).smul (γ : PO n 1) p = p) ∨
  ((∃ ξ η : BoundaryH n, ξ ≠ η ∧ ∀ γ : Γ,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) ∧
    ∃ a : Γ, (Subgroup.zpowers a).FiniteIndex) ∨
  (∃ ξ : BoundaryH n, ∀ γ : Γ,
    (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧ poConfFactor hn (γ : PO n 1) ξ = 1)

theorem structure_of_geometry (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hgeometry : ElementaryGeometry hn Γ) :
    ElementaryStructure hn Γ := by
  rcases hgeometry with hfinite | ⟨ξ, η, hne, hpair⟩ | hhoro
  · exact Or.inl hfinite
  · exact Or.inr (Or.inl ⟨⟨ξ, η, hne, hpair⟩,
      exists_finiteIndex_zpowers_of_pair hn Γ hΓ ξ η hne hpair⟩)
  · exact Or.inr (Or.inr hhoro)

theorem smallSubgroup_structure (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n)
    (hvirt : Group.IsVirtuallyNilpotent (Margulis.smallSubgroup hn Γ ε x)) :
    ElementaryStructure hn (Margulis.smallSubgroup hn Γ ε x) :=
  structure_of_geometry hn _ (hΓ.mono (Margulis.smallSubgroup_le hn Γ ε x))
    (smallSubgroup_geometry hn Γ hΓ ε x hvirt)

theorem exists_margulis_structure_constant (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ x : HUpper n, ElementaryStructure hn (Margulis.smallSubgroup hn Γ ε x) := by
  obtain ⟨ε, hε, hMargulis⟩ := Margulis.exists_margulis_constant hn
  exact ⟨ε, hε, fun Γ hΓ x => smallSubgroup_structure hn Γ hΓ ε x (hMargulis Γ hΓ x)⟩

theorem horospherical_of_not_virtualCyclic (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (helem : IsElementary hn Γ)
    (hnot : ¬∃ a : Γ, (Subgroup.zpowers a).FiniteIndex) :
    ∃ ξ : BoundaryH n, ∀ γ : Γ,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1 := by
  rcases structure_of_geometry hn Γ hΓ (elementary_geometry hn Γ hΓ helem) with
    ⟨hfinite, _⟩ | ⟨_, hcyc⟩ | hhoro
  · let := hfinite
    exact (hnot ⟨1, inferInstance⟩).elim
  · exact (hnot hcyc).elim
  · exact hhoro

theorem unique_boundary_fixed_of_horospherical (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ξ : BoundaryH n)
    (hfix : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1)
    (γ : Γ) (hγ : ¬IsOfFinOrder (γ : PO n 1))
    (η : BoundaryH n) (hη : (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) :
    η = ξ := by
  by_contra hne
  exact hγ (BoundaryFixedPoints.isOfFinOrder_of_interior_fixed hn Γ hΓ γ _
    (BoundaryFixedPoints.smul_boundaryPairPoint_of_two_fixed_scale_one hn γ (Ne.symm hne)
      (hfix γ).1 hη (hfix γ).2))

theorem parabolic_of_fg_virtuallyNilpotent_not_virtualCyclic
    (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [Group.FG Γ] (hvirt : Group.IsVirtuallyNilpotent Γ)
    (hnot : ¬∃ a : Γ, (Subgroup.zpowers a).FiniteIndex) :
    ∃ ξ : BoundaryH n,
      (∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (γ : PO n 1) ξ = 1) ∧
      ∀ γ : Γ, ¬IsOfFinOrder (γ : PO n 1) →
        ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η → η = ξ := by
  obtain ⟨ξ, hξ⟩ := horospherical_of_not_virtualCyclic hn Γ hΓ
    (isElementary_of_fg_virtuallyNilpotent hn Γ hΓ hvirt) hnot
  exact ⟨ξ, hξ, unique_boundary_fixed_of_horospherical hn Γ hΓ ξ hξ⟩

end DifferentialGeometry.AxialGroups
