/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Horosphere.Coordinates
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ElementaryGroups

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology IsMulCommutative

namespace DifferentialGeometry.BoundaryFixedPoints

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology ElementaryGroups Busemann BusemannCocycle

variable {n : ℕ}

theorem boundary_fixed_of_eigen (A : LorGrp n) (ξ : BoundaryH n) {c : ℝ}
    (hc : c ≠ 0) (hξ : matOf A *ᵥ ξ.val = c • ξ.val) : A • ξ = ξ := by
  apply BoundaryH.ext
  change boundaryRep (matOf A *ᵥ ξ.val) = ξ.val
  rw [hξ, boundaryRep_smul c hc]
  simp only [boundaryRep, ξ.tc_eq, inv_one, one_smul]

theorem exists_reciprocal_eigenvector (A : LorGrp n) (ξ : BoundaryH n) {c : ℝ}
    (hc : c ≠ 0) (hξ : matOf A *ᵥ ξ.val = c • ξ.val) :
    ∃ w : LorVec n, w ≠ 0 ∧ matOf A *ᵥ w = c⁻¹ • w := by
  let T : LorVec n →ₗ[ℝ] LorVec n :=
    Matrix.toLin' (matOf A) - c⁻¹ • LinearMap.id
  have hpair (v : LorVec n) : lorB ξ.val (T v) = 0 := by
    have h := lorB_matOf_mulVec A ξ.val v
    rw [hξ, lorB_smul_left] at h
    have hp : lorB ξ.val (matOf A *ᵥ v) = c⁻¹ * lorB ξ.val v := by
      calc
        lorB ξ.val (matOf A *ᵥ v) = c⁻¹ * (c * lorB ξ.val (matOf A *ᵥ v)) := by
          rw [inv_mul_cancel_left₀ hc]
        _ = c⁻¹ * lorB ξ.val v := congrArg (c⁻¹ * ·) h
    change lorB ξ.val (matOf A *ᵥ v - c⁻¹ • v) = 0
    rw [lorB_sub_right, lorB_smul_right, hp, sub_self]
  have hnotSurj : ¬Function.Surjective T := by
    intro h
    obtain ⟨v, hv⟩ := h eTime
    have hp := hpair v
    rw [hv, DirichletDomain.lorB_eTime_right, ξ.tc_eq] at hp
    norm_num at hp
  have hnotInj : ¬Function.Injective T :=
    fun h => hnotSurj (LinearMap.injective_iff_surjective.mp h)
  obtain ⟨v, w, heq, hne⟩ := Function.not_injective_iff.mp hnotInj
  refine ⟨v - w, sub_ne_zero.mpr hne, ?_⟩
  have hT : T (v - w) = 0 := by rw [map_sub, heq, sub_self]
  exact sub_eq_zero.mp hT

theorem eigenvector_is_null (A : LorGrp n) {w : LorVec n} {d : ℝ}
    (hd : d ^ 2 ≠ 1) (hw : matOf A *ᵥ w = d • w) : lorB w w = 0 := by
  have h := lorB_matOf_mulVec A w w
  rw [hw, lorB_smul_left, lorB_smul_right] at h
  have he : (d ^ 2 - 1) * lorB w w = 0 := by nlinarith
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hd)

theorem exists_other_boundary_fixed_of_eigen (A : LorGrp n) (ξ : BoundaryH n)
    {c : ℝ} (hc : c ≠ 0) (hc2 : c ^ 2 ≠ 1)
    (hξ : matOf A *ᵥ ξ.val = c • ξ.val) :
    ∃ η : BoundaryH n, η ≠ ξ ∧ A • η = η ∧ matOf A *ᵥ η.val = c⁻¹ • η.val := by
  obtain ⟨w, hw0, hw⟩ := exists_reciprocal_eigenvector A ξ hc hξ
  have hi2 : (c⁻¹) ^ 2 ≠ 1 := by
    intro h
    have he : c ^ 2 * (c⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
    exact hc2 (by simpa only [h, mul_one] using he)
  have hnull := eigenvector_is_null A hi2 hw
  have htc : tc w ≠ 0 := fun h => hw0 (eq_zero_of_lorB_self_eq_zero hnull h)
  let η : BoundaryH n := ⟨boundaryRep w, lorB_boundaryRep_self hnull, tc_boundaryRep htc⟩
  have hη : matOf A *ᵥ η.val = c⁻¹ • η.val := by
    change matOf A *ᵥ ((tc w)⁻¹ • w) = c⁻¹ • ((tc w)⁻¹ • w)
    rw [Matrix.mulVec_smul, hw]
    exact smul_comm (tc w)⁻¹ c⁻¹ w
  refine ⟨η, ?_, boundary_fixed_of_eigen A η (inv_ne_zero hc) hη, hη⟩
  intro heq
  rw [heq] at hη
  have he : c = c⁻¹ := by
    have h := congrArg tc (hξ.symm.trans hη)
    simpa only [tc_smul, ξ.tc_eq, mul_one] using h
  apply hc2
  calc
    c ^ 2 = c * c⁻¹ := by rw [pow_two, ← he]
    _ = 1 := mul_inv_cancel₀ hc

theorem exists_other_boundary_fixed_of_scale_ne_one (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hc : poConfFactor hn g ξ ≠ 1) :
    ∃ η : BoundaryH n, η ≠ ξ ∧ (poBoundaryMulAction hn).smul g η = η := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hAξ : A • ξ = ξ := (po_boundary_smul_mk hn A ξ).symm.trans hξ
  have heig := eigen_of_boundary_fixed hAξ
  have hc2 : tc (matOf A *ᵥ ξ.val) ^ 2 ≠ 1 := by
    intro h
    apply hc
    change |tc (matOf A *ᵥ ξ.val)| = 1
    rcases sq_eq_one_iff.mp h with h | h <;> rw [h] <;> norm_num
  obtain ⟨η, hηne, hη, _⟩ :=
    exists_other_boundary_fixed_of_eigen A ξ (tc_matOf_mulVec_ne_zero A ξ) hc2 heig
  exact ⟨η, hηne, (po_boundary_smul_mk hn A η).trans hη⟩

theorem poConfFactor_eq_one_of_unique_boundary_fixed (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul g η = η → η = ξ) :
    poConfFactor hn g ξ = 1 := by
  by_contra hc
  obtain ⟨η, hηne, hη⟩ := exists_other_boundary_fixed_of_scale_ne_one hn g ξ hξ hc
  exact hηne (hunique η hη)

theorem busemann_smul_of_unique_boundary_fixed (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul g η = η → η = ξ)
    (x : HUpper n) : busemann ξ ((poMulAction hn).smul g x) = busemann ξ x := by
  have h := po_busemann_smul hn g ξ x
  rwa [hξ, poConfFactor_eq_one_of_unique_boundary_fixed hn g ξ hξ hunique,
    Real.log_one, sub_zero] at h

theorem smul_mem_horoball_iff_of_unique_boundary_fixed (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul g η = η → η = ξ)
    (c : ℝ) (x : HUpper n) :
    (poMulAction hn).smul g x ∈ horoball ξ c ↔ x ∈ horoball ξ c := by
  change busemann ξ ((poMulAction hn).smul g x) ≤ c ↔ busemann ξ x ≤ c
  rw [busemann_smul_of_unique_boundary_fixed hn g ξ hξ hunique]

theorem smul_mem_horosphere_iff_of_unique_boundary_fixed (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul g η = η → η = ξ)
    (c : ℝ) (x : HUpper n) :
    (poMulAction hn).smul g x ∈ horosphere ξ c ↔ x ∈ horosphere ξ c := by
  change busemann ξ ((poMulAction hn).smul g x) = c ↔ busemann ξ x = c
  rw [busemann_smul_of_unique_boundary_fixed hn g ξ hξ hunique]

theorem exists_affineIsometry_of_unique_fixed_ptInfty {m : ℕ} (g : PO (m + 1) 1)
    (hfix : (poBoundaryMulAction (by omega)).smul g MobiusBoundary.ptInfty =
      MobiusBoundary.ptInfty)
    (hunique : ∀ η : BoundaryH (m + 1), (poBoundaryMulAction (by omega)).smul g η = η →
      η = MobiusBoundary.ptInfty) :
    ∃ a : Horospherical.Horizontal m ≃ᵃⁱ[ℝ] Horospherical.Horizontal m,
      ∀ (x : Horospherical.Horizontal m) (h : ℝ) (hh : 0 < h),
        (poMulAction (by omega)).smul g (Horospherical.ofCoords x h hh) =
          Horospherical.ofCoords (a x) h hh :=
  Horospherical.exists_affineIsometry_of_po_fix_scale_one g hfix
    (poConfFactor_eq_one_of_unique_boundary_fixed (by omega) g _ hfix hunique)

theorem isOfFinOrder_of_interior_fixed (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (γ : Γ) (p : HUpper n)
    (hp : (poMulAction hn).smul (γ : PO n 1) p = p) : IsOfFinOrder (γ : PO n 1) := by
  let := EquivariantMap.subAction hn Γ
  let H := MulAction.stabilizer Γ p
  let : Finite H := EquivariantMap.finite_stabilizer hn Γ hΓ p
  let a : H := ⟨γ, hp⟩
  obtain ⟨k, hk, hpow⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨k, hk, ?_⟩
  exact congrArg (fun b : H => ((b : Γ) : PO n 1)) hpow

theorem exists_interior_fixed_of_isOfFinOrder (hn : 1 ≤ n) (g : PO n 1)
    (hg : IsOfFinOrder g) :
    ∃ p : HUpper n, (poMulAction hn).smul g p = p := by
  let : Finite (Subgroup.zpowers g) := finite_zpowers.mpr hg
  let := Fintype.ofFinite (Subgroup.zpowers g)
  obtain ⟨p, hp, _⟩ := EquivariantMap.exists_fixed_point_of_finite_subgroup hn (Subgroup.zpowers g)
  exact ⟨p, hp g (Subgroup.mem_zpowers g)⟩

theorem exists_boundary_fixed_of_not_isOfFinOrder (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (γ : Γ)
    (hγ : ¬IsOfFinOrder (γ : PO n 1)) :
    ∃ ξ : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ := by
  let Z := Subgroup.zpowers (γ : PO n 1)
  let : Infinite Z := by
    simpa [Z] using (infinite_zpowers.mpr hγ)
  let : Group.FG Z := (Group.fg_iff_subgroup_fg Z).mpr
    ((Subgroup.fg_iff Z).mpr ⟨{(γ : PO n 1)}, (Subgroup.zpowers_eq_closure _).symm,
      Set.finite_singleton _⟩)
  obtain ⟨ξ, hξ⟩ := exists_boundary_fixed_of_nilpotent hn Z
    (hΓ.mono (Subgroup.zpowers_le.mpr γ.property))
  exact ⟨ξ, hξ ⟨γ, Subgroup.mem_zpowers (γ : PO n 1)⟩⟩

theorem poConfFactor_eq_one_of_interior_fixed (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (p : HUpper n) (hp : (poMulAction hn).smul g p = p) : poConfFactor hn g ξ = 1 := by
  have h := po_busemann_smul hn g ξ p
  rw [hξ, hp] at h
  have hl : Real.log (poConfFactor hn g ξ) = 0 := by linarith
  have he := congrArg Real.exp hl
  rwa [Real.exp_log (poConfFactor_pos hn g ξ), Real.exp_zero] at he

theorem smul_boundaryPairPoint_of_two_fixed_scale_one (hn : 1 ≤ n) (g : PO n 1)
    {ξ η : BoundaryH n} (hne : ξ ≠ η)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η) (hc : poConfFactor hn g ξ = 1) :
    (poMulAction hn).smul g (boundaryPairPoint ξ η hne) = boundaryPairPoint ξ η hne := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hAξ : A • ξ = ξ := (po_boundary_smul_mk hn A ξ).symm.trans hξ
  have hAη : A • η = η := (po_boundary_smul_mk hn A η).symm.trans hη
  have hmul := boundary_eigenvalue_mul A hne hAξ hAη
  have hs : tc (matOf A *ᵥ ξ.val) ^ 2 = 1 := by
    change |tc (matOf A *ᵥ ξ.val)| = 1 at hc
    nlinarith [sq_abs (tc (matOf A *ᵥ ξ.val))]
  have he : tc (matOf A *ᵥ ξ.val) = tc (matOf A *ᵥ η.val) := by
    apply mul_left_cancel₀ (tc_matOf_mulVec_ne_zero A ξ)
    simpa only [pow_two] using hs.trans hmul.symm
  let p := boundaryPairPoint ξ η hne
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

theorem boundary_fixed_trichotomy_of_discrete (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (γ : Γ) :
    (IsOfFinOrder (γ : PO n 1) ∧ ∃ p : HUpper n, (poMulAction hn).smul (γ : PO n 1) p = p) ∨
      (¬IsOfFinOrder (γ : PO n 1) ∧ ∃ ξ : BoundaryH n,
        (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        (∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η → η = ξ) ∧
        poConfFactor hn (γ : PO n 1) ξ = 1) ∨
      (¬IsOfFinOrder (γ : PO n 1) ∧ ∃ ξ η : BoundaryH n, ξ ≠ η ∧
        (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        (poBoundaryMulAction hn).smul (γ : PO n 1) η = η ∧
        (∀ ζ : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) ζ = ζ →
          ζ = ξ ∨ ζ = η) ∧ poConfFactor hn (γ : PO n 1) ξ ≠ 1) := by
  by_cases hγ : IsOfFinOrder (γ : PO n 1)
  · exact Or.inl ⟨hγ, exists_interior_fixed_of_isOfFinOrder hn γ hγ⟩
  obtain ⟨ξ, hξ⟩ := exists_boundary_fixed_of_not_isOfFinOrder hn Γ hΓ γ hγ
  by_cases huniq : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η → η = ξ
  · exact Or.inr (Or.inl ⟨hγ, ξ, hξ, huniq,
      poConfFactor_eq_one_of_unique_boundary_fixed hn γ ξ hξ huniq⟩)
  · obtain ⟨η, h⟩ := not_forall.mp huniq
    obtain ⟨hη, hηne⟩ := Classical.not_imp.mp h
    refine Or.inr (Or.inr ⟨hγ, ξ, η, Ne.symm hηne, hξ, hη, ?_, ?_⟩)
    · intro ζ hζ
      by_cases hζξ : ζ = ξ
      · exact Or.inl hζξ
      by_cases hζη : ζ = η
      · exact Or.inr hζη
      exact (hγ (isOfFinOrder_of_interior_fixed hn Γ hΓ γ _
        (smul_boundaryPairPoint_of_three_fixed hn γ (Ne.symm hηne) (Ne.symm hζξ)
          (Ne.symm hζη) hξ hη hζ))).elim
    · intro hc
      exact hγ (isOfFinOrder_of_interior_fixed hn Γ hΓ γ _
        (smul_boundaryPairPoint_of_two_fixed_scale_one hn γ (Ne.symm hηne) hξ hη hc))

end DifferentialGeometry.BoundaryFixedPoints
