/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.FixedPoints

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryStabilizer

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology AsymptoticRays Busemann BusemannCocycle
open ElementaryGroups BoundaryFixedPoints

variable {n : ℕ}

theorem poConfFactor_one (hn : 1 ≤ n) (ξ : BoundaryH n) :
    poConfFactor hn 1 ξ = 1 := by
  change confFactor (1 : LorGrp n) ξ = 1
  simp only [confFactor, matOf_one, Matrix.one_mulVec, ξ.tc_eq, abs_one]

theorem boundary_pow_fixed (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) (k : ℕ) :
    (poBoundaryMulAction hn).smul (g ^ k) ξ = ξ := by
  let := poBoundaryMulAction hn
  exact (MulAction.stabilizer (PO n 1) ξ).pow_mem hξ k

theorem boundary_inv_fixed (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) :
    (poBoundaryMulAction hn).smul g⁻¹ ξ = ξ := by
  let := poBoundaryMulAction hn
  exact (MulAction.stabilizer (PO n 1) ξ).inv_mem hξ

theorem poConfFactor_pow_of_fixed (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) (k : ℕ) :
    poConfFactor hn (g ^ k) ξ = poConfFactor hn g ξ ^ k := by
  let := poBoundaryMulAction hn
  change g • ξ = ξ at hξ
  induction k with
  | zero => rw [pow_zero, pow_zero, poConfFactor_one]
  | succ k ih =>
    rw [pow_succ, poConfFactor_mul, hξ, ih, pow_succ, mul_comm]

theorem poConfFactor_inv_of_fixed (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) :
    poConfFactor hn g⁻¹ ξ = (poConfFactor hn g ξ)⁻¹ := by
  let := poBoundaryMulAction hn
  change g • ξ = ξ at hξ
  have h := poConfFactor_mul hn g⁻¹ g ξ
  rw [inv_mul_cancel, poConfFactor_one, hξ] at h
  apply mul_left_cancel₀ (poConfFactor_pos hn g ξ).ne'
  exact h.symm.trans (mul_inv_cancel₀ (poConfFactor_pos hn g ξ).ne').symm

theorem exists_exactly_two_fixed_of_scale_ne_one (hn : 1 ≤ n) (g : PO n 1)
    (ξ : BoundaryH n) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hc : poConfFactor hn g ξ ≠ 1) :
    ∃ η : BoundaryH n, η ≠ ξ ∧ (poBoundaryMulAction hn).smul g η = η ∧
      ∀ ζ : BoundaryH n, (poBoundaryMulAction hn).smul g ζ = ζ → ζ = ξ ∨ ζ = η := by
  obtain ⟨η, hηne, hη⟩ := exists_other_boundary_fixed_of_scale_ne_one hn g ξ hξ hc
  refine ⟨η, hηne, hη, fun ζ hζ => ?_⟩
  by_cases hζξ : ζ = ξ
  · exact Or.inl hζξ
  by_cases hζη : ζ = η
  · exact Or.inr hζη
  exact (hc (poConfFactor_eq_one_of_interior_fixed hn g ξ hξ _
    (smul_boundaryPairPoint_of_three_fixed hn g hηne.symm (Ne.symm hζξ)
      (Ne.symm hζη) hξ hη hζ))).elim

theorem exists_positive_boundary_lift (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) :
    ∃ A : LorGrp n, QuotientGroup.mk' _ A = g ∧
      matOf A *ᵥ ξ.val = poConfFactor hn g ξ • ξ.val := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hAξ : A • ξ = ξ := (po_boundary_smul_mk hn A ξ).symm.trans hξ
  have he := eigen_of_boundary_fixed hAξ
  change matOf A *ᵥ ξ.val = tc (matOf A *ᵥ ξ.val) • ξ.val at he
  by_cases hpos : 0 ≤ tc (matOf A *ᵥ ξ.val)
  · refine ⟨A, rfl, ?_⟩
    change matOf A *ᵥ ξ.val = |tc (matOf A *ᵥ ξ.val)| • ξ.val
    rwa [abs_of_nonneg hpos]
  · refine ⟨-A, BoundaryExtension.mk'_neg_eq_mk' A, ?_⟩
    have hmat : matOf (-A) = -matOf A := by
      change MatrixSum.ofMatrix.symm (-A : LorGrp n).val = -MatrixSum.ofMatrix.symm A.val
      rw [Unitary.coe_neg]
      exact map_neg _ _
    change matOf (-A) *ᵥ ξ.val = |tc (matOf A *ᵥ ξ.val)| • ξ.val
    rw [hmat, Matrix.neg_mulVec, he]
    simp only [tc_smul, ξ.tc_eq, mul_one]
    rw [abs_of_nonpos (le_of_not_ge hpos), neg_smul]

theorem dirTo_boundaryPairPoint (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    dirTo (boundaryPairPoint ξ η hne) ξ =
      (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ • (ξ.val - η.val) := by
  let s := Real.sqrt (-2 * lorB ξ.val η.val)
  have hpos : 0 < -2 * lorB ξ.val η.val := by
    have := lorB_boundary_neg_of_ne hne
    linarith
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs : s ^ 2 = -2 * lorB ξ.val η.val := Real.sq_sqrt hpos.le
  have hid : s⁻¹ * (2 * lorB ξ.val η.val) = -s := by
    calc
      s⁻¹ * (2 * lorB ξ.val η.val) = s⁻¹ * (-(s ^ 2)) := by rw [hs]; ring
      _ = -(s⁻¹ * s) * s := by ring
      _ = -s := by rw [inv_mul_cancel₀ hs0, neg_one_mul]
  have hpair : -lorB (boundaryPairPoint ξ η hne).val ξ.val = s / 2 := by
    change -lorB (s⁻¹ • (ξ.val + η.val)) ξ.val = s / 2
    rw [lorB_smul_left, lorB_add_left, ξ.is_null, lorB_comm η.val ξ.val, zero_add]
    linarith
  have hnorm : (-lorB (boundaryPairPoint ξ η hne).val ξ.val)⁻¹ = 2 * s⁻¹ := by
    rw [hpair, inv_div, div_eq_mul_inv]
  have hsum := add_dirTo_eq (boundaryPairPoint ξ η hne) ξ
  rw [hnorm] at hsum
  have hd : dirTo (boundaryPairPoint ξ η hne) ξ =
      (2 * s⁻¹) • ξ.val - (boundaryPairPoint ξ η hne).val :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hsum)
  rw [hd]
  change (2 * s⁻¹) • ξ.val - s⁻¹ • (ξ.val + η.val) = s⁻¹ • (ξ.val - η.val)
  module

theorem rayTo_boundaryPairPoint_val (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) :
    (rayTo (boundaryPairPoint ξ η hne) ξ t).val =
      (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ •
        (Real.exp t • ξ.val + Real.exp (-t) • η.val) := by
  change Real.cosh t • (boundaryPairPoint ξ η hne).val +
    Real.sinh t • dirTo (boundaryPairPoint ξ η hne) ξ = _
  rw [dirTo_boundaryPairPoint]
  have hplus : Real.exp t = Real.cosh t + Real.sinh t := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hminus : Real.exp (-t) = Real.cosh t - Real.sinh t := (cosh_sub_sinh t).symm
  rw [hplus, hminus]
  change Real.cosh t • ((Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ • (ξ.val + η.val)) +
    Real.sinh t • ((Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ • (ξ.val - η.val)) = _
  module

theorem smul_axis_ray (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (hne : ξ ≠ η) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η) (t : ℝ) :
    (poMulAction hn).smul g (rayTo (boundaryPairPoint ξ η hne) ξ t) =
      rayTo (boundaryPairPoint ξ η hne) ξ (t + Real.log (poConfFactor hn g ξ)) := by
  let c := poConfFactor hn g ξ
  have hc : 0 < c := poConfFactor_pos hn g ξ
  obtain ⟨A, hA, hAξ⟩ := exists_positive_boundary_lift hn g ξ hξ
  have hAη : A • η = η := by
    rw [← hA] at hη
    exact (po_boundary_smul_mk hn A η).symm.trans hη
  have hcA : tc (matOf A *ᵥ ξ.val) = c := by
    rw [hAξ, tc_smul, ξ.tc_eq, mul_one]
  have hmul := boundary_eigenvalue_mul A hne (boundary_fixed_of_eigen A ξ hc.ne' hAξ) hAη
  rw [hcA] at hmul
  have hcη : tc (matOf A *ᵥ η.val) = c⁻¹ := by
    apply mul_left_cancel₀ hc.ne'
    exact hmul.trans (mul_inv_cancel₀ hc.ne').symm
  have hAηv : matOf A *ᵥ η.val = c⁻¹ • η.val := by
    rw [eigen_of_boundary_fixed hAη, hcη]
  let p := boundaryPairPoint ξ η hne
  have hmat : matOf A *ᵥ (rayTo p ξ t).val = (rayTo p ξ (t + Real.log c)).val := by
    rw [rayTo_boundaryPairPoint_val, rayTo_boundaryPairPoint_val,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hAξ, hAηv]
    have hplus : Real.exp (t + Real.log c) = Real.exp t * c := by
      rw [Real.exp_add, Real.exp_log hc]
    have hminus : Real.exp (-(t + Real.log c)) = Real.exp (-t) * c⁻¹ := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log c), Real.exp_log hc]
    rw [hplus, hminus]
    change _ = (Real.sqrt (-2 * lorB ξ.val η.val))⁻¹ •
      ((Real.exp t * c) • ξ.val + (Real.exp (-t) * c⁻¹) • η.val)
    module
  calc
    (poMulAction hn).smul g (rayTo p ξ t) = A • rayTo p ξ t := by
      rw [← hA]
      exact po_smul_mk hn A _
    _ = rayTo p ξ (t + Real.log c) := by
      apply HUpper.ext
      change upperize (matOf A *ᵥ (rayTo p ξ t).val) = _
      rw [hmat]
      exact ite_eq_left (rayTo p ξ (t + Real.log c)).future

theorem pow_smul_boundaryPairPoint (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (hne : ξ ≠ η) (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η) (k : ℕ) :
    (poMulAction hn).smul (g ^ k) (boundaryPairPoint ξ η hne) =
      rayTo (boundaryPairPoint ξ η hne) ξ ((k : ℝ) * Real.log (poConfFactor hn g ξ)) := by
  let := poMulAction hn
  change (g ^ k) • boundaryPairPoint ξ η hne =
    rayTo (boundaryPairPoint ξ η hne) ξ ((k : ℝ) * Real.log (poConfFactor hn g ξ))
  induction k with
  | zero => simp only [pow_zero, one_smul, Nat.cast_zero, zero_mul, rayTo_zero]
  | succ k ih =>
    rw [pow_succ', mul_smul, ih]
    apply (smul_axis_ray hn g ξ η hne hξ hη
      ((k : ℝ) * Real.log (poConfFactor hn g ξ))).trans
    congr 1
    push_cast
    ring

theorem commutes_with_power_of_finite_conjugates {G : Type*} [Group G] (g h : G)
    (hfin : (Set.range (fun k : ℕ => (g ^ k)⁻¹ * h * g ^ k)).Finite) :
    ∃ m : ℕ, 0 < m ∧ h * g ^ m = g ^ m * h := by
  let a : ℕ → G := fun k => (g ^ k)⁻¹ * h * g ^ k
  have hnot : ¬Function.Injective a := by
    intro ha
    let : Finite (Set.range a) := hfin
    exact (Finite.of_injective_finite_range ha).false
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnot
  have step (i j : ℕ) (hij : i < j) (heq : a i = a j) :
      ∃ m : ℕ, 0 < m ∧ h * g ^ m = g ^ m * h := by
    let m := j - i
    have hj : j = m + i := (Nat.sub_add_cancel hij.le).symm
    change (g ^ i)⁻¹ * h * g ^ i = (g ^ j)⁻¹ * h * g ^ j at heq
    rw [hj, pow_add] at heq
    have he := congrArg (fun x : G => g ^ i * x * (g ^ i)⁻¹) heq
    have he' : h = (g ^ m)⁻¹ * h * g ^ m := by
      simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
        mul_inv_cancel, mul_one, one_mul] using he
    refine ⟨m, Nat.sub_pos_of_lt hij, ?_⟩
    have he'' := congrArg (g ^ m * ·) he'
    simpa only [mul_assoc, mul_inv_cancel_left] using he''.symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact step i j h hij
  · exact step j i h hij.symm

theorem exists_ray_displacement_bound (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ) (p : HUpper n) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t) ≤ B := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  change g • ξ = ξ at hξ
  let p' : HUpper n := g • p
  refine ⟨Real.arcosh (max (-lorB p'.val p.val)
    ((lorB p'.val ξ.val / lorB p.val ξ.val + lorB p.val ξ.val / lorB p'.val ξ.val) / 2)),
    fun t ht => ?_⟩
  change dist (g • rayTo p ξ t) (rayTo p ξ t) ≤ _
  have he := BoundaryExtension.po_smul_rayTo hn g p ξ t
  rw [hξ] at he
  rw [he]
  exact dist_rayTo_rayTo_le p' p ξ ht

theorem finite_setOf_displacement_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (p : HUpper n) (B : ℝ) :
    {γ : Γ | dist ((poMulAction hn).smul (γ : PO n 1) p) p ≤ B}.Finite := by
  have hfin := (finite_smallElements hn Γ hΓ (B + 1) p).preimage
    (f := ((↑) : Γ → PO n 1)) Subtype.coe_injective.injOn
  exact hfin.subset (fun γ hγ => ⟨γ.property, hγ.trans_lt (lt_add_one B)⟩)

theorem finite_conjugates_of_scale_gt_one (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (g h : Γ) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hgξ : (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ)
    (hgη : (poBoundaryMulAction hn).smul (g : PO n 1) η = η)
    (hc : 1 < poConfFactor hn (g : PO n 1) ξ)
    (hhξ : (poBoundaryMulAction hn).smul (h : PO n 1) ξ = ξ) :
    (Set.range (fun k : ℕ => (g ^ k)⁻¹ * h * g ^ k)).Finite := by
  let := poMulAction hn
  let p := boundaryPairPoint ξ η hne
  obtain ⟨B, hB⟩ := exists_ray_displacement_bound hn h ξ hhξ p
  apply (finite_setOf_displacement_le hn Γ hΓ p B).subset
  rintro _ ⟨k, rfl⟩
  have ht : 0 ≤ (k : ℝ) * Real.log (poConfFactor hn (g : PO n 1) ξ) :=
    mul_nonneg (Nat.cast_nonneg k) (Real.log_pos hc).le
  calc
    dist (((((g ^ k)⁻¹ * h * g ^ k : Γ) : PO n 1)) • p) p
        = dist p (((((g ^ k)⁻¹ * h * g ^ k : Γ) : PO n 1)) • p) := dist_comm _ _
    _ = dist (((g : PO n 1) ^ k) • p)
        ((h : PO n 1) • (((g : PO n 1) ^ k) • p)) :=
      (LatticeCompactness.displacement_conj hn ((g : PO n 1) ^ k) h p).symm
    _ = dist ((h : PO n 1) •
        rayTo p ξ ((k : ℝ) * Real.log (poConfFactor hn (g : PO n 1) ξ)))
        (rayTo p ξ ((k : ℝ) * Real.log (poConfFactor hn (g : PO n 1) ξ))) := by
      have he := pow_smul_boundaryPairPoint hn g ξ η hne hgξ hgη k
      change (g : PO n 1) ^ k • p =
        rayTo p ξ ((k : ℝ) * Real.log (poConfFactor hn (g : PO n 1) ξ)) at he
      rw [he, dist_comm]
    _ ≤ B := hB _ ht

theorem exists_second_fixed_of_scale_gt_one (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (ξ : BoundaryH n)
    (hfix : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ)
    (g : Γ) (hc : 1 < poConfFactor hn (g : PO n 1) ξ) :
    ∃ η : BoundaryH n, η ≠ ξ ∧
      ∀ h : Γ, (poBoundaryMulAction hn).smul (h : PO n 1) η = η := by
  let := poBoundaryMulAction hn
  obtain ⟨η, hηne, hgη, _⟩ :=
    exists_exactly_two_fixed_of_scale_ne_one hn g ξ (hfix g) hc.ne'
  refine ⟨η, hηne, fun h => ?_⟩
  obtain ⟨m, hm, hcomm⟩ := commutes_with_power_of_finite_conjugates g h
    (finite_conjugates_of_scale_gt_one hn Γ hΓ g h ξ η hηne.symm (hfix g) hgη hc (hfix h))
  have hcomm' : (h : PO n 1) * (g : PO n 1) ^ m = (g : PO n 1) ^ m * (h : PO n 1) :=
    congrArg Subtype.val hcomm
  have hgmξ := boundary_pow_fixed hn g ξ (hfix g) m
  have hgmη := boundary_pow_fixed hn g η hgη m
  change (g : PO n 1) ^ m • η = η at hgmη
  have hscale : poConfFactor hn ((g : PO n 1) ^ m) ξ ≠ 1 := by
    rw [poConfFactor_pow_of_fixed hn g ξ (hfix g) m]
    exact (one_lt_pow₀ hc hm.ne').ne'
  obtain ⟨η', _, _, hclass⟩ :=
    exists_exactly_two_fixed_of_scale_ne_one hn ((g : PO n 1) ^ m) ξ hgmξ hscale
  have hηeq : η = η' := (hclass η hgmη).resolve_left hηne
  have hhη : (g : PO n 1) ^ m • ((h : PO n 1) • η) = (h : PO n 1) • η := by
    rw [← mul_smul, ← hcomm', mul_smul, hgmη]
  have hhηne : (h : PO n 1) • η ≠ ξ := by
    intro he
    apply hηne
    apply (MulAction.toPerm (h : PO n 1)).injective
    exact he.trans (hfix h).symm
  exact ((hclass _ hhη).resolve_left hhηne).trans hηeq.symm

theorem boundary_stabilizer_dichotomy (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (ξ : BoundaryH n)
    (hfix : ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) :
    (∃ η : BoundaryH n, η ≠ ξ ∧
      ∀ γ : Γ, (poBoundaryMulAction hn).smul (γ : PO n 1) η = η) ∨
    ((∀ γ : Γ, poConfFactor hn (γ : PO n 1) ξ = 1) ∧
      ∀ (γ : Γ) (x : HUpper n),
        busemann ξ ((poMulAction hn).smul (γ : PO n 1) x) = busemann ξ x) := by
  by_cases hscale : ∀ γ : Γ, poConfFactor hn (γ : PO n 1) ξ = 1
  · refine Or.inr ⟨hscale, fun γ x => ?_⟩
    have h := po_busemann_smul hn γ ξ x
    rwa [hfix γ, hscale γ, Real.log_one, sub_zero] at h
  · obtain ⟨g, hg⟩ := not_forall.mp hscale
    apply Or.inl
    by_cases hgt : 1 < poConfFactor hn (g : PO n 1) ξ
    · exact exists_second_fixed_of_scale_gt_one hn Γ hΓ ξ hfix g hgt
    · apply exists_second_fixed_of_scale_gt_one hn Γ hΓ ξ hfix g⁻¹
      change 1 < poConfFactor hn (g : PO n 1)⁻¹ ξ
      rw [poConfFactor_inv_of_fixed hn g ξ (hfix g)]
      apply (one_lt_inv₀ (poConfFactor_pos hn g ξ)).mpr
      exact lt_of_le_of_ne (le_of_not_gt hgt) hg

def ElementaryGeometry (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) : Prop :=
  (Finite Γ ∧ ∃ p : HUpper n, ∀ γ : Γ, (poMulAction hn).smul (γ : PO n 1) p = p) ∨
  (∃ ξ η : BoundaryH n, ξ ≠ η ∧ ∀ γ : Γ,
    (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
    (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n))) ∨
  (∃ ξ : BoundaryH n, ∀ γ : Γ,
    (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧ poConfFactor hn (γ : PO n 1) ξ = 1)

theorem elementary_geometry (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (helem : IsElementary hn Γ) :
    ElementaryGeometry hn Γ := by
  rcases finite_or_infinite Γ with hfinite | hinfinite
  · let := hfinite
    let := Fintype.ofFinite Γ
    obtain ⟨p, hp, _⟩ := EquivariantMap.exists_fixed_point_of_finite_subgroup hn Γ
    exact Or.inl ⟨hfinite, p, fun γ => hp γ γ.property⟩
  · let := hinfinite
    rcases helem with ⟨hfinite, _⟩ | ⟨ξ, hξfin, _⟩
    · exact hfinite.false.elim
    · rcases fixed_point_or_pair_of_finite_boundaryOrbit hn Γ hΓ hξfin with ⟨u, hu⟩ | hpair
      · rcases boundary_stabilizer_dichotomy hn Γ hΓ u hu with ⟨v, hvne, hv⟩ | ⟨hscale, _⟩
        · refine Or.inr (Or.inl ⟨u, v, hvne.symm, fun γ => ?_⟩)
          simp only [hu γ, hv γ, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
            or_true, and_self]
        · exact Or.inr (Or.inr ⟨u, fun γ => ⟨hu γ, hscale γ⟩⟩)
      · exact Or.inr (Or.inl hpair)

theorem smallSubgroup_geometry (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n)
    (hvirt : Group.IsVirtuallyNilpotent (Margulis.smallSubgroup hn Γ ε x)) :
    ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x) :=
  elementary_geometry hn _ (hΓ.mono (Margulis.smallSubgroup_le hn Γ ε x))
    (isElementary_smallSubgroup hn Γ hΓ ε x hvirt)

theorem exists_margulis_geometry_constant (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x) := by
  obtain ⟨ε, hε, hMargulis⟩ := Margulis.exists_margulis_constant hn
  exact ⟨ε, hε, fun Γ hΓ x => smallSubgroup_geometry hn Γ hΓ ε x (hMargulis Γ hΓ x)⟩

theorem poConfFactor_eq_one_on_parabolic_stabilizer (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (g : Γ) (ξ : BoundaryH n)
    (hg : (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (g : PO n 1) η = η → η = ξ)
    (h : Γ) (hh : (poBoundaryMulAction hn).smul (h : PO n 1) ξ = ξ) :
    poConfFactor hn (h : PO n 1) ξ = 1 := by
  let := poBoundaryMulAction hn
  let H := Γ ⊓ MulAction.stabilizer (PO n 1) ξ
  have hH : IsDiscrete (SetLike.coe H) := hΓ.mono inf_le_left
  have hHfix (a : H) : (poBoundaryMulAction hn).smul (a : PO n 1) ξ = ξ := a.property.2
  rcases boundary_stabilizer_dichotomy hn H hH ξ hHfix with ⟨η, hηne, hη⟩ | ⟨hscale, _⟩
  · exact (hηne (hunique η (hη ⟨g, g.property, hg⟩))).elim
  · exact hscale ⟨h, h.property, hh⟩

theorem busemann_smul_on_parabolic_stabilizer (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    (g : Γ) (ξ : BoundaryH n)
    (hg : (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ)
    (hunique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul (g : PO n 1) η = η → η = ξ)
    (h : Γ) (hh : (poBoundaryMulAction hn).smul (h : PO n 1) ξ = ξ) (x : HUpper n) :
    busemann ξ ((poMulAction hn).smul (h : PO n 1) x) = busemann ξ x := by
  have he := po_busemann_smul hn h ξ x
  rwa [hh, poConfFactor_eq_one_on_parabolic_stabilizer hn Γ hΓ g ξ hg hunique h hh,
    Real.log_one, sub_zero] at he

end DifferentialGeometry.BoundaryStabilizer
