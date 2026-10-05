import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LensGroup
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
Primitive circle roots are standard additive characters at units of ZMod. Rescaling the generator
normalizes the first multiplier and retains the actual subgroup of the two-coordinate lens action.
-/

set_option autoImplicit false

noncomputable section

open GC.Seifert

namespace GC.Geometry.SphericalCyclic

theorem exists_coprime_toCircle (p : ℕ) [NeZero p] (u : Circle)
    (hu : IsPrimitiveRoot u p) : ∃ a : ℕ, a.Coprime p ∧ ZMod.toCircle (a : ZMod p) = u := by
  obtain ⟨a, ha⟩ := (bijective_rootsOfUnityAddChar p).surjective hu.toRootsOfUnity
  have hcircle := congrArg (fun x : rootsOfUnity p Circle => (x.val : Circle)) ha
  change ZMod.toCircle a = u at hcircle
  have hi : Function.Injective (ZMod.toCircle (N := p)).toMonoidHom := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    exact ZMod.injective_toCircle hxy
  have ho := orderOf_injective (ZMod.toCircle (N := p)).toMonoidHom hi
    (Multiplicative.ofAdd a)
  change orderOf (ZMod.toCircle a) = addOrderOf a at ho
  rw [hcircle, ← hu.eq_orderOf] at ho
  have hdiv : p / p.gcd a.val = p := by
    rw [← ZMod.addOrderOf_coe a.val (NeZero.ne p), ZMod.natCast_zmod_val]
    exact ho.symm
  have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left p a.val)
  rw [hdiv] at hmul
  have hg : p.gcd a.val = 1 := Nat.mul_left_cancel (NeZero.pos p) (by simpa using hmul)
  refine ⟨a.val, ?_, ?_⟩
  · exact (Nat.coprime_iff_gcd_eq_one.mpr hg).symm
  · simpa only [ZMod.natCast_zmod_val] using hcircle


theorem lensPairRotation_zpowers_of_primitive_roots (p : ℕ) [NeZero p] (u v : Circle)
    (hu : IsPrimitiveRoot u p) (hv : IsPrimitiveRoot v p) :
    ∃ q : ℤ, ∃ hpq : IsCoprime (p : ℤ) q,
      Subgroup.zpowers (lensPairRotation u v) = (lensSpaceFormGroup p q hpq).group := by
  obtain ⟨a, ha, hua⟩ := exists_coprime_toCircle p u hu
  obtain ⟨b, hb, hvb⟩ := exists_coprime_toCircle p v hv
  let ua : (ZMod p)ˣ := ((ZMod.isUnit_iff_coprime a p).mpr ha).unit
  let ub : (ZMod p)ˣ := ((ZMod.isUnit_iff_coprime b p).mpr hb).unit
  have hau : (ua : ZMod p) = (a : ZMod p) := IsUnit.unit_spec _
  have hub : (ub : ZMod p) = (b : ZMod p) := IsUnit.unit_spec _
  let r := ub * ua⁻¹
  let q : ℤ := (r : ZMod p).val
  have hq : (q : ZMod p) = r := by
    simpa only [q, Int.cast_natCast] using ZMod.natCast_zmod_val (r : ZMod p)
  have hpq : IsCoprime (p : ℤ) q := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa only [Int.natAbs_natCast, q] using (ZMod.val_coe_unit_coprime r).symm
  have hqa : (q : ZMod p) * (a : ZMod p) = (b : ZMod p) := by
    rw [hq, ← hau, ← hub]
    simp [r]
  have haction : lensSpaceFormAction p q (Multiplicative.ofAdd (a : ZMod p)) =
      lensPairRotation u v := by
    rw [lensSpaceFormAction_apply, toAdd_ofAdd, hqa, hua, hvb]
  have hfirst : Subgroup.zpowers (lensPairRotation u v) ≤
      (lensSpaceFormGroup p q hpq).group := by
    apply Subgroup.zpowers_le.mpr
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (a : ZMod p), haction⟩
  let i := (ua⁻¹ : ZMod p).val
  have hia : (i : ZMod p) * (a : ZMod p) = 1 := by
    rw [show (i : ZMod p) = (ua⁻¹ : ZMod p) from ZMod.natCast_zmod_val _, ← hau]
    simp
  have hib : (i : ZMod p) * (b : ZMod p) = (q : ZMod p) := by
    rw [show (i : ZMod p) = (ua⁻¹ : ZMod p) from ZMod.natCast_zmod_val _, ← hub, hq]
    simp [r, mul_comm]
  have hpair (n : ℕ) :
      (lensPairRotation u v) ^ n = lensPairRotation (u ^ n) (v ^ n) := by
    induction n with
    | zero => simpa using lensPairRotation_one.symm
    | succ n hn => rw [pow_succ, hn, pow_succ, pow_succ, lensPairRotation_mul]
  have hstandard : (lensPairRotation u v) ^ i =
      lensSpaceFormAction p q (Multiplicative.ofAdd 1) := by
    rw [hpair, ← hua, ← hvb,
      ← AddChar.map_nsmul_eq_pow (ZMod.toCircle (N := p)) i (a : ZMod p),
      ← AddChar.map_nsmul_eq_pow (ZMod.toCircle (N := p)) i (b : ZMod p),
      nsmul_eq_mul, nsmul_eq_mul, hia, hib]
    simp only [lensSpaceFormAction_apply, toAdd_ofAdd, mul_one]
  refine ⟨q, hpq, le_antisymm hfirst ?_⟩
  rw [lensSpaceFormGroup_group_eq_zpowers]
  apply Subgroup.zpowers_le.mpr
  rw [← hstandard]
  exact (Subgroup.zpowers (lensPairRotation u v)).pow_mem
    (Subgroup.mem_zpowers (lensPairRotation u v)) i

end GC.Geometry.SphericalCyclic
