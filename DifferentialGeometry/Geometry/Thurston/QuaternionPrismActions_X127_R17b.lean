import DifferentialGeometry.Geometry.Thurston.QuaternionSphereActions
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry
open scoped Real

namespace GC.Geometry.QuaternionPrismX127R3

local notation "QH" => Quaternion ℝ
local notation "UQ" => unitary (Quaternion ℝ)

def rootComplex_X127 (n : ℕ) : ℂ :=
  Complex.exp (Real.pi * Complex.I / (n : ℝ))

private theorem coeComplex_pow_X127 (z : ℂ) (k : ℕ) :
    (z : QH) ^ k = ((z ^ k : ℂ) : QH) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, Quaternion.coeComplex_mul]

theorem rootComplex_primitive_X127 (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (rootComplex_X127 n) (2 * n) := by
  have hzero : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) (NeZero.ne n)
  have h := Complex.isPrimitiveRoot_exp (2 * n) hzero
  have harg :
      (Real.pi * Complex.I : ℂ) / (n : ℝ) =
        (2 * Real.pi * Complex.I : ℂ) / (2 * n : ℕ) := by
    push_cast
    field_simp [NeZero.ne n]
  change IsPrimitiveRoot (Complex.exp ((Real.pi * Complex.I : ℂ) / (n : ℝ))) (2 * n)
  rw [harg]
  exact h

theorem rootComplex_norm_X127 (n : ℕ) [NeZero n] :
    ‖rootComplex_X127 n‖ = 1 := by
  rw [rootComplex_X127]
  have harg : (Real.pi * Complex.I : ℂ) / (n : ℝ) =
      ((Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    field_simp [hn]
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I (Real.pi / (n : ℝ))

theorem rootComplex_pow_n_X127 (n : ℕ) [NeZero n] :
    rootComplex_X127 n ^ n = -1 := by
  rw [rootComplex_X127, ← Complex.exp_nat_mul]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have harg : (n : ℂ) * ((Real.pi * Complex.I : ℂ) / (n : ℝ)) =
      (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp [hn]
  rw [harg, Complex.exp_pi_mul_I]

def rootUnit_X127 (n : ℕ) [NeZero n] : ℂˣ :=
  Units.mk0 (rootComplex_X127 n) (by
    intro h
    have hn := congrArg norm h
    rw [rootComplex_norm_X127, norm_zero] at hn
    norm_num at hn)

theorem rootUnit_primitive_X127 (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (rootUnit_X127 n) (2 * n) := by
  have hplain : IsPrimitiveRoot ((rootUnit_X127 n : ℂˣ) : ℂ) (2 * n) := by
    simpa [rootUnit_X127] using rootComplex_primitive_X127 n
  exact (IsPrimitiveRoot.coe_units_iff (ζ := rootUnit_X127 n)).mp hplain

noncomputable def characterSubgroup_X127 (n : ℕ) [NeZero n]
    (i : ZMod (2 * n)) : Subgroup.zpowers (rootUnit_X127 n) :=
  ((rootUnit_primitive_X127 n).zmodEquivZPowers i).toMul

def characterComplex_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) : ℂˣ :=
  characterSubgroup_X127 n i

theorem characterComplex_add_X127 (n : ℕ) [NeZero n] (i k : ZMod (2 * n)) :
    characterComplex_X127 n (i + k) =
      characterComplex_X127 n i * characterComplex_X127 n k := by
  simp [characterComplex_X127, characterSubgroup_X127]

theorem characterComplex_neg_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) :
    characterComplex_X127 n (-i) = (characterComplex_X127 n i)⁻¹ := by
  simp [characterComplex_X127, characterSubgroup_X127]

theorem characterComplex_zero_X127 (n : ℕ) [NeZero n] :
    characterComplex_X127 n 0 = 1 := by
  simp [characterComplex_X127, characterSubgroup_X127]

theorem characterComplex_natCast_X127 (n : ℕ) [NeZero n] (k : ℕ) :
    characterComplex_X127 n (k : ZMod (2 * n)) = (rootUnit_X127 n) ^ k := by
  simp [characterComplex_X127, characterSubgroup_X127,
    IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]

private theorem characterComplex_mem_roots_X127 (n : ℕ) [NeZero n]
    (i : ZMod (2 * n)) : characterComplex_X127 n i ∈ rootsOfUnity (2 * n) ℂ := by
  rw [← (rootUnit_primitive_X127 n).zpowers_eq]
  exact (characterSubgroup_X127 n i).property

theorem characterComplex_norm_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) :
    ‖((characterComplex_X127 n i : ℂˣ) : ℂ)‖ = 1 :=
  Complex.norm_eq_one_of_mem_rootsOfUnity (characterComplex_mem_roots_X127 n i)

def characterQ_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) : UQ :=
  ⟨((characterComplex_X127 n i : ℂˣ) : QH), by
    rw [Unitary.mem_iff]
    have hnormSq :
        Quaternion.normSq ((characterComplex_X127 n i : ℂˣ) : QH) = 1 := by
      calc
        Quaternion.normSq ((characterComplex_X127 n i : ℂˣ) : QH) =
            Complex.normSq ((characterComplex_X127 n i : ℂˣ) : ℂ) := by
          rw [Quaternion.normSq_def']
          simp only [Quaternion.re_coeComplex, Quaternion.imI_coeComplex,
            Quaternion.imJ_coeComplex, Quaternion.imK_coeComplex]
          rw [Complex.normSq_apply]
          ring
        _ = ‖((characterComplex_X127 n i : ℂˣ) : ℂ)‖ ^ 2 :=
          Complex.normSq_eq_norm_sq _
        _ = 1 := by rw [characterComplex_norm_X127]; norm_num
    exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
      by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩

theorem characterQ_add_X127 (n : ℕ) [NeZero n] (i k : ZMod (2 * n)) :
    characterQ_X127 n (i + k) = characterQ_X127 n i * characterQ_X127 n k := by
  apply Subtype.ext
  simp [characterQ_X127, characterComplex_add_X127, Quaternion.coeComplex_mul]

theorem characterQ_zero_X127 (n : ℕ) [NeZero n] :
    characterQ_X127 n 0 = 1 := by
  apply Subtype.ext
  simp [characterQ_X127, characterComplex_zero_X127]

theorem characterQ_natCast_X127 (n : ℕ) [NeZero n] (k : ℕ) :
    characterQ_X127 n (k : ZMod (2 * n)) =
      (⟨(rootComplex_X127 n : QH), by
        rw [Unitary.mem_iff]
        have hnormSq : Quaternion.normSq (rootComplex_X127 n : QH) = 1 := by
          calc
            Quaternion.normSq (rootComplex_X127 n : QH) =
                Complex.normSq (rootComplex_X127 n) := by
              rw [Quaternion.normSq_def']
              simp only [Quaternion.re_coeComplex, Quaternion.imI_coeComplex,
                Quaternion.imJ_coeComplex, Quaternion.imK_coeComplex]
              rw [Complex.normSq_apply]
              ring
            _ = ‖rootComplex_X127 n‖ ^ 2 := Complex.normSq_eq_norm_sq _
            _ = 1 := by rw [rootComplex_norm_X127]; norm_num
        exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
          by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩ : UQ) ^ k := by
  apply Subtype.ext
  change ((characterComplex_X127 n (k : ZMod (2 * n)) : ℂˣ) : QH) =
      ((rootComplex_X127 n : QH) ^ k)
  rw [characterComplex_natCast_X127]
  change Quaternion.ofComplex (rootComplex_X127 n ^ k) =
    (Quaternion.ofComplex (rootComplex_X127 n) : QH) ^ k
  exact (Quaternion.ofComplex).map_pow _ _

def alpha_X127 (n : ℕ) [NeZero n] : UQ := characterQ_X127 n 1

theorem alpha_pow_n_X127 (n : ℕ) [NeZero n] :
    ((alpha_X127 n ^ n : UQ) : QH) = -1 := by
  have hroot : alpha_X127 n =
      (⟨(rootComplex_X127 n : QH), by
        rw [Unitary.mem_iff]
        have hnormSq : Quaternion.normSq (rootComplex_X127 n : QH) = 1 := by
          calc
            Quaternion.normSq (rootComplex_X127 n : QH) =
                Complex.normSq (rootComplex_X127 n) := by
              rw [Quaternion.normSq_def']
              simp only [Quaternion.re_coeComplex, Quaternion.imI_coeComplex,
                Quaternion.imJ_coeComplex, Quaternion.imK_coeComplex]
              rw [Complex.normSq_apply]
              ring
            _ = ‖rootComplex_X127 n‖ ^ 2 := Complex.normSq_eq_norm_sq _
            _ = 1 := by rw [rootComplex_norm_X127]; norm_num
        exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
          by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩ : UQ) := by
    simpa [alpha_X127] using characterQ_natCast_X127 n 1
  rw [hroot]
  simp only [SubmonoidClass.coe_pow]
  change (rootComplex_X127 n : QH) ^ n = (-1 : QH)
  have hpow : (rootComplex_X127 n : QH) ^ n =
      ((rootComplex_X127 n ^ n : ℂ) : QH) := by
    exact coeComplex_pow_X127 (rootComplex_X127 n) n
  have hlast : ((rootComplex_X127 n ^ n : ℂ) : QH) = (-1 : QH) := by
    rw [rootComplex_pow_n_X127]
    simpa using Quaternion.coeComplex_coe (-1 : ℝ)
  exact hpow.trans hlast

private def jValue_X127 : QH := ⟨0, 0, 1, 0⟩

def jUnit_X127 : UQ :=
  ⟨jValue_X127, by
    rw [Unitary.mem_iff]
    have hnormSq : Quaternion.normSq jValue_X127 = 1 := by
      rw [Quaternion.normSq_def']
      norm_num [jValue_X127]
    exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
      by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩

theorem jUnit_sq_X127 (n : ℕ) [NeZero n] :
    jUnit_X127 * jUnit_X127 = alpha_X127 n ^ n := by
  apply Subtype.ext
  calc
    jValue_X127 * jValue_X127 = -1 := by
      apply Quaternion.ext <;> norm_num [jValue_X127]
    _ = ((alpha_X127 n ^ n : UQ) : QH) := (alpha_pow_n_X127 n).symm

theorem alpha_pow_eq_character_n_X127 (n : ℕ) [NeZero n] :
    alpha_X127 n ^ n = characterQ_X127 n (n : ZMod (2 * n)) := by
  calc
    alpha_X127 n ^ n =
        (⟨(rootComplex_X127 n : QH), by
          rw [Unitary.mem_iff]
          have hnormSq : Quaternion.normSq (rootComplex_X127 n : QH) = 1 := by
            calc
              Quaternion.normSq (rootComplex_X127 n : QH) =
                  Complex.normSq (rootComplex_X127 n) := by
                rw [Quaternion.normSq_def']
                simp only [Quaternion.re_coeComplex, Quaternion.imI_coeComplex,
                  Quaternion.imJ_coeComplex, Quaternion.imK_coeComplex]
                rw [Complex.normSq_apply]
                ring
              _ = ‖rootComplex_X127 n‖ ^ 2 := Complex.normSq_eq_norm_sq _
              _ = 1 := by rw [rootComplex_norm_X127]; norm_num
          exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
            by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩ : UQ) ^ n := by
      have hroot : alpha_X127 n =
          (⟨(rootComplex_X127 n : QH), by
            rw [Unitary.mem_iff]
            have hnormSq : Quaternion.normSq (rootComplex_X127 n : QH) = 1 := by
              calc
                Quaternion.normSq (rootComplex_X127 n : QH) =
                    Complex.normSq (rootComplex_X127 n) := by
                  rw [Quaternion.normSq_def']
                  simp only [Quaternion.re_coeComplex, Quaternion.imI_coeComplex,
                    Quaternion.imJ_coeComplex, Quaternion.imK_coeComplex]
                  rw [Complex.normSq_apply]
                  ring
                _ = ‖rootComplex_X127 n‖ ^ 2 := Complex.normSq_eq_norm_sq _
                _ = 1 := by rw [rootComplex_norm_X127]; norm_num
            exact ⟨by rw [Quaternion.star_mul_self, hnormSq]; rfl,
              by rw [Quaternion.self_mul_star, hnormSq]; rfl⟩⟩ : UQ) := by
        simpa [alpha_X127] using characterQ_natCast_X127 n 1
      rw [hroot]
    _ = characterQ_X127 n (n : ZMod (2 * n)) := by
      symm
      simpa using characterQ_natCast_X127 n n

private theorem j_conj_complex_X127 (z : ℂ) :
    jValue_X127 * (z : QH) * star jValue_X127 = (star z : QH) := by
  apply Quaternion.ext <;> simp [jValue_X127, Quaternion.coeComplex]

theorem j_conj_character_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) :
    jUnit_X127 * characterQ_X127 n i * jUnit_X127⁻¹ =
      characterQ_X127 n (-i) := by
  apply Subtype.ext
  change jValue_X127 * ((characterComplex_X127 n i : ℂˣ) : QH) *
      star jValue_X127 = ((characterComplex_X127 n (-i) : ℂˣ) : QH)
  rw [j_conj_complex_X127, characterComplex_neg_X127]
  have hnormSq : Complex.normSq ((characterComplex_X127 n i : ℂˣ) : ℂ) = 1 := by
    calc
      Complex.normSq ((characterComplex_X127 n i : ℂˣ) : ℂ) =
          ‖((characterComplex_X127 n i : ℂˣ) : ℂ)‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      _ = 1 := by rw [characterComplex_norm_X127]; norm_num
  apply Quaternion.ext <;> simp [Quaternion.coeComplex, hnormSq]

theorem characterQ_mul_j_X127 (n : ℕ) [NeZero n] (i : ZMod (2 * n)) :
    characterQ_X127 n i * jUnit_X127 =
      jUnit_X127 * characterQ_X127 n (-i) := by
  have h := j_conj_character_X127 n (-i)
  have hneg : -(-i) = i := by abel
  rw [hneg] at h
  calc
    characterQ_X127 n i * jUnit_X127 =
        (jUnit_X127 * characterQ_X127 n (-i) * jUnit_X127⁻¹) * jUnit_X127 := by
      rw [h]
    _ = jUnit_X127 * characterQ_X127 n (-i) := by group

def value_X127 (n : ℕ) [NeZero n] : QuaternionGroup n → UQ
  | .a i => characterQ_X127 n i
  | .xa i => jUnit_X127 * characterQ_X127 n i

def hom_X127 (n : ℕ) [NeZero n] : QuaternionGroup n →* UQ where
  toFun := value_X127 n
  map_one' := by
    rw [QuaternionGroup.one_def]
    exact characterQ_zero_X127 n
  map_mul' q r := by
    rcases q with i | i <;> rcases r with k | k
    · simpa [value_X127, QuaternionGroup.a_mul_a] using characterQ_add_X127 n i k
    · rw [QuaternionGroup.a_mul_xa, value_X127]
      symm
      calc
        characterQ_X127 n i * (jUnit_X127 * characterQ_X127 n k) =
            (characterQ_X127 n i * jUnit_X127) * characterQ_X127 n k := by
          rw [mul_assoc]
        _ = (jUnit_X127 * characterQ_X127 n (-i)) * characterQ_X127 n k := by
          rw [characterQ_mul_j_X127]
        _ = jUnit_X127 * characterQ_X127 n (k - i) := by
          rw [mul_assoc, ← characterQ_add_X127]
          congr 2
          abel
    · rw [QuaternionGroup.xa_mul_a, value_X127]
      symm
      calc
        (jUnit_X127 * characterQ_X127 n i) * characterQ_X127 n k =
            jUnit_X127 * (characterQ_X127 n i * characterQ_X127 n k) := by
          rw [← mul_assoc]
        _ = jUnit_X127 * characterQ_X127 n (i + k) := by
          rw [characterQ_add_X127]
    · rw [QuaternionGroup.xa_mul_xa, value_X127]
      symm
      calc
        (jUnit_X127 * characterQ_X127 n i) *
            (jUnit_X127 * characterQ_X127 n k) =
          (jUnit_X127 * jUnit_X127) *
            (characterQ_X127 n (-i) * characterQ_X127 n k) := by
          calc
            (jUnit_X127 * characterQ_X127 n i) *
                (jUnit_X127 * characterQ_X127 n k) =
              ((jUnit_X127 * characterQ_X127 n i) * jUnit_X127) *
                characterQ_X127 n k := by group
            _ = (jUnit_X127 *
                (characterQ_X127 n i * jUnit_X127)) *
                characterQ_X127 n k := by rw [← mul_assoc]
            _ = (jUnit_X127 *
                (jUnit_X127 * characterQ_X127 n (-i))) *
                characterQ_X127 n k := by rw [characterQ_mul_j_X127]
            _ = (jUnit_X127 * jUnit_X127) *
                (characterQ_X127 n (-i) * characterQ_X127 n k) := by group
        _ = characterQ_X127 n (n : ZMod (2 * n)) *
            (characterQ_X127 n (-i) * characterQ_X127 n k) := by
          rw [jUnit_sq_X127 n, alpha_pow_eq_character_n_X127 n]
        _ = characterQ_X127 n (n + ((-i) + k)) := by
          rw [← characterQ_add_X127, ← characterQ_add_X127]
        _ = characterQ_X127 n (n + k - i) := by congr 2; abel

private instance instHomRangeFinite_X127 (n : ℕ) [NeZero n] :
    Finite (hom_X127 n).range :=
  Finite.of_surjective (hom_X127 n).rangeRestrict (hom_X127 n).rangeRestrict_surjective

def spaceForm_X127 (n : ℕ) [NeZero n] : SphericalSpaceFormGroup :=
  quaternionLeftSpaceForm (hom_X127 n).range

end GC.Geometry.QuaternionPrismX127R3
