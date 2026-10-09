import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# A finite central quotient and finite abelianization force finiteness

Commutators depend only on the cosets modulo the centre. A finite central quotient therefore
has finitely many commutators; Schur's theorem makes the derived subgroup finite. Finiteness
of the abelianization then gives finiteness of the original group. This separates the group
argument from the actual carrier and Euler identifications still needed for a closed block.
-/

set_option autoImplicit false
noncomputable section
open scoped commutatorElement
universe u
namespace GC.Seifert

variable {G : Type u} [Group G]

private theorem commutator_eq_of_central_left {a a' b : G}
    (h : a⁻¹ * a' ∈ Subgroup.center G) : ⁅a, b⁆ = ⁅a', b⁆ := by
  have hz : Commute (a⁻¹ * a') b :=
    (Subgroup.mem_center_iff.mp h b).symm
  have ha : a' = a * (a⁻¹ * a') := by simp
  conv_rhs => rw [ha]
  rw [commutatorElement_mul_left_eq_conj_mul, hz.commutator_eq]
  simp

private theorem commutator_eq_of_central_right {a b b' : G}
    (h : b⁻¹ * b' ∈ Subgroup.center G) : ⁅a, b⁆ = ⁅a, b'⁆ := by
  have hz : Commute a (b⁻¹ * b') := Subgroup.mem_center_iff.mp h a
  have hb : b' = b * (b⁻¹ * b') := by simp
  conv_rhs => rw [hb]
  rw [commutatorElement_mul_right_eq_mul_conj, hz.commutator_eq]
  simp

theorem finite_commutatorSet_of_finite_centerQuotient
    [Finite (G ⧸ Subgroup.center G)] : Finite (commutatorSet G) := by
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → commutatorSet G :=
    fun q => ⟨⁅q.1.out, q.2.out⁆, commutator_mem_commutatorSet _ _⟩
  apply Finite.of_surjective f
  intro c
  obtain ⟨a, b, hab⟩ := c.property
  refine ⟨(QuotientGroup.mk a, QuotientGroup.mk b), Subtype.ext ?_⟩
  change ⁅(QuotientGroup.mk a : G ⧸ Subgroup.center G).out,
    (QuotientGroup.mk b : G ⧸ Subgroup.center G).out⁆ = c.val
  rw [← hab]
  have ha : (QuotientGroup.mk a : G ⧸ Subgroup.center G).out⁻¹ * a ∈
      Subgroup.center G := QuotientGroup.eq.mp (Quotient.out_eq' _)
  have hb : (QuotientGroup.mk b : G ⧸ Subgroup.center G).out⁻¹ * b ∈
      Subgroup.center G := QuotientGroup.eq.mp (Quotient.out_eq' _)
  exact (commutator_eq_of_central_left ha).trans (commutator_eq_of_central_right hb)

theorem finite_of_finite_centerQuotient_abelianization
    [Finite (G ⧸ Subgroup.center G)] [Finite (Abelianization G)] : Finite G := by
  have := finite_commutatorSet_of_finite_centerQuotient (G := G)
  have : Finite (commutator G) := inferInstance
  have : Finite (G ⧸ commutator G) := ‹Finite (Abelianization G)›
  exact Finite.of_subgroup_quotient (commutator G)

theorem finite_of_finite_centralQuotient_abelianization (H : Subgroup G)
    (hH : H ≤ Subgroup.center G) [Finite (G ⧸ H)] [Finite (Abelianization G)] : Finite G := by
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : (Subgroup.center G).FiniteIndex := Subgroup.finiteIndex_of_le hH
  exact finite_of_finite_centerQuotient_abelianization

theorem finite_of_finite_fibreQuotient_abelianization (z : G)
    (hz : ∀ g, g * z = z * g) [Finite (G ⧸ Subgroup.zpowers z)]
    [Finite (Abelianization G)] : Finite G := by
  apply finite_of_finite_centralQuotient_abelianization (Subgroup.zpowers z)
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hz)

end GC.Seifert
