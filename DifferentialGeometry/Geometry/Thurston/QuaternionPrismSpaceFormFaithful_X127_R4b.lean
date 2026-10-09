import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismFaithful_X127_R7b

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismFaithfulX127

namespace GC.Geometry.QuaternionPrismSpaceFormFaithfulX127

local notation "UQ" => unitary (Quaternion ℝ)

def prismSpaceFormGroupEquiv_X127 (n : ℕ) [NeZero n] :
    QuaternionGroup n ≃* (spaceForm_X127 n).group :=
  (MonoidHom.ofInjective (hom_injective_X127 n)).trans
    (quaternionLeftSpaceFormEquiv ((hom_X127 n).range))

theorem prismSpaceFormGroup_card_X127 (n : ℕ) [NeZero n] :
    Nat.card (spaceForm_X127 n).group = 4 * n := by
  rw [← Nat.card_congr (prismSpaceFormGroupEquiv_X127 n).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem prismSpaceForm_noncommutative_X127 (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    ∃ a b : (spaceForm_X127 n).group, a * b ≠ b * a := by
  refine ⟨prismSpaceFormGroupEquiv_X127 n (.a 1),
    prismSpaceFormGroupEquiv_X127 n (.xa 0), ?_⟩
  intro h
  have hne : (QuaternionGroup.a 1 : QuaternionGroup n) * .xa 0 ≠
      .xa 0 * .a 1 := by
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
    intro hz
    have hindex := congrArg (fun q : QuaternionGroup n =>
      match q with
      | .a i => i
      | .xa i => i) hz
    have htwo : (2 : ZMod (2 * n)) = 0 := by
      have ht := congrArg (fun z : ZMod (2 * n) => z + 1) hindex
      norm_num at ht
      exact ht.symm
    have hdiv : 2 * n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp htwo
    have hbound : 2 ≤ 2 * n := by omega
    have := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have he := (prismSpaceFormGroupEquiv_X127 n).injective
    ((prismSpaceFormGroupEquiv_X127 n).map_mul _ _ |>.trans
      (h.trans ((prismSpaceFormGroupEquiv_X127 n).map_mul _ _).symm))
  exact hne he

end GC.Geometry.QuaternionPrismSpaceFormFaithfulX127
