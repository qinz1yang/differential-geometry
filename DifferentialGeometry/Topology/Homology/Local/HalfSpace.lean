import DifferentialGeometry.Topology.Homology.Local.Euclidean
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
namespace DifferentialGeometry.Homology
variable {n : ℕ} [NeZero n] (p : EuclideanHalfSpace n)


def puncturedHalfSpaceHomeomorph :
    ({p}ᶜ : Set (EuclideanHalfSpace n)) ≃ₜ
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _


theorem contractibleSpace_euclideanHalfSpace : ContractibleSpace (EuclideanHalfSpace n) :=
  EuclideanHalfSpace.convex.contractibleSpace ⟨0, by simp⟩


theorem contractibleSpace_puncturedHalfSpace (hp : p.val 0 = 0) :
    ContractibleSpace ({p}ᶜ : Set (EuclideanHalfSpace n)) := by
  let c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hc : c 0 = 1 := rfl
  have hcS : c ∈ {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} := by
    refine ⟨by rw [hc]; norm_num, ?_⟩
    intro h
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) h
    rw [hc, hp] at he
    norm_num at he
  have hs : StarConvex ℝ c {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} := by
    intro y hy a b ha hb hab
    have he : (a • c + b • y) 0 = a + b * y 0 := by
      simp [hc]
    refine ⟨by rw [he]; exact add_nonneg ha (mul_nonneg hb hy.1), ?_⟩
    by_cases haz : a = 0
    · have hb1 : b = 1 := by linarith
      simpa only [haz, hb1, zero_smul, one_smul, zero_add] using hy.2
    · intro h
      have hh := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) h
      rw [he, hp] at hh
      have : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      have : 0 ≤ b * y 0 := mul_nonneg hb hy.1
      linarith
  let := hs.contractibleSpace ⟨c, hcS⟩
  exact (puncturedHalfSpaceHomeomorph p).contractibleSpace

variable (k : Type) [Field k]


theorem finiteHomologyType_localHalfSpace (hp : p.val 0 = 0) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of (EuclideanHalfSpace n))
        ({p}ᶜ : Set (EuclideanHalfSpace n)) (ModuleCat.of k k)) := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  exact finiteHomologyType_relativeChainComplex _ _ k
    (finiteHomologyType_of_contractible k) (finiteHomologyType_of_contractible k)


theorem relativeEulerChar_localHalfSpace (hp : p.val 0 = 0) :
    relativeEulerChar (TopCat.of (EuclideanHalfSpace n))
      ({p}ᶜ : Set (EuclideanHalfSpace n)) k = 0 := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  rw [relativeEulerChar_eq_sub _ _ k (finiteHomologyType_of_contractible k)
    (finiteHomologyType_of_contractible k), eulerChar_of_contractible,
    eulerChar_of_contractible, sub_self]

end DifferentialGeometry.Homology
