import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.IsometricSMul

set_option autoImplicit false

namespace EuclideanSpace

noncomputable def finSuccProdIsometry (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ) :=
  ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin k ⊕ Fin 1 => ℝ))).trans
      (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ _)
        (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm)

end EuclideanSpace

namespace IsometryEquiv

universe u
variable {X : Type u} [MetricSpace X]

theorem exists_pointed_euclidean_of_l2_real_product {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ)) (p : X) :
    ∃ F : X ≃ᵢ EuclideanSpace ℝ (Fin (k + 1)), F p = 0 := by
  let f := e.trans (EuclideanSpace.finSuccProdIsometry k).symm.toIsometryEquiv
  exact ⟨f.trans (IsometryEquiv.subRight (f p)), sub_self _⟩

theorem exists_pointed_successor_splitting_of_l2_real_product {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ)) (p : X) :
    ∃ (Z : Type u) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × Z)),
        F p = WithLp.toLp 2 (0, z) := by
  obtain ⟨f, hf⟩ := e.exists_pointed_euclidean_of_l2_real_product p
  let Z := {x : X // x = p}
  let z : Z := ⟨p, rfl⟩
  let : Unique Z := ⟨⟨z⟩, fun x => Subtype.ext x.property⟩
  let F := f.trans (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin (k + 1))) Z).symm
  refine ⟨Z, inferInstance, z, F, ?_⟩
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact hf
  · exact Subsingleton.elim _ _

end IsometryEquiv
