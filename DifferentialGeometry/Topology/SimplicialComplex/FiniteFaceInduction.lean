import DifferentialGeometry.Topology.SimplicialComplex.MaximalFace
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}

@[elab_as_elim]
theorem finite_face_induction (P : PreAbstractSimplicialComplex ι → Prop)
    (hEmpty : ∀ K, K.faces = ∅ → P K)
    (hFace : ∀ (K : PreAbstractSimplicialComplex ι) [Finite K.faces]
      (s : Finset ι) (hs : s ∈ K), IsMax (⟨s, hs⟩ : K.faces) → P (faceCostar K s) → P K)
    (K : PreAbstractSimplicialComplex ι) [Finite K.faces] : P K := by
  generalize hn : Nat.card K.faces = n
  induction n using Nat.strong_induction_on generalizing K with
  | h n ih =>
    by_cases he : K.faces = ∅
    · exact hEmpty K he
    · obtain ⟨s, hs⟩ := (Set.toFinite K.faces).exists_maximal (Set.nonempty_iff_ne_empty.mpr he)
      have hmax : IsMax (⟨s, hs.1⟩ : K.faces) := fun t ht ↦ hs.2 t.prop ht
      apply hFace K s hs.1 hmax
      exact ih (Nat.card (faceCostar K s).faces)
        (by rw [← hn]; exact card_faceCostar_lt K s hs.1) (faceCostar K s) rfl

section Geometry
variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

@[elab_as_elim]
theorem finite_geometricFace_induction (P : Geometry.SimplicialComplex 𝕜 E → Prop)
    (hEmpty : ∀ K, K.faces = ∅ → P K)
    (hFace : ∀ (K : Geometry.SimplicialComplex 𝕜 E) [Finite K.faces]
      (s : Finset E), s ∈ K.facets → P (geometricFaceCostar K s) → P K)
    (K : Geometry.SimplicialComplex 𝕜 E) [Finite K.faces] : P K := by
  generalize hn : Nat.card K.faces = n
  induction n using Nat.strong_induction_on generalizing K with
  | h n ih =>
    by_cases he : K.faces = ∅
    · exact hEmpty K he
    · obtain ⟨s, hs⟩ := (Set.toFinite K.faces).exists_maximal (Set.nonempty_iff_ne_empty.mpr he)
      have hfacet : s ∈ K.facets :=
        ⟨hs.1, fun _ ht hst ↦ Finset.Subset.antisymm hst (hs.2 ht hst)⟩
      apply hFace K s hfacet
      exact ih (Nat.card (geometricFaceCostar K s).faces)
        (by rw [← hn]; exact card_faceCostar_lt K.toPreAbstractSimplicialComplex s hs.1)
        (geometricFaceCostar K s) rfl

end Geometry
end DifferentialGeometry.Topology.SimplicialComplex
