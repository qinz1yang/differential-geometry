import DifferentialGeometry.Topology.Covering.Quotient
import DifferentialGeometry.Geometry.Metric.Isometry.Compactness
import Mathlib.Topology.Algebra.OpenSubgroup

namespace IsometryEquiv

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem finite_setOf_image_inter_nonempty (Γ : Subgroup (X ≃ᵢ X)) [DiscreteTopology Γ]
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) :
    Set.Finite {g : Γ | (((g : X ≃ᵢ X) : X → X) '' K ∩ L).Nonempty} := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨o, _⟩
  · simp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall o
  obtain ⟨T, hT⟩ := hL.isBounded.subset_closedBall o
  have hΓ : IsClosed (Γ : Set (X ≃ᵢ X)) := Subgroup.isClosed_of_discreteTopology
  have hfin : Set.Finite {g : Γ | dist ((g : X ≃ᵢ X) o) o ≤ R + T} :=
    (hΓ.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_setOf_dist_apply_le o (R + T))).finite_of_discrete
  apply hfin.subset
  rintro g ⟨z, ⟨p, hp, rfl⟩, hgp⟩
  calc
    dist ((g : X ≃ᵢ X) o) o ≤
        dist ((g : X ≃ᵢ X) o) ((g : X ≃ᵢ X) p) + dist ((g : X ≃ᵢ X) p) o :=
      dist_triangle _ _ _
    _ = dist o p + dist ((g : X ≃ᵢ X) p) o := by rw [(g : X ≃ᵢ X).dist_eq]
    _ ≤ R + T := add_le_add (by simpa only [Metric.mem_closedBall, dist_comm o p] using hR hp)
      (hT hgp)

instance instProperlyDiscontinuousSMul (Γ : Subgroup (X ≃ᵢ X)) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ X where
  finite_disjoint_inter_image hK hL := finite_setOf_image_inter_nonempty Γ hK hL

theorem isCoveringMap_quotientMk_of_torsion_free (Γ : Subgroup (X ≃ᵢ X)) [DiscreteTopology Γ]
    (hΓ : ∀ g : Γ, IsOfFinOrder g → g = 1) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel Γ X)) :=
  MulAction.isCoveringMap_quotientMk_of_torsion_free hΓ

end IsometryEquiv
