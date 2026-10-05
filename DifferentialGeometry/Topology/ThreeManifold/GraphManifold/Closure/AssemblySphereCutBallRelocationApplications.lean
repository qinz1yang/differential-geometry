import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallRelocation

/-!
# Consumers of the cap relocation

* `range_relativeSphereCap_subset_interior`: the caps of a relative sphere capping lie in the
  interior of the capped carrier (a cap meets the core only along its cut sphere, and the cut
  spheres avoid the retained torus collars).
* `SphereCutCapped.exists_capRelocation`: when the capped carrier of a sphere cut is connected
  (the non-separating case of L2-relative), every cap is moved into a fibre piece of any raw
  presentation of it, by an isotopy that fixes the boundary throughout.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The caps of a relative sphere capping lie in the interior of the capped carrier. -/
theorem range_relativeSphereCap_subset_interior {C Q : CompactCarrier.{u}}
    {B : MixedBoundaryCertificate C} (K : RelativeSphereCapping C Q B) (i : Fin B.sphereCount) :
    range (K.cap i) ⊆ Q.interior := by
  rintro _ ⟨x, rfl⟩
  change Q.model.IsInteriorPoint (K.cap i x)
  by_contra hx
  have hb : K.cap i x ∈ Q.model.boundary Q.Carrier :=
    (Q.model.isBoundaryPoint_iff_not_isInteriorPoint _).mpr hx
  rw [K.boundary_exhausted] at hb
  obtain ⟨k, t, ht⟩ := mem_iUnion.mp hb
  rw [K.retained_zero] at ht
  have hmem : K.cap i x ∈ range K.core ∩ range (K.cap i) := ⟨⟨_, ht⟩, ⟨x, rfl⟩⟩
  rw [K.core_cap_intersection] at hmem
  obtain ⟨z, hz⟩ := hmem
  have heq : B.sphere i (z, halfZero) = B.tori.torusMap k t :=
    K.core_embedding.isEmbedding.injective (hz.trans ht.symm)
  have h1 : B.sphere i (z, halfZero) ∈ (B.sphere i).target := by
    apply (B.sphere i).map_source
    rw [B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  have h2 : B.tori.torusMap k t ∈ (B.tori.collar k).target := by
    apply (B.tori.collar k).map_source
    rw [B.tori.source_eq]
    change (0 : ℝ) < 1
    norm_num
  exact Set.disjoint_left.mp (B.cross_disjoint k i) h2 (heq ▸ h1)

/-- **Non-separating case: every cap is relocated into a fibre piece.** -/
theorem SphereCutCapped.exists_capRelocation {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ}
    {E : BoundaryTori W n} (X : SphereCutCapped W S E) [ConnectedSpace X.Q.Carrier]
    (R : RawGraphPresentation X.Q) (i : Fin X.B.sphereCount) :
    ∃ Ψ : ℝ → (X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier),
      (∀ x, Ψ 0 x = x) ∧ (∀ t, ∀ x ∈ X.Q.model.boundary X.Q.Carrier, Ψ t x = x) ∧
      ∃ (j : Fin R.components.count) (b : (R.fibration j).base.Carrier),
        range (Ψ 1 ∘ X.capping.cap i) ⊆ capRelocationTarget R j b := by
  obtain ⟨Ψ, -, h0, ⟨U, -, hU, hfix⟩, j, b, hrange⟩ :=
    exists_capRelocation_into_fibrePiece X.Q R (X.capping.cap i) (X.capping.cap_embedding i)
      (range_relativeSphereCap_subset_interior X.capping i)
  exact ⟨Ψ, h0, fun t x hx => hfix t x (hU hx), j, b, hrange⟩

end GC.GraphManifold.Assembly
