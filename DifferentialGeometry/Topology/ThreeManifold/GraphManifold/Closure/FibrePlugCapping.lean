import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCapping

/-!
The actual bounded fibre plug has its canonical spherical cut and standard oriented ball caps,
with both original external collars retained at one common scale.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

theorem exists_fibrePlugCapping :
    ∃ (W : CompactCarrier.{u}) (E : ElementaryPresentation W)
      (j : Fin E.toTorus.pairing.count) (h : E.IsSplitSeam j true)
      (hlin : E.IsLinearSeam j)
      (d : PartialDiffeomorph sphereSignedCollarModel W.model
        (ClosureSphere.{u} × ℝ) W.Carrier ∞),
      W.kind = .withBoundary ∧ E.toTorus.components.count = 2 ∧
      E.toTorus.pairing.count = 1 ∧ E.toTorus.externalCount = 2 ∧
      d.source = sphereSignedCollarSource ∧ d.target ⊆ W.interior ∧
      (∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s)) ∧
      ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
        (C : CompactCarrier.{u}) (B : MixedBoundaryCertificate C)
        (hn : B.torusCount = E.toTorus.externalCount) (h2 : B.sphereCount = 2)
        (fold : C.Carrier → W.Carrier),
        C.kind = .withBoundary ∧ ContMDiff C.model W.model ∞ fold ∧ Surjective fold ∧
        (∀ x, ∃ A : TangentSpace C.model x ≃ₗ[ℝ] TangentSpace W.model (fold x),
          (∀ v, A v = mfderiv C.model W.model fold x v) ∧
          Orientation.map (Fin 3) A (C.orientation.orientation x) =
            W.orientation.orientation (fold x)) ∧
        (∀ r p, p ∈ halfCollarSource →
          fold (B.tori.collar (Fin.cast hn.symm r) p) =
            (E.toTorus.external.shrink hδ hδ1).collar r p) ∧
        (∀ i z s (hs0 : 0 ≤ s), s < 1 →
          fold (B.sphere (Fin.cast h2.symm i) (z, halfPoint s hs0)) =
            d (z, if i.val = 0 then s else -s)) ∧
        (∀ x y, fold x = fold y ↔ x = y ∨ ∃ z,
          (x = B.sphere (Fin.cast h2.symm 0) (z, halfZero) ∧
            y = B.sphere (Fin.cast h2.symm 1) (z, halfZero)) ∨
          (x = B.sphere (Fin.cast h2.symm 1) (z, halfZero) ∧
            y = B.sphere (Fin.cast h2.symm 0) (z, halfZero))) ∧
        (∃ ρ : Quotient (Setoid.ker fold) ≃ₜ W.Carrier,
          ∀ x : C.Carrier, ρ (Quotient.mk'' x) = fold x) ∧
        Nonempty (RelativeSphereCapping C B.sphereCapCarrier B) := by
  obtain ⟨W, E, j, hW, hC, hP, hE, h, hlin⟩ := exists_fibrePlug.{u}
  obtain ⟨d, hs, hI, heq, δ, hδ, hδ1, hav⟩ :=
    E.exists_boundedSplitSignedTube j true h hlin
  have hboundary : W.model.boundary W.Carrier =
      (E.toTorus.external.shrink hδ hδ1).image := by
    rw [BoundaryTori.shrink_image]
    exact E.toTorus.external_exhausted
  have havoid (r : Fin E.toTorus.externalCount) :
      Disjoint ((E.toTorus.external.shrink hδ hδ1).collar r).target d.target :=
    (hav r).symm
  obtain ⟨C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, hrel, hq⟩ :=
    exists_sphereCutCarrier W d hs hI (E.toTorus.external.shrink hδ hδ1)
      hboundary havoid
  exact ⟨W, E, j, h, hlin, d, hW, hC, hP, hE, hs, hI, heq, δ, hδ, hδ1,
    C, B, hn, h2, fold, hk, hsm, hsurj, ho, ht, hf, hrel, hq, ⟨B.sphereCapRelativeCapping⟩⟩

end GC.GraphManifold
