import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereBundleApplications

/-!
# Chapter-14 assembly, L3: the slim circle-base branch of the FC42 consumer

Consumer of `AssemblyTorusBundleRaw.lean` and `AssemblySphereBundleApplications.lean` (lane
ASM-L3; design §3, FC42 step 2). A closed carrier fibred over the circle whose fibre over `1` is an
actual torus or an actual sphere has a raw graph presentation: the torus case through L3-cut and the
one-self-seam B3 assembly (with its torus presentation: one component diffeomorphic to `T² × I`,
one self-paired torus, no external torus), the sphere case through L3-S² and the `S² × S¹` adapter.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- L3-T² with the torus presentation of the cut: one component diffeomorphic to `T² × I`, one
self-paired torus, no external torus. -/
theorem exists_rawGraphPresentation_and_torusPresentation_of_torusBundle (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : Torus → W.Carrier) (hf : IsSmoothEmbedding torusModel W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    Nonempty (RawGraphPresentation W) ∧ ∃ T : TorusPresentation W,
      T.components.count = 1 ∧ T.pairing.count = 1 ∧ T.externalCount = 0 ∧
      (∀ c, T.leftPiece c = T.rightPiece c) ∧
      ∀ i, Nonempty ((T.Component i).Carrier ≃ₘ⟮(T.Component i).model,
        annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier) := by
  obtain ⟨D, h1, hs, hself, he⟩ := exists_selfSeam_cutData_of_torusBundle W hW p hp hsub f hf hr
  exact exists_rawGraphPresentation_of_selfSeam_torusProduct D h1 hs hself he

/-- **Slim circle-base branch.** A closed carrier fibred over the circle with an actual torus or
sphere fibre over `1` has a raw graph presentation. -/
theorem exists_rawGraphPresentation_of_circleBundle (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (hfibre : (∃ f : Torus → W.Carrier, IsSmoothEmbedding torusModel W.model ∞ f ∧
        range f = p ⁻¹' {1}) ∨
      ∃ f : ClosureSphere.{u} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ f ∧
        range f = p ⁻¹' {1}) :
    Nonempty (RawGraphPresentation W) := by
  rcases hfibre with ⟨f, hf, hr⟩ | ⟨f, hf, hr⟩
  · exact exists_rawGraphPresentation_of_torusBundle W hW p hp hsub f hf hr
  · obtain ⟨G, -⟩ := exists_rawGraphPresentation_of_sphereBundle W hW p hp hsub f hf hr
    exact ⟨G⟩

end GC.GraphManifold.Assembly
