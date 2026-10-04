import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRawApplications

/-!
# Chapter-14 assembly, L3-T²: the raw presentation of a torus bundle over the circle

Lane ASM-L3 (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §0.7 and
§3 L3). L3-cut (`exists_selfSeam_cutData_of_torusBundle`: one piece `T² × I`, one self-seam) followed
by the one-piece, one-self-seam B3 assembly of lane ASM-B3
(`exists_rawGraphPresentation_of_selfSeam_torusProduct`: B3, G1, `annulusRawPresentation`
`Closure/BasicModels.lean:65`, `exists_rawGraphPresentation_of_rawPieces`
`Closure/LocalRawFaces.lean:331`). The total space is not identified with `T³` or with one Seifert
piece; the monodromy is arbitrary.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **L3-T².** Raw presentation of a torus bundle over the circle (L3-cut, B3, G1,
`annulusRawPresentation` `Closure/BasicModels.lean:65`, `exists_rawGraphPresentation_of_rawPieces`
`Closure/LocalRawFaces.lean:331`). -/
theorem exists_rawGraphPresentation_of_torusBundle (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : Torus → W.Carrier) (hf : IsSmoothEmbedding torusModel W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨D, h1, hs, hself, he⟩ := exists_selfSeam_cutData_of_torusBundle W hW p hp hsub f hf hr
  exact (exists_rawGraphPresentation_of_selfSeam_torusProduct D h1 hs hself he).1

end GC.GraphManifold.Assembly
