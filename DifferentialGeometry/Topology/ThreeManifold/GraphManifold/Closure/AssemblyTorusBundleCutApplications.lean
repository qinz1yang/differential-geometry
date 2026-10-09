import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyTorusBundleCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystemApplications

/-!
# Chapter-14 assembly, L3-cut: the torus presentation of a torus bundle over the circle

Consumer of `AssemblyTorusBundleCut.lean` (lane ASM-L3): the cut data of L3-cut fed to the B3
producer (`exists_torusPresentation_of_selfSeam_cutData`, lane ASM-B3). A torus bundle over the
circle with empty boundary has a torus presentation with one component, one pairing torus whose two
sides lie in that component (a self-seam), no external torus, and the seam collar is the signed
collar of the cut.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Torus presentation of a torus bundle over the circle**: one component, one self-paired
torus, no external torus. -/
theorem exists_torusPresentation_of_torusBundle (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : Torus → W.Carrier) (hf : IsSmoothEmbedding torusModel W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    ∃ T : TorusPresentation W, T.components.count = 1 ∧ T.pairing.count = 1 ∧
      T.externalCount = 0 ∧ ∀ c, T.leftPiece c = T.rightPiece c := by
  obtain ⟨D, h1, hs, hself, -⟩ := exists_selfSeam_cutData_of_torusBundle W hW p hp hsub f hf hr
  obtain ⟨T, hc, hpc, he, hlr, -⟩ := exists_torusPresentation_of_selfSeam_cutData D h1 hs hself
  exact ⟨T, hc, hpc, he, hlr⟩

end GC.GraphManifold.Assembly
