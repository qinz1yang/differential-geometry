import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClass
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonRegular

/-!
# Regular heights and bigons on the torus

Chapter 6, packet K08, lane MC2. A height `s` is regular for `φ` when the height of `φ` along
the first circle has nonzero derivative at every point of the level `s`. Regular heights exist
(and are dense), and the level set of a regular height is finite.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def IsRegularHeight (φ : TDiff) (s : Circle) : Prop :=
  ∀ z, heightOnCircle φ z = s → mfderiv (𝓡 1) (𝓡 1) (heightOnCircle φ) z ≠ 0

theorem contMDiff_alphaCircle : ContMDiff (𝓡 1) torusModel ∞ alphaCircle :=
  contMDiff_id.prodMk contMDiff_const

theorem contMDiff_heightOnCircle (φ : TDiff) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (heightOnCircle φ) :=
  contMDiff_snd.comp (φ.contMDiff.comp contMDiff_alphaCircle)

theorem exists_isRegularHeight_mem (φ : TDiff) {U : Set Circle} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ s ∈ U, IsRegularHeight φ s :=
  circle_exists_regular_mem (contMDiff_heightOnCircle φ) hU hne

theorem exists_isRegularHeight (φ : TDiff) : ∃ s : Circle, IsRegularHeight φ s := by
  obtain ⟨s, -, hs⟩ := exists_isRegularHeight_mem φ isOpen_univ univ_nonempty
  exact ⟨s, hs⟩

theorem IsRegularHeight.finite {φ : TDiff} {s : Circle} (hs : IsRegularHeight φ s) :
    {z | heightOnCircle φ z = s}.Finite :=
  circle_finite_fiber_of_regular (contMDiff_heightOnCircle φ) hs

end GC.Seifert
