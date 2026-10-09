import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentOneCone

/-!
# Filled pants geometry modulo the two-cone family

S9 packet A5 with the one-cone family discharged. The input `hone` of
`filledPantsBlockGeometry_of_families` (an `H² × ℝ` interior geometry on every standard one-cone
carrier) is `oneConeBlock_interiorGeometry` (lanes A4b2 and A4D2: the one-cone fold data and the
route-D descent), so `filledPantsBlockGeometry_of_twoCone` leaves only the two-cone family `htwo`.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem filledPantsBlockGeometry_of_twoCone
    (htwo : ∀ (W : CompactCarrier.{u}) (d : SeifertData) (_ : SeifertBlock W d)
      (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ), d.ports = 1 → d.cones = [(p₁, q₁), (p₂, q₂)] →
      ¬ (p₁ = 2 ∧ p₂ = 2) →
      ∃ G : W.InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
        letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    FilledPantsBlockGeometry.{u} :=
  filledPantsBlockGeometry_of_families
    (fun p q hp hpq => oneConeBlock_interiorGeometry p q hp hpq) htwo

end GC.Seifert
