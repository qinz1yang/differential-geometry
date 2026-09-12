import Poincare.Topology.Homology.RelativeHomeomorphism
import Mathlib.Geometry.Manifold.ChartedSpace

/-! # Actual local homology through the same open chart -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]

/-- Restriction to the SAME open source, its original chart homeomorphism,
and inclusion of its SAME open target identify the original local homology. -/
def integralLocalHomologyOpenPartialHomeomorphIso (n : ℕ) (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) : integralLocalHomology n x ≅ integralLocalHomology n (e x) :=
  (integralLocalHomologyNeighborhoodIso n x e.source e.open_source hx).symm ≪≫
    integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget ⟨x, hx⟩ ≪≫
      integralLocalHomologyNeighborhoodIso n (e x) e.target e.open_target (e.map_source hx)

/-- The original manifold chart identifies local singular homology at
the SAME point with local singular homology at its actual chart coordinate. -/
def integralLocalHomologyChartIso [ChartedSpace Y X] (n : ℕ) (x : X) :
    integralLocalHomology n x ≅ integralLocalHomology n (chartAt Y x x) :=
  integralLocalHomologyOpenPartialHomeomorphIso n (chartAt Y x) x (mem_chart_source Y x)

theorem integralLocalHomologyOpenPartialHomeomorphIso_natural (n : ℕ)
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) :
    (integralLocalHomologyNeighborhoodIso n x e.source e.open_source hx).hom ≫
        (integralLocalHomologyOpenPartialHomeomorphIso n e x hx).hom =
      (integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget
        (⟨x, hx⟩ : e.source)).hom ≫
          (integralLocalHomologyNeighborhoodIso n (e x) e.target
            e.open_target (e.map_source hx)).hom := by
  simp [integralLocalHomologyOpenPartialHomeomorphIso]
  rfl

end Poincare.Topology
