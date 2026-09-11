import DifferentialGeometry.Topology.Homology.RelativeHomeomorphism
import Mathlib.Geometry.Manifold.ChartedSpace



noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]



def integralLocalHomologyOpenPartialHomeomorphIso (n : ℕ) (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) : integralLocalHomology n x ≅ integralLocalHomology n (e x) :=
  (integralLocalHomologyNeighborhoodIso n x e.source e.open_source hx).symm ≪≫
    integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget ⟨x, hx⟩ ≪≫
      integralLocalHomologyNeighborhoodIso n (e x) e.target e.open_target (e.map_source hx)



def integralLocalHomologyChartIso [ChartedSpace Y X] (n : ℕ) (x : X) :
    integralLocalHomology n x ≅ integralLocalHomology n (chartAt Y x x) :=
  integralLocalHomologyOpenPartialHomeomorphIso n (chartAt Y x) x (mem_chart_source Y x)

end DifferentialGeometry.Topology
