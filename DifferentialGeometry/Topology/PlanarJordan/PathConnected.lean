import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Topology.Connected.LocallyPathConnected

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem isPathConnected_compl_arc {A : Set Schoenflies.Plane} (hA : Schoenflies.IsArc A) :
    IsPathConnected Aᶜ :=
  (isOpen_compl_iff.mpr hA.isClosed).isConnected_iff_isPathConnected.mp
    (Schoenflies.arc_complement hA)

theorem isPathConnected_inside {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C) :
    IsPathConnected (Schoenflies.inside C) :=
  (Schoenflies.jordan_curve_theorem hC).isOpen_inside.isConnected_iff_isPathConnected.mp
    (Schoenflies.jordan_curve_theorem hC).isConnected_inside

theorem isPathConnected_outside {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C) :
    IsPathConnected (Schoenflies.outside C) :=
  (Schoenflies.jordan_curve_theorem hC).isOpen_outside.isConnected_iff_isPathConnected.mp
    (Schoenflies.jordan_curve_theorem hC).isConnected_outside

end DifferentialGeometry.Topology.PlanarJordan
