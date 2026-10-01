import DifferentialGeometry.Topology.ThreeManifold.Model
import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology



variable (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

abbrev tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    TangentSpace ThreeModel x ≃ₗ[ℝ] ThreeSpace :=
  DifferentialGeometry.tangentChartEquiv ThreeModel M p x hx

abbrev TangentOrientationSection :=
  DifferentialGeometry.ManifoldOrientation ThreeModel M 3

variable {M}


variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]

def PreservesTangentOrientationAt (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) (x : M)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x)) : Prop :=
  Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f x).toLinearMap hf)
      (oM.orientation x) = oN.orientation (f x)

def PreservesTangentOrientation (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : M → N) : Prop :=
  ContMDiff ThreeModel ThreeModel ∞ f ∧
    ∀ x : M, ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f x),
      PreservesTangentOrientationAt oM oN f x hf

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
