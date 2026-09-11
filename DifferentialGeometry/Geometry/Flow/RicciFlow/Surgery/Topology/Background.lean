import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeModel := 𝓘(ℝ, ThreeSpace)

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def tangentChartEquiv (p x : M)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    TangentSpace ThreeModel x ≃ₗ[ℝ] ThreeSpace :=
  (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).linearEquivAt ℝ x hx

structure TangentOrientationSection where
  orientation : (x : M) → Orientation ℝ (TangentSpace ThreeModel x) (Fin 3)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin 3) (tangentChartEquiv M p y (hU hy)) (orientation y) =
          Orientation.map (Fin 3) (tangentChartEquiv M p x hx) (orientation x)

variable {M}


def TangentOrientationSection.inChart (o : TangentOrientationSection M) (p x : M)
    (hx : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    Orientation ℝ ThreeSpace (Fin 3) :=
  Orientation.map (Fin 3) (tangentChartEquiv M p x hx) (o.orientation x)

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
