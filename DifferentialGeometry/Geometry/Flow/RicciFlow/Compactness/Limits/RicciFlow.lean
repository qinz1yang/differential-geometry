import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps


set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def CompactnessConclusion (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D, exists subseq : Nat -> Nat,
    StrictMono subseq /\
      Nonempty.{max (max uE uH) u + 1} (SmoothCGHConverges (I := I) X L subseq)

end HCGCompactness
end DifferentialGeometry
