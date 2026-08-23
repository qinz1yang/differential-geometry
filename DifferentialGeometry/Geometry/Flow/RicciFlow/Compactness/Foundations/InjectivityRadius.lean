import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.InjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

abbrev FlowerScaleInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
