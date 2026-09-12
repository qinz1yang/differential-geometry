import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaModelCurvatureWindow

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem modelCurvatureBoundNearBase
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (hkappa : 0 < kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa := by
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
    hdim hkappa

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
