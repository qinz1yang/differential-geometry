import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.HCGCompactness.PointedFlowData

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {D D' D'' : RealTimeInterval}

def timeRestrict (F : PointedFlowData.{u, uE, uH} I D)
    (D' : RealTimeInterval) (hcarrier : D'.carrier ⊆ D.carrier)
    (hregular : D'.regular ⊆ D.regular) : PointedFlowData.{u, uE, uH} I D' := by
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  letI : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  exact {
    M := F.M
    topology := F.topology
    charted := F.charted
    smooth := F.smooth
    sigmaCompact := F.sigmaCompact
    t2 := F.t2
    t2TangentBundle := F.t2TangentBundle
    basepoint := F.basepoint
    S := F.S.timeRestrict D'
    isSolution := isSoln_timeRestrict F.isSolution hcarrier hregular }

@[simp]
theorem timeRestrict_atTime (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D'.carrier ⊆ D.carrier) (hregular : D'.regular ⊆ D.regular)
    (t : Real) :
    (F.timeRestrict D' hcarrier hregular).atTime t = F.atTime t := rfl

@[simp]
theorem timeRestrict_self (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D.carrier ⊆ D.carrier) (hregular : D.regular ⊆ D.regular) :
    F.timeRestrict D hcarrier hregular = F := by
  cases F
  rfl

@[simp]
theorem timeRestrict_timeRestrict (F : PointedFlowData.{u, uE, uH} I D)
    (hcarrier : D'.carrier ⊆ D.carrier) (hregular : D'.regular ⊆ D.regular)
    (hcarrier' : D''.carrier ⊆ D'.carrier) (hregular' : D''.regular ⊆ D'.regular) :
    (F.timeRestrict D' hcarrier hregular).timeRestrict D'' hcarrier' hregular' =
      F.timeRestrict D'' (hcarrier'.trans hcarrier) (hregular'.trans hregular) := rfl

end DifferentialGeometry.HCGCompactness.PointedFlowData
