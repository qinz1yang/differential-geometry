import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderQuotient

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} I ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem AncientCylinderBranch.not_compactSpace
    (h : AncientCylinderBranch F) : ¬ CompactSpace F.M := by
  intro hcompact
  let _ : CompactSpace F.M := hcompact
  let _ : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ⟨sphereEquator 0⟩
  rcases h with ⟨C, htrivial | hantipodal | hdiagonal⟩
  · obtain ⟨e, _⟩ := htrivial.1
    have hc := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ))) hc
  · obtain ⟨e, _⟩ := hantipodal.1
    let _ : Nonempty SphereAntipodalQuotient :=
      ⟨SphereAntipodalQuotient.proj (sphereEquator 0)⟩
    have hc := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace (SphereAntipodalQuotient × ℝ))) hc
  · obtain ⟨e, _⟩ := hdiagonal.1
    have hc := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr
      DifferentialGeometry.Geometry.noncompactSpace_cylinderDiagonalQuotient) hc

theorem ancientKappa_curvatureOperatorPositive_of_compact {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    [CompactSpace F.M] : AncientPositiveCurvatureOperator F := by
  rcases (xor_iff_or_and_not_and _ _).mp
    (ancientKappa_three_dimensional_split_branch F hF hdim) with ⟨hpos | hcylinder, _⟩
  · exact hpos
  · exact (AncientCylinderBranch.not_compactSpace F hcylinder inferInstance).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
