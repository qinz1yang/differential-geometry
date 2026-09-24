import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarBoundAdditiveDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_ancientKappa_riemannianEDist_sub_le
    (hdim : 2 ≤ Module.finrank ℝ E) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x y : F.M,
      0 ≤ (riemannianEDistOf (F.S.base.metric s) x y).toReal -
        (riemannianEDistOf (F.S.base.metric t) x y).toReal ∧
      (riemannianEDistOf (F.S.base.metric s) x y).toReal -
        (riemannianEDistOf (F.S.base.metric t) x y).toReal ≤ C * (t - s) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  have hRnonneg : 0 ≤ R :=
    (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).1.trans
      (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).2
  refine ⟨(10 / 3 : ℝ) * Real.sqrt (((Module.finrank ℝ E : ℝ) - 1) * R),
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro s t hst ht x y
  apply ricciFlow_additive_distance_bound_of_scalar_upper F.S F.isSolution hdim hF.connected
    hst hRnonneg (fun r hr => hr.2.trans ht) (fun r hr => hr.2.trans_le ht)
    (fun r hr => ⟨hF.complete r (hr.2.trans ht)⟩)
  · intro r hr z
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric r) z).mpr
    intro n c v w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator r (hr.2.trans ht) z n c v w
  · intro r hr z
    exact (hR r (hr.2.trans ht) z).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
