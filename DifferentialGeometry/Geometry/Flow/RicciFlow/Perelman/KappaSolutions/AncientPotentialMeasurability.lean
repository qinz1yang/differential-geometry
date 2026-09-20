import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityMeasurability

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff Topology ENNReal

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
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem measurable_exp_neg_redLength
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 < tau) (p : F.M) :
    Measurable (fun x => Real.exp (-redLength F.S T p x tau)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hden := ancient_measurable_redDensity F hF hT htau p
  have heq : (fun x => Real.exp (-redLength F.S T p x tau)) = fun x =>
      redDensity F.S T p x tau * Real.exp
        (((Module.finrank ℝ E : ℝ) / 2) * Real.log tau +
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) := by
    funext x
    rw [redDensity, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hden.mul_const _


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
