import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.EndpointSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalMeasurableTopology : TopologicalSpace F.M := F.topology
private local instance terminalMeasurableCharted : ChartedSpace H F.M := F.charted
private local instance terminalMeasurableSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalMeasurableT2 : T2Space F.M := F.t2
private local instance terminalMeasurableSpace : MeasurableSpace F.M := borel F.M
private local instance terminalMeasurableBorel : BorelSpace F.M := ⟨rfl⟩

theorem ancient_measurable_redDensity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T tau : ℝ} (hT : T ≤ 0) (htau : 0 < tau) (p : F.M) :
    Measurable (fun q : F.M => redDensity F.S T p q tau) := by
  let : ConnectedSpace F.M := hF.connected
  obtain ⟨B, hB⟩ := hF.globalScalarBound
  have hcost : UpperSemicontinuous (fun q : F.M => lCost F.S T p q tau) :=
    upperSemicontinuous_lCost_of_scalar_nonneg F.S F.isSolution htau p
      isOpen_univ (subset_univ _)
      (fun s _ => by change T - s ^ 2 ≤ 0; nlinarith [sq_nonneg s])
      (fun s hs z => (hB (T - s) ((sub_le_self _ hs.1).trans hT) z).1)
  let phi : ℝ → ℝ := fun r => Real.exp
    (-r / (2 * Real.sqrt tau) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hphi : Continuous phi := by dsimp only [phi]; fun_prop
  have hphiAnti : Antitone phi := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    gcongr
  have hdensity : LowerSemicontinuous (fun q : F.M => redDensity F.S T p q tau) := by
    simpa only [Function.comp_def, phi, redDensity, redLength, neg_div] using
      hphi.comp_upperSemicontinuous_antitone hcost hphiAnti
  exact hdensity.measurable

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
