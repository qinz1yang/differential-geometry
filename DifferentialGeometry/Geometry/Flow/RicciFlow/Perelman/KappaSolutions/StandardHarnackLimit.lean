import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalHarnack

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance standardHarnackTopology : TopologicalSpace F.M := F.topology
local instance standardHarnackCharted : ChartedSpace H F.M := F.charted
local instance standardHarnackSmooth : IsManifold I ∞ F.M := F.smooth
local instance standardHarnackC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance standardHarnackT2 : T2Space F.M := F.t2
local instance standardHarnackSigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem ancientKappa_toKLim_of_rmNormSqBound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : 2 ≤ Module.finrank ℝ E) {B : ℝ}
    (hbound : PointedFlowRmNormSqBounded (I := I) F B) : KLim kappa F := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hcomplete : ∀ t ∈ D.carrier,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) := by
    intro t ht
    exact ⟨hF.complete t ht⟩
  have hcurv : ∀ a b : ℝ, Set.Icc a b ⊆ D.carrier →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        Tensor0SBundle.normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ C := by
    intro a b hslab
    exact ⟨B, fun t ht x => hbound t (hslab ht) x⟩
  have hR : ∀ t ∈ D.carrier, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  refine
    { dimension_ge_two := hdim
      kappa_pos := hF.kappa_pos
      carrier_eq := hF.carrier_eq
      regular_eq := hF.regular_eq
      connected := hF.connected
      complete := hF.complete
      nonnegativeCurvatureOperator := hF.nonnegativeCurvatureOperator
      noncollapsed := hF.noncollapsed
      notFlat := hF.notFlat
      traceHarnack := ?_ }
  intro t ht x V
  by_cases ht0 : t = 0
  · subst t
    exact hamilton_ancient_trace_harnack_at_terminal F.S F.isSolution
      hF.carrier_eq hF.regular_eq hcomplete hcurv hR x V
  · have htneg : t < 0 := lt_of_le_of_ne
      (by simpa only [hF.carrier_eq, Set.mem_Iic] using ht) ht0
    have htreg : t ∈ D.regular := by
      simpa only [hF.regular_eq, Set.mem_Iio] using htneg
    rw [derivWithin_of_mem_nhds (D.regular_mem_nhds htreg)]
    apply hamilton_ancient_trace_harnack F.S F.isSolution
      (fun s hs => hcomplete s (D.regular_subset hs))
      (fun a b hab => hcurv a b (hab.trans D.regular_subset))
      (fun s hs y => hR s (D.regular_subset hs) y) _ x V
    intro s hs
    simpa only [hF.regular_eq, Set.mem_Iio] using hs.trans_lt htneg

theorem ancientKappaSurface_toKLim {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 2) :
    KLim kappa F := by
  obtain ⟨C, _, hbound⟩ := ancientKappaSurface_rmNormSqBounded F hdim hF
  exact ancientKappa_toKLim_of_rmNormSqBound F hF (by omega) hbound

theorem ancientKappaThree_toKLim {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    KLim kappa F := by
  obtain ⟨C, _, hbound⟩ := ancientKappa_rmNormSqBounded F hdim hF
  exact ancientKappa_toKLim_of_rmNormSqBound F hF (by omega) hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
