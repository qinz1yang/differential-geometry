import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceEntropyLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyRigidity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRoundScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceScalarPositive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientRoundFlowTopology : TopologicalSpace F.M := F.topology
local instance ancientRoundFlowCharted : ChartedSpace H F.M := F.charted
local instance ancientRoundFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientRoundFlowC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientRoundFlowT2 : T2Space F.M := F.t2
local instance ancientRoundFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientRoundFlowNonempty : Nonempty F.M := ⟨F.basepoint⟩

theorem ancientKappaSurface_entropy_minimum_and_scalar_constant
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
    ∀ t : ℝ, t ≤ 0 →
      surfaceEntropy (F.S.family.metric t) =
        totalScalarCurvature (F.S.family.metric 0) *
          Real.log (totalScalarCurvature (F.S.family.metric 0)) ∧
        ∃ c : ℝ, ∀ x : F.M, F.S.scalar t x = c := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  let _ : ConnectedSpace F.M := hF.connected
  have hpositive : ∀ t : ℝ, t ≤ 0 → ∀ x : F.M, 0 < F.S.scalar t x :=
    fun _ ht x => ancientKappaSurface_scalar_pos F hdim hF ht x
  obtain ⟨rho, _, hrho, hbackward⟩ :=
    ancientKappaSurface_exists_backward_entropy_minimum F hF hdim
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  exact surfaceEntropy_rigidity_of_backward_minimum F.S.family.metric
    (totalScalarCurvature (F.S.family.metric 0))
    (fun _ ht => ancientSurfaceFlow_totalScalar_eq_terminal F.S F.isSolution hdim ht)
    hpositive (ancientSurfaceEntropy_antitoneOn F.S F.isSolution hdim hpositive)
    rho hrho hbackward

theorem ancientKappaSurface_roundScaling
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
    let T := surfaceArea (F.S.family.metric 0) /
      totalScalarCurvature (F.S.family.metric 0)
    ∃ hT : 0 < T,
      (∀ t : ℝ, t ≤ 0 → totalScalarCurvature (F.S.family.metric t) =
        totalScalarCurvature (F.S.family.metric 0)) ∧
      (∀ t : ℝ, t ≤ 0 → surfaceArea (F.S.family.metric t) =
        surfaceArea (F.S.family.metric 0) - totalScalarCurvature (F.S.family.metric 0) * t) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ x : F.M, F.S.scalar t x = 1 / (T - t)) ∧
      (∀ (t : ℝ) (ht : t ≤ 0), F.S.family.metric t =
        scaleMetric ((T - t) / T) (div_pos (by linarith) hT) (F.S.family.metric 0)) := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  have hpositive : ∀ t : ℝ, t ≤ 0 → ∀ x : F.M, 0 < F.S.scalar t x :=
    fun _ ht x => ancientKappaSurface_scalar_pos F hdim hF ht x
  have hrigid := ancientKappaSurface_entropy_minimum_and_scalar_constant F hF hdim
  exact ancientSurfaceFlow_roundScaling_of_spatially_constant F.S F.isSolution hdim
    hpositive (fun t ht => (hrigid t ht).2)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
