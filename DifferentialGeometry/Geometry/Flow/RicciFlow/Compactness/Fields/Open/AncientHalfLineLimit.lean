import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLimitScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointCompactLimit

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood Perelman.CanonicalNeighborhood.FiniteHorn
open Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : PointedFlowSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
  {phi : ℕ → ℕ} (Phi : PointedCGHMaps X P phi)
  {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
  {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}

def HalfLineMetricConvergenceData.pointedFlow
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular) :
    PointedFlowData.{u, 0, 0} I3 X.D := by
  let _ : NeZero (Module.finrank ℝ Surgery.Topology.ThreeSpace) :=
    ⟨by simp [Surgery.Topology.ThreeSpace]⟩
  exact { M := P.M
          topology := P.topology
          charted := P.charted
          smooth := P.smooth
          sigmaCompact := P.sigmaCompact
          t2 := P.t2
          t2TangentBundle := P.t2TangentBundle
          basepoint := P.basepoint
          S := { base := { metric := co.gInf } }
          isSolution := co.isSolutionOn Phi hcarrier hregular }

theorem HalfLineMetricConvergenceData.pointedFlow_isAncientKappaSolution
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hD : X.D = ancientTimeInterval) {kappa : ℝ}
    (hsource : ∀ i, IsAncientKappaSolution kappa (X.term i))
    (hconnected : ConnectedSpace P.M)
    (hcomplete : ∀ s ≤ (0 : ℝ), MetricComplete
      ({ P with metric := co.gInf s } : PointedRiemannianManifold I3))
    {B : ℝ} (hbound : ∀ x : P.M, metricScalarAt (co.gInf 0) x ≤ B)
    (hnonflat : ∃ x : P.M, metricScalarAt (co.gInf 0) x ≠ 0) :
    IsAncientKappaSolution kappa
      (co.pointedFlow Phi (hD ▸ rfl) (hD ▸ Subset.rfl)) := by
  let G := co.pointedFlow Phi (hD ▸ rfl) (hD ▸ Subset.rfl)
  let Psi : PointedCGHMaps X (G.atTime 0) (phi ∘ co.φ) := {
    partialDiffeomorph i := Phi.partialDiffeomorph (co.φ i)
    source_exhausts := (Phi.compSubseq co.φ co.strictMono).source_exhausts
    base_mem i := Phi.base_mem (co.φ i)
    basepoint_map i := Phi.basepoint_map (co.φ i) }
  apply isAncientKappaSolution_of_pointed_limit_of_terminal_scalar_bound X hD G Psi
    (by simp [Surgery.Topology.ThreeSpace]) hsource hconnected
    (fun t ht => hcomplete t (by simpa only [hD, ancientTimeInterval_carrier, mem_Iic] using ht))
    ?_ hbound hnonflat
  intro t ht
  obtain ⟨C, hC, _href⟩ := co.exists_canonicalMetricConvergenceData Phi
    (show t ≤ 0 by simpa only [hD, ancientTimeInterval_carrier, mem_Iic] using ht)
  exact ⟨C, hC⟩

end DifferentialGeometry.CheegerGromovCompactness

end

end
