import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerBlowdown
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormedSpaceGeneralization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance backwardSliceShrinkerReplayTopology : TopologicalSpace F.M := F.topology
local instance backwardSliceShrinkerReplayCharted : ChartedSpace H F.M := F.charted
local instance backwardSliceShrinkerReplaySmooth : IsManifold I ∞ F.M := F.smooth
local instance backwardSliceShrinkerReplayT2 : T2Space F.M := F.t2
local instance backwardSliceShrinkerReplaySigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance backwardSliceShrinkerReplayTangentT2 :
    T2Space (TangentBundle I F.M) := F.t2TangentBundle

def backwardSliceLimitRigidity (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (q : ℕ → F.M) : Prop :=
  ∀ (phi : ℕ → ℕ) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)),
    StrictMono phi →
    ∀ (Phi : PointedRiemannianConvergenceMaps (I := I)
      (backwardSliceSequence F tau htau q) L phi)
      (C : MetricConvergenceData (I := I) Phi),
    (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) →
    MetricComplete (I := I) L →
    (let _ : TopologicalSpace L.M := L.topology
     let _ : ChartedSpace H L.M := L.charted
     let _ : IsManifold I ∞ L.M := L.smooth
     let _ : T2Space L.M := L.t2
     ConnectedSpace L.M →
     (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
     ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1)


def backwardSliceShrinkerFrontier {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) : Prop :=
  ∃ q : ℕ → F.M, backwardSliceApproximateMetricCompactness F hF tau htau q ∧
    backwardSliceLimitRigidity F tau htau q


theorem exists_backward_slice_asymptotic_shrinker_of_compactness_rigidity
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (_hdim : 2 ≤ Module.finrank ℝ E)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (_hescape : Tendsto tau atTop atTop)
    (h : backwardSliceShrinkerFrontier F hF tau htau) :
    ∃ (q : ℕ → F.M) (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
        (C : MetricConvergenceData (I := I) Phi),
        (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Phi k) ∧
        (∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric) ∧
        MetricComplete (I := I) L ∧
        (let _ : TopologicalSpace L.M := L.topology
         let _ : ChartedSpace H L.M := L.charted
         let _ : IsManifold I ∞ L.M := L.smooth
         let _ : T2Space L.M := L.t2
         ConnectedSpace L.M ∧
         (∃ x : L.M, metricScalarAt (I := I) L.metric x ≠ 0) ∧
         ∃ f : C^∞⟮I, L.M; ℝ⟯, gradientRicciSoliton (I := I) L.metric f 1) := by
  obtain ⟨q, hcompact, hrigid⟩ := h
  obtain ⟨L, phi, hphi, Phi, C, hdomain, hreference, hcomplete, hconnected⟩ :=
    exists_backward_slice_pointed_limit F hF tau htau q hcompact
  obtain ⟨hnonflat, hsoliton⟩ := hrigid phi L hphi Phi C hdomain hcomplete hconnected
  exact ⟨q, L, phi, hphi, Phi, C, hdomain, hreference, hcomplete,
    hconnected, hnonflat, hsoliton⟩


theorem backwardSliceShrinkerFrontier_of_asymptoticShrinkerInput
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (h : Blowdown.BackwardSliceAsymptoticShrinkerInput (G := F) hF tau htau) :
    backwardSliceShrinkerFrontier F hF tau htau := by
  obtain ⟨q, p, hmono, hcompact, hrigid⟩ := h
  refine ⟨q, hcompact, fun phi L hphi Phi C hdomain hcomplete hconnected => ?_⟩
  exact hrigid hmono L ⟨phi, Phi, C, hphi, hdomain⟩ hcomplete hconnected

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
