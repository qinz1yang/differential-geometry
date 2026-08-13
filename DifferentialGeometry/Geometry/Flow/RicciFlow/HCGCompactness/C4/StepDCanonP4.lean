import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitUpgrade
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable [NeZero (Module.finrank Real E)]

namespace StepDCanonData

variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}

omit [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)] in
theorem canon_cp
    (D : StepDCanonData (I := I) (X.atZero (I := I)))
    (hsrc : SrcSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps))
    (htgt : TgtSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps)) :
    let mc := D.mc
    let Phi := pointedCGHMaps_of_manifold (I := I) X
      mc.limit mc.subseq mc.maps
    letI : TopologicalSpace mc.limit.M := mc.limit.topology
    letI : ChartedSpace H mc.limit.M := mc.limit.charted
    letI : T2Space mc.limit.M := mc.limit.t2
    letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
    letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
    forall K : Set mc.limit.M, IsCompact K -> forall eps : Real, 0 < eps ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Phi.source k /\
        (letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
            sourceDomTop (I := I) Phi k
         letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
            sourceDomCharted (I := I) Phi k
         letI : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
         letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
            sourceDomSmooth (I := I) Phi k
         letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
            sourceDomSigmaOf (I := I) Phi k (hsrc k)
         metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Phi k K) 0
           (srcMetric (I := I) Phi hsrc htgt k 0)
           (resSrc (I := I) Phi hsrc k mc.limit.metric)
           (refRes (I := I) Phi mc.limit.metric hsrc k) < eps) := by
  dsimp only
  intro K hK eps heps
  obtain ⟨k0, hk0⟩ := D.mc.convergence.metrics.converges K hK 0 eps heps
  refine ⟨k0, fun k hk => ?_⟩
  have hk' := hk0 k hk
  rw [D.domain_eq k] at hk'
  simpa only [MetricSourceData.derivNormSupOn, StepDCanonData.canonDomain,
    StepDCanonData.canonRef] using hk'

omit [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)] in
theorem canon_rel
    (D : StepDCanonData (I := I) (X.atZero (I := I)))
    (hsrc : SrcSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps))
    (htgt : TgtSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps)) :
    let mc := D.mc
    let Phi := pointedCGHMaps_of_manifold (I := I) X
      mc.limit mc.subseq mc.maps
    letI : TopologicalSpace mc.limit.M := mc.limit.topology
    letI : ChartedSpace H mc.limit.M := mc.limit.charted
    letI : T2Space mc.limit.M := mc.limit.t2
    letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
    letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
    exists Crel : Real, 1 <= Crel /\ forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Phi k))
        (refRes (I := I) Phi mc.limit.metric hsrc k)
        (srcMetric (I := I) Phi hsrc htgt k 0) Crel := by
  dsimp only
  obtain ⟨Crel, hCrel, hrel⟩ := D.rel
  refine ⟨Crel, hCrel, fun k => ?_⟩
  have hk := hrel k
  rw [D.domain_eq k] at hk
  simpa only [StepDCanonData.canonDomain, StepDCanonData.canonRef] using hk

omit [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)] in
theorem canon_init
    (D : StepDCanonData (I := I) (X.atZero (I := I)))
    (hsrc : SrcSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps))
    (htgt : TgtSigma (pointedCGHMaps_of_manifold (I := I) X
      D.mc.limit D.mc.subseq D.mc.maps)) :
    let mc := D.mc
    let Phi := pointedCGHMaps_of_manifold (I := I) X
      mc.limit mc.subseq mc.maps
    letI : TopologicalSpace mc.limit.M := mc.limit.topology
    letI : ChartedSpace H mc.limit.M := mc.limit.charted
    letI : T2Space mc.limit.M := mc.limit.t2
    letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
    letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
    forall q : Nat, exists Cq : Real, 0 <= Cq /\ forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
        sourceDomSigmaOf (I := I) Phi k (hsrc k)
      forall y : SourceDomain (I := I) Phi k,
        metricCovDerivNorm (I := I) q
          (srcMetric (I := I) Phi hsrc htgt k 0)
          (refRes (I := I) Phi mc.limit.metric hsrc k) y <= Cq := by
  dsimp only
  intro q
  obtain ⟨Cq, hCq, hcov⟩ := D.init_cov q
  refine ⟨Cq, hCq, fun k y => ?_⟩
  have hk := hcov k y
  rw [D.domain_eq k] at hk
  simpa only [StepDCanonData.canonDomain, StepDCanonData.canonRef] using hk

end StepDCanonData

end HCGCompactness
end DifferentialGeometry
