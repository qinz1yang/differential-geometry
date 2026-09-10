import DifferentialGeometry.Geometry.Curvature.SectionalRicciBound
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Connection

namespace Poincare.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem universalCover_compactSpace_of_positiveSectional
    (g : SmoothRiemannianMetric I M) (hsec : Poincare.Geometry.HasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) : CompactSpace (UniversalCover M) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hbaseNorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  let : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : RegularSpace (UniversalCover M) := UniversalCover.uc_regularSpace I
  let h := UniversalCover.liftedMetric (I := I) g
  let : RiemannianBundle (TangentSpace I : UniversalCover M → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : UniversalCover M → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hcoverNorm : IsMetricNorm (I := I) h :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) h x v
  let : PseudoEMetricSpace (UniversalCover M) := UniversalCover.ucPseudoEMetricSpace h
  let : IsRiemannianManifold I (UniversalCover M) := UniversalCover.isRiemannianManifold h
  let : CompleteSpace (UniversalCover M) :=
    UniversalCover.completeSpace_of_complete g hbaseNorm hcoverNorm
  obtain ⟨k, hk, hRic⟩ := hsec.exists_positive_ricci_bound hdim
  have hRicLift : BonnetMyers.RicciBoundedBelow h (((Module.finrank ℝ E : ℝ) - 1) * k) :=
    UniversalCover.ricciBoundedBelow_liftedMetric_of_base hRic
      (fun x => chartRiemannBasisIdentity_LeviCivita h x)
      (fun x => chartRiemannBasisIdentity_LeviCivita g x)
  exact BonnetMyers.bonnet_myers_compactSpace_of_ricci_bound h hdim hk hRicLift hcoverNorm

end Poincare.Geometry.Riemannian
