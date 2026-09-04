import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Topology.Covering.Fiber.Equivalence
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisBracket
import DifferentialGeometry.Topology.Covering.SemilocallySimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Finite.Defs
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem bonnet_myers_finite_fundamentalGroup_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [PseudoEMetricSpace M] [Inhabited M]
    [T2Space (TangentBundle I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnormBase : ∀ (xb : M) (v : TangentSpace I xb),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner xb v v)))
    (x : M) :
    Finite (FundamentalGroup M x) := by
  set UC := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
  set p :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
  have hcov :
      IsCoveringMap
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    Geometry.Riemannian.Topology.UniversalCover.proj_isCoveringMap
  have hpcM : PathConnectedSpace M :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  let gLift :
      SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := I) g
  let hRB :
      Bundle.RiemannianBundle
        (fun (xt :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I xt) :=
    ⟨gLift.toRiemannianMetric⟩
  have hSCH : SecondCountableTopology H :=
    ModelWithCorners.secondCountableTopology I
  have hSCM : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  have hBasisLift : ∀ x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
      DifferentialGeometry.Geometry.Connection.chartRiemannBasisIdentity
        (I := I) gLift x' :=
    fun x' =>
      DifferentialGeometry.Geometry.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) gLift x'
  have hBasisBase : ∀ x : M,
      DifferentialGeometry.Geometry.Connection.chartRiemannBasisIdentity
        (I := I) g x :=
    fun x =>
      DifferentialGeometry.Geometry.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) g x
  have hRicLift :
      RicciBoundedBelow (I := I) gLift (((Module.finrank ℝ E : ℝ) - 1) * K) :=
    Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_liftedMetric_of_base
      (I := I) (g := g) hRic hBasisLift hBasisBase
  have hRegUC :
      RegularSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace
      (M := M) I
  have hEnormCover :
      ∀ (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
        (v : TangentSpace I x'),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gLift.inner x' v v)) := by
    intro x' v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    have hinner : (inner ℝ v v : ℝ) = gLift.inner x' v v := rfl
    rw [hinner]
  let hUCem :
      PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ucPseudoEMetricSpace
      (I := I) (M := M) gLift
  have hRiemUC :
      IsRiemannianManifold I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold
      (I := I) (M := M) gLift
  have hCompUC :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_of_complete
      (I := I) (M := M) g hEnormBase hEnormCover
  have hCRBcover :
      IsContinuousRiemannianBundle E
        (fun (x' :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x') :=
    ⟨gLift.inner, gLift.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hT2TanCover :
      T2Space (TangentBundle I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)) :=
    inferInstance
  have hCompactUC :
      CompactSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    bonnet_myers_compactSpace_of_ricci_bound (E := E) gLift hdim hK hRicLift hEnormCover
  have hFinFibre :
      Finite
        ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          ⁻¹' {x}) :=
    Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact
      hcov x
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) x
  let e' :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
    ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩,
      by
        change
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
              (X := M)
              (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
            = x
        rfl⟩
  have hEquiv :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x})
        ≃ FundamentalGroup M x :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hcov x e'
  exact Finite.of_equiv _ hEquiv
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem bonnet_myers_finite_fundamentalGroup_of_complete_metric
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [Inhabited M]
    [T2Space (TangentBundle I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (x : M) :
    Finite (FundamentalGroup M x) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact bonnet_myers_finite_fundamentalGroup_of_ricci_bound (I := I) (M := M) g
    hdim hK hRic hEnorm x

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
