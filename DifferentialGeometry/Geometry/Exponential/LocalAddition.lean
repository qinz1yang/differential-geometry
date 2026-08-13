import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Topology.FiberBundleT2
import Mathlib.Topology.Connected.LocallyConnected
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

def connCompOpen (p : M) : Opens M := by
  letI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨connectedComponent p, isOpen_connectedComponent⟩

def connCompPt (p : M) : connCompOpen (I := I) p :=
  ⟨p, mem_connectedComponent⟩

@[reducible] noncomputable def connCompConnected (p : M) :
    ConnectedSpace (connCompOpen (I := I) p) := by
  apply Subtype.connectedSpace
  simpa only [connCompOpen] using (isConnected_connectedComponent (x := p))

@[reducible] noncomputable def connCompCompact (p : M) :
    CompactSpace (connCompOpen (I := I) p) := by
  apply isCompact_iff_compactSpace.mp
  simpa only [connCompOpen] using
    (isClosed_connectedComponent (x := p)).isCompact

noncomputable def connCompMetric
    (g : SmoothRiemannianMetric I M) (p : M) :
    SmoothRiemannianMetric I (connCompOpen (I := I) p) := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  exact g.restrictOpen (I := I) (connCompOpen (I := I) p)

section

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

@[reducible] private noncomputable def connCompRiemBundle
    (g : SmoothRiemannianMetric I M) (p : M) :
    RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
  ⟨(connCompMetric (I := I) g p).toRiemannianMetric⟩

@[reducible] private noncomputable def connCompContBundle
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
      connCompRiemBundle (I := I) g p
    IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) := by
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  exact
    ⟨(connCompMetric (I := I) g p).inner,
      (connCompMetric (I := I) g p).contMDiff.continuous,
      fun _ _ _ => rfl⟩

@[reducible] private noncomputable def connCompEMetric
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
      connCompRiemBundle (I := I) g p
    PseudoEMetricSpace (connCompOpen (I := I) p) := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompContBundle (I := I) g p
  exact PseudoEMetricSpace.ofRiemannianMetric I (connCompOpen (I := I) p)

@[reducible] private noncomputable def connCompRiemMan
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
      connCompRiemBundle (I := I) g p
    letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
      connCompEMetric (I := I) g p
    IsRiemannianManifold I (connCompOpen (I := I) p) := by
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
    connCompEMetric (I := I) g p
  exact ⟨fun _ _ => rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem connComp_enorm
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
      connCompRiemBundle (I := I) g p
    ∀ (x : connCompOpen (I := I) p) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt ((connCompMetric (I := I) g p).inner x v v)) := by
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  intro x v
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  rfl

noncomputable def connDiagExp
    (g : SmoothRiemannianMetric I M) (p : M) :
    TangentBundle I (connCompOpen (I := I) p) →
      connCompOpen (I := I) p × connCompOpen (I := I) p := by
  letI : ConnectedSpace (connCompOpen (I := I) p) := connCompConnected (I := I) p
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompContBundle (I := I) g p
  letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
    connCompEMetric (I := I) g p
  letI : IsRiemannianManifold I (connCompOpen (I := I) p) :=
    connCompRiemMan (I := I) g p
  exact diagExp (I := I) (connCompMetric (I := I) g p)
    (connComp_enorm (I := I) g p)

end

noncomputable def connAddChart
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E × E :=
  let z : TangentBundle I (connCompOpen (I := I) p) :=
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))
  extChartAt (I.prod I) (connDiagExp (I := I) g p z) ∘
    connDiagExp (I := I) g p ∘
    (extChartAt I.tangent z).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem connAdd_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    connDiagExp (I := I) g p
        (⟨connCompPt (I := I) p, (0 : E)⟩ :
          TangentBundle I (connCompOpen (I := I) p)) =
      (connCompPt (I := I) p, connCompPt (I := I) p) := by
  classical
  letI : ConnectedSpace (connCompOpen (I := I) p) := connCompConnected (I := I) p
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompContBundle (I := I) g p
  letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
    connCompEMetric (I := I) g p
  letI : IsRiemannianManifold I (connCompOpen (I := I) p) :=
    connCompRiemMan (I := I) g p
  change diagExp (I := I) (connCompMetric (I := I) g p)
      (connComp_enorm (I := I) g p)
      (⟨connCompPt (I := I) p, (0 : E)⟩ :
        TangentBundle I (connCompOpen (I := I) p)) = _
  rw [diagExp_apply]
  exact Prod.ext rfl
    (expMapIntrinsic_zero (I := I) (connCompMetric (I := I) g p)
      (connComp_enorm (I := I) g p) (connCompPt (I := I) p))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem connAdd_cd
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (connDiagExp (I := I) g p)
      (⟨connCompPt (I := I) p, (0 : E)⟩ :
        TangentBundle I (connCompOpen (I := I) p)) := by
  classical
  letI : ConnectedSpace (connCompOpen (I := I) p) := connCompConnected (I := I) p
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompContBundle (I := I) g p
  letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
    connCompEMetric (I := I) g p
  letI : IsRiemannianManifold I (connCompOpen (I := I) p) :=
    connCompRiemMan (I := I) g p
  change ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
    (diagExp (I := I) (connCompMetric (I := I) g p)
      (connComp_enorm (I := I) g p))
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))
  exact diagExp_contMDiffAt_zero (I := I)
    (connCompMetric (I := I) g p) (connComp_enorm (I := I) g p)
    (connCompPt (I := I) p) n hn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem connAdd_fderiv
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (connAddChart (I := I) g p)
      (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E))
      (extChartAt I.tangent
        (⟨connCompPt (I := I) p, (0 : E)⟩ :
          TangentBundle I (connCompOpen (I := I) p))
        (⟨connCompPt (I := I) p, (0 : E)⟩ :
          TangentBundle I (connCompOpen (I := I) p))) := by
  classical
  letI : ConnectedSpace (connCompOpen (I := I) p) := connCompConnected (I := I) p
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  letI : RiemannianBundle
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompRiemBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connCompOpen (I := I) p ↦ TangentSpace I x) :=
    connCompContBundle (I := I) g p
  letI : PseudoEMetricSpace (connCompOpen (I := I) p) :=
    connCompEMetric (I := I) g p
  letI : IsRiemannianManifold I (connCompOpen (I := I) p) :=
    connCompRiemMan (I := I) g p
  simpa only [connAddChart, connDiagExp] using
    (diagExp_hasFDerivAt_zero_unipotent (I := I)
      (connCompMetric (I := I) g p) (connComp_enorm (I := I) g p)
      (connCompPt (I := I) p) n hn)

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
