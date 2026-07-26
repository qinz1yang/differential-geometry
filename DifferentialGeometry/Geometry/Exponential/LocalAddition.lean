import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Topology.FiberBundleT2
import Mathlib.Topology.Connected.LocallyConnected

set_option linter.unusedSectionVars false

/-!
# Component-local exponential addition

The intrinsic diagonal exponential developed in `DiagExpDerivative.lean` is
stated for a connected manifold.  Ricci-flow uniqueness, however, is stated on
an arbitrary compact manifold.  This file records the componentwise form needed
by an exponential-section chart without adding `ConnectedSpace M` to the
ambient theorem.

For `p : M`, its connected component is open because a manifold is locally
connected, and closed by general topology.  Hence on a compact manifold that
component is itself a compact connected manifold.  Restricting a smooth metric
to this open subtype therefore lets us reuse the already proved intrinsic
diagonal exponential, its zero-section smoothness, and its unipotent derivative.

This is deliberately a component-local producer.  It does not assert joint
smoothness of the chart-fixed `expMap g q` as `q` varies: that object uses the
arbitrarily selected chart at each `q`, so it is not the canonical moving-base
exponential.  The intrinsic `diagExp` on the connected component is the faithful
geometric object.

## Main declarations

* `connCompOpen` is the open connected component of a point.
* `connCompConnected` and `connCompCompact` provide local component instances
  to downstream consumers without installing global instances.
* `connDiagExp` is the intrinsic diagonal exponential for the restricted metric.
* `connAdd_cd` gives finite-order smoothness at the zero section.
* `connAdd_fderiv` gives the unipotent chart derivative used by Banach IFT.
-/

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

/-- The connected component of `p`, regarded as an open subtype. -/
def connCompOpen (p : M) : Opens M := by
  letI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨connectedComponent p, isOpen_connectedComponent⟩

/-- The point `p` in its open connected component. -/
def connCompPt (p : M) : connCompOpen (I := I) p :=
  ⟨p, mem_connectedComponent⟩

/-- The connected-space structure on `connCompOpen p`, exported as an explicit
producer rather than installed as a global instance. -/
@[reducible] noncomputable def connCompConnected (p : M) :
    ConnectedSpace (connCompOpen (I := I) p) := by
  apply Subtype.connectedSpace
  simpa only [connCompOpen] using (isConnected_connectedComponent (x := p))

/-- The compact-space structure on `connCompOpen p`, exported as an explicit
producer rather than installed as a global instance. -/
@[reducible] noncomputable def connCompCompact (p : M) :
    CompactSpace (connCompOpen (I := I) p) := by
  apply isCompact_iff_compactSpace.mp
  simpa only [connCompOpen] using
    (isClosed_connectedComponent (x := p)).isCompact

/-- Restriction of a smooth metric to the open connected component of `p`. -/
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

/-- The intrinsic diagonal exponential of the restricted metric on the open
connected component of `p`.

All metric and completeness instances are local to this definition.  In
particular, it introduces no ambient `ConnectedSpace M` instance. -/
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

/-- The chart expression of `connDiagExp` at the zero vector over `p`. -/
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
/-- On the connected component, the diagonal exponential sends the zero vector
over `p` to `(p,p)`. -/
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
/-- Finite-order smoothness of the component-local diagonal exponential at the
zero vector over `p`. -/
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
/-- The chart derivative of the component-local diagonal exponential at the
zero vector over `p` is the unipotent block equivalence
`(a,b) ↦ (a,a+b)`. -/
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
