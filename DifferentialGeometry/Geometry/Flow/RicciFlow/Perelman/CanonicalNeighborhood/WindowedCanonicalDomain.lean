import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.canonical_domain_subset_comparison_ball
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) :
    K.domain.carrier ⊆ riemannianClosedBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta) := by
  have hscalar : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hr : K.radius ≤ C1 := by
    simpa only [hscalar, Real.sqrt_one, div_one] using K.radius_upper
  intro y hy
  have hdist := K.inside_ball hy
  exact hdist.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.canonical_domain_subset_source
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) :
    K.domain.carrier ⊆ W.embedding.source := by
  exact (W.canonical_domain_subset_comparison_ball K hbuffer).trans
    ((riemannianClosedBallOf_mono (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (by linarith : modelRadius delta ≤ modelRadius delta + 1)).trans
      W.buffered_ball)

omit [T2Space M] [SigmaCompactSpace M] in
theorem WindowedModelWitness.mem_interior_image_canonical_domain
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) :
    x ∈ interior (W.embedding '' K.domain.carrier) := by
  rw [← K.domain.image_interior W.embedding (W.canonical_domain_subset_source K hbuffer)]
  exact ⟨W.model.basepoint, K.center_inside, W.base_map⟩

omit [SigmaCompactSpace M] in
def WindowedModelWitness.canonicalDomainImage
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) : CompactDomain M :=
  K.domain.map W.embedding (W.canonical_domain_subset_source K hbuffer)

omit [SigmaCompactSpace M] in
@[simp] theorem WindowedModelWitness.canonicalDomainImage_carrier
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) :
    (W.canonicalDomainImage K hbuffer).carrier = W.embedding '' K.domain.carrier := rfl

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.mem_interior_canonicalDomainImage
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) :
    x ∈ interior (W.canonicalDomainImage K hbuffer).carrier :=
  W.mem_interior_image_canonical_domain K hbuffer

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
