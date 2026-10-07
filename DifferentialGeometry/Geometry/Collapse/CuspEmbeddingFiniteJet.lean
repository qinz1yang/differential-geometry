import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.FiniteJetRealization

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {δ : ℝ} {X : Set W.Carrier}

/-- At positive height, the finite jet of the given cusp embedding is realized
by a separate smooth local diffeomorphism inside the original collar and its image.
The point, derivative, and both charts remain those of the original embedding. -/
theorem CuspEmbedding.exists_partialDiffeomorph_eq_finiteJet
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (hpos : 0 < p.2.val 0) :
    ∃ Φ : PartialDiffeomorph halfCollarModel W.model CuspHalfSpace W.Carrier ∞,
      p ∈ Φ.source ∧ Φ.source ⊆ cuspDomain ∧
      Φ.target ⊆ e.toFun '' cuspDomain ∧
      Φ p = e.toFun p ∧
      mfderiv halfCollarModel W.model Φ p = mfderiv halfCollarModel W.model e.toFun p ∧
      ∀ k ≤ K + 1,
        iteratedFDeriv ℝ k
            (extChartAt W.model (e.toFun p) ∘ Φ ∘ (extChartAt halfCollarModel p).symm)
            (extChartAt halfCollarModel p p) =
          iteratedFDeriv ℝ k
            (extChartAt W.model (e.toFun p) ∘ e.toFun ∘ (extChartAt halfCollarModel p).symm)
            (extChartAt halfCollarModel p p) := by
  have hpint : halfCollarModel.IsInteriorPoint p := by
    change p ∈ (torusModel.prod (𝓡∂ 1)).interior (Torus × EuclideanHalfSpace 1)
    rw [ModelWithCorners.interior_prod]
    refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
    change (𝓡∂ 1).IsInteriorPoint p.2
    simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply,
      interior_range_modelWithCornersEuclideanHalfSpace, mem_setOf_eq,
      modelWithCornersEuclideanHalfSpace_apply] using hpos
  have hfpint : W.model.IsInteriorPoint (e.toFun p) := by
    rw [W.model.isInteriorPoint_iff_not_isBoundaryPoint]
    intro hb
    exact (ne_of_gt hpos) ((e.boundary_preimage hp).mp hb)
  have hdomain : IsOpen cuspDomain :=
    isOpen_lt (by fun_prop) continuous_const
  exact DifferentialGeometry.Manifold.exists_partialDiffeomorph_eq_finiteJet
    (e.contMDiffOn.contMDiffAt (hdomain.mem_nhds hp)) (by show 1 ≤ K + 1; omega)
    (e.isInvertible_mfderiv_at p hp) hpint hfpint hdomain hp
    e.isOpen_image_openness ⟨p, hp, rfl⟩

end DifferentialGeometry.Geometry.Collapse
