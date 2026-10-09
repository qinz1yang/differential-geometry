import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleBinderECM
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeRegistry

/-!
# Consumer of the E4 binder: the radial solid torus (X135)

The binder of `EdgeCircleBinderECM.lean` on the tree's concrete radial edge bundle
(`radialEdgeBundle`: a solid torus with boundary, base the circle, circle component = the whole
base, parametrized by the identity): the total space over the circle component is connected, its
circle-valued projection is a submersion, and through every boundary point runs a smooth boundary
curve with nonzero circle velocity. This is a compiled non-trivial inhabitant of the hypotheses of
the binder.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_BinderX135ECM :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

/-- The identity of the circle is a smooth embedding of the circle into the radial base. -/
theorem radial_isSmoothEmbedding_id_ECM :
    IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (id : Circle → radialEdgeBundle.Base) :=
  (Diffeomorph.refl (𝓡 1) Circle ∞).isSmoothEmbedding

theorem radial_totalC_connected_ECM :
    ConnectedSpace
      (EdgeBundle.TotalC_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM) :=
  EdgeBundle.connectedSpace_totalC_ECM radial_isSmoothEmbedding_id_ECM

theorem radial_totalProj_submersion_ECM
    (x : EdgeBundle.TotalC_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1)
      (EdgeBundle.totalProj_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM) x) :=
  EdgeBundle.surjective_mfderiv_totalProj_ECM radial_isSmoothEmbedding_id_ECM x

theorem radial_boundaryCurve_ECM
    (x : EdgeBundle.TotalC_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM)
    (hx : (𝓡∂ 3).IsBoundaryPoint x) :
    ∃ γ : ℝ → EdgeBundle.TotalC_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = x ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
          (EdgeBundle.totalProj_ECM (P := radialEdgeBundle) radial_isSmoothEmbedding_id_ECM ∘ γ)
          0 ≠ 0 :=
  EdgeBundle.exists_boundaryCurve_ECM radial_isSmoothEmbedding_id_ECM x hx

end GC.GraphManifold.Assembly.FC39P0.X135Radial
