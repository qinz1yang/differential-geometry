import DifferentialGeometry.Geometry.Thurston.ElementaryModels
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Topology.ThreeManifold.SphereMappingTorusTrivialization
import DifferentialGeometry.Topology.Diffeomorph.Product
namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem flatCircle_model_atlas :
    ModelAtlas AddCircle.flatMetric (DifferentialGeometry.euclideanMetric (E := ℝ)) := by
  intro z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨e, ht, he⟩ := AddCircle.isLocalDiffeomorph_coe t
  refine ⟨e, ?_, ?_⟩
  · convert e.toPartialEquiv.map_source ht using 1
    exact he ht
  · intro y hy v w
    have hnear : (fun t : ℝ => (t : AddCircle (1 : ℝ))) =ᶠ[nhds y] e :=
      Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hy) he
    have hder : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun t : ℝ => (t : AddCircle (1 : ℝ))) y : ℝ →L[ℝ] ℝ) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) e y := hnear.mfderiv_eq
    rw [← he hy, ← hder]
    exact (AddCircle.flatMetric_inner_mfderiv_coe y v w).trans (mul_comm (show ℝ from v) (show ℝ from w))

abbrev PeriodicCylinder := SpatialNeckSphere × AddCircle (1 : ℝ)
def periodicCylinderMetric : SmoothRiemannianMetric SpatialNeckCylinderModel PeriodicCylinder :=
  (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).prod AddCircle.flatMetric

theorem periodicCylinder_model_atlas :
    CompleteModelAtlas periodicCylinderMetric sphericalProductModelMetric := by
  refine ⟨RiemannianMetricComplete.of_compact _, ?_⟩
  intro x
  obtain ⟨e, hx, he⟩ := flatCircle_model_atlas x.2
  let d := DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (Diffeomorph.refl (𝓡 2) SpatialNeckSphere ∞).toPartialDiffeomorph e
  refine ⟨d, ⟨Set.mem_univ x.1, hx⟩, ?_⟩
  rintro ⟨y,z⟩ hy ⟨v,a⟩ ⟨w,b⟩
  have hd : mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel d (y,z) =
      (mfderiv (𝓡 2) (𝓡 2) id y).prodMap (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) e z) :=
    mfderiv_prodMap mdifferentiableAt_id (e.mdifferentiableAt (by decide) hy.2)
  rw [hd, mfderiv_id]
  change (periodicCylinderMetric.inner (y,e z))
    (v,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) e z a)
    (w,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) e z b) = _
  exact (SmoothRiemannianMetric.prod_inner (I := 𝓡 2) (J := 𝓘(ℝ,ℝ))
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) AddCircle.flatMetric
    (y,e z) (v,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) e z a)
    (w,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) e z b)).trans (by
      have hc := he z hy.2 a b
      change _ = _ + a * b
      rw [hc]
      exact congrArg (_ + ·) (mul_comm b a))

def sphereTwoTimesCircleToPeriodic :
    DifferentialGeometry.Topology.SphereTwoTimesCircle ≃ₘ⟮(𝓡 2).prod (𝓡 1),
      SpatialNeckCylinderModel⟯ PeriodicCylinder :=
  (Diffeomorph.refl (𝓡 2) SpatialNeckSphere ∞).prodCongrCross
    DifferentialGeometry.Topology.addCircleOneDiffeomorphSphereOne.symm

def sphereTwoTimesCircleMetric : SmoothRiemannianMetric ((𝓡 2).prod (𝓡 1))
    DifferentialGeometry.Topology.SphereTwoTimesCircle :=
  Diffeomorph.pullbackMetricCross periodicCylinderMetric sphereTwoTimesCircleToPeriodic

theorem sphereTwoTimesCircle_complete_model_atlas :
    CompleteModelAtlas sphereTwoTimesCircleMetric sphericalProductModelMetric :=
  periodicCylinder_model_atlas.pullback sphereTwoTimesCircleToPeriodic

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem sphereTwoTimesCircle_factor_geometry
    (f : M ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ DifferentialGeometry.Topology.SphereTwoTimesCircle) :
    ∃ g : SmoothRiemannianMetric (𝓡 3) M,
      CompleteModelAtlas g sphericalProductModelMetric :=
  ⟨Diffeomorph.pullbackMetricCross sphereTwoTimesCircleMetric f,
    sphereTwoTimesCircle_complete_model_atlas.pullback f⟩

end
end GC.Geometry
