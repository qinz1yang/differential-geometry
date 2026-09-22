import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckAxialReflection

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

def SpatialNeck.axialReflection (nk : SpatialNeck g eps p) : SpatialNeck g eps p := by
  have hU : ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹,
      cylinderAxialReflection y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro y hy
    simp only [cylinderAxialReflection_apply, mem_prod, mem_univ, true_and, mem_Ioo]
    exact ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := nk.Q_pos
    cylinder := nk.cylinder
    map := cylinderAxialReflection.trans nk.map
    center := nk.center
    center_eq := ?_
    domain := fun y hy => ⟨mem_univ _, nk.domain (hU y hy)⟩
    comparison := ?_ }
  · change nk.map (cylinderAxialReflection (nk.center, 0)) = p
    simpa only [cylinderAxialReflection_apply, neg_zero] using nk.center_eq
  · apply axialReflectionMetricComparison
      (fun s hs y v w => ?_) hU
      (fun y hy => nk.map.mdifferentiableAt (by simp) (nk.domain (hU y hy))) nk.comparison
    rw [cylinderAxialReflection_mfderiv, cylinderAxialReflection_mfderiv]
    exact CylinderReference.inner_axialReflection nk.cylinder le_rfl y v w

@[simp] theorem SpatialNeck.axialReflection_apply
    (nk : SpatialNeck g eps p) (q : Sphere 2) (t : ℝ) :
    nk.axialReflection.map (q, t) = nk.map (q, -t) := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
