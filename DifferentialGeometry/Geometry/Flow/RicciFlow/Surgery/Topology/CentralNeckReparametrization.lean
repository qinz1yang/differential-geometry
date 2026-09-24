import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRotationCutCore

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type*} {ι : Type*} {δ : ι → ℝ}

theorem removedSlab_eq_of_central_sphere_reparametrization {d : ℝ}
    {f g : bufferedCylinder d → M}
    (e : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2)
    (hmap : ∀ z ∈ centralDomain d, g z = f ⟨(e z.val.1, z.val.2), z.property⟩) :
    removedSlab g = removedSlab f := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨(e z.val.1, z.val.2), z.property⟩, hz, (hmap z hz).symm⟩
  · rintro _ ⟨z, hz, rfl⟩
    let w : bufferedCylinder d := ⟨(e.symm z.val.1, z.val.2), z.property⟩
    refine ⟨w, hz, ?_⟩
    rw [hmap w hz]
    apply congrArg f
    exact Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

theorem cutCore_eq_of_central_sphere_reparametrization
    {f g : ∀ i : ι, bufferedCylinder (δ i) → M}
    (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
    (hmap : ∀ i z, z ∈ centralDomain (δ i) → g i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩) :
    cutCore g = cutCore f := by
  unfold cutCore
  congr 1
  exact iUnion_congr fun i => removedSlab_eq_of_central_sphere_reparametrization (e i) (hmap i)

section Scalar
variable [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]
  {f g : ∀ i : ι, bufferedCylinder (δ i) → M}

theorem mem_scalarSublevelComponents_of_cutCore_eq
    (U : Opens M) (metric : DifferentialGeometry.SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore g = cutCore f) (x : cutCore g) :
    ConnectedComponents.mk x ∈ scalarSublevelComponents U metric g K ↔
      ConnectedComponents.mk (Homeomorph.setCongr hcore x) ∈ scalarSublevelComponents U metric f K := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U metric K hcore]
  rfl

end Scalar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
