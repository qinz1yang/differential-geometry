import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedTubeSystem
import DifferentialGeometry.Geometry.Neck.ScalarRetainedCore
import DifferentialGeometry.Geometry.Neck.BufferedRotation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private theorem componentMap_setCongr_injective {M : Type*} [TopologicalSpace M]
    {S T : Set M} (h : S = T) :
    Injective (Homeomorph.setCongr h).continuous.connectedComponentsMap := by
  cases h
  intro c d he
  have hid (c : ConnectedComponents S) :
      (Homeomorph.setCongr rfl : S ≃ₜ S).continuous.connectedComponentsMap c = c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  rw [hid, hid] at he
  exact he

variable {M : Type*} [TopologicalSpace M] {ι : Type*} {δ : ι → ℝ}
  {f f' : ∀ i, bufferedCylinder (δ i) → M}

section CuttingSphere
variable [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
  (hδ : ∀ i, 0 < δ i)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hf' : ∀ i, _root_.Topology.IsOpenEmbedding (f' i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hdisj' : Pairwise fun i j => Disjoint (range (f' i)) (range (f' j)))
  (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
  (hmap : ∀ i z, f' i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩)

theorem cuttingSphereComponent_map_of_sphere_reparametrization (b : ι × Bool) :
    (Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap)).continuous.connectedComponentsMap
      (cuttingSphereComponent hδ f' hf' hdisj' b) = cuttingSphereComponent hδ f hf hdisj b := by
  change ConnectedComponents.mk ((Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap))
    (cuttingSphereAttachment hδ f' (fun i => (hf' i).injective) hdisj' ⟨b, spherePoint⟩)) = _
  have he : (Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap))
      (cuttingSphereAttachment hδ f' (fun i => (hf' i).injective) hdisj' ⟨b, spherePoint⟩) =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, e b.1 spherePoint⟩ := by
    apply Subtype.ext
    exact hmap b.1 _
  rw [he]
  exact cuttingSphere_component_eq hδ f hf hdisj b (e b.1 spherePoint)

end CuttingSphere

section Scalar
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalarSublevelComponents_preimage_of_cutCore_eq
    (U : Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore f' = cutCore f) :
    scalarSublevelComponents U g f' K =
      (Homeomorph.setCongr hcore).continuous.connectedComponentsMap ⁻¹'
        scalarSublevelComponents U g f K := by
  ext c
  constructor
  · rintro ⟨x, hx, hmem, he⟩
    refine ⟨x, hx, hcore ▸ hmem, ?_⟩
    rw [← he]
    rfl
  · rintro ⟨x, hx, hmem, he⟩
    refine ⟨x, hx, hcore.symm ▸ hmem, ?_⟩
    apply componentMap_setCongr_injective hcore
    exact he

theorem retainedCore_image_of_cutCore_eq
    (U : Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore f' = cutCore f) :
    (Subtype.val : cutCore f' → M) '' retainedCore f' (scalarSublevelComponents U g f' K) =
      (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f K) := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U g K hcore]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Homeomorph.setCongr hcore p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(Homeomorph.setCongr hcore).symm p, ?_, rfl⟩
    change ConnectedComponents.mk ((Homeomorph.setCongr hcore) ((Homeomorph.setCongr hcore).symm p)) ∈ scalarSublevelComponents U g f K
    rw [Homeomorph.apply_symm_apply]
    exact hp

theorem cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization
    [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
    (U : Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hδ : ∀ i, 0 < δ i)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hf' : ∀ i, _root_.Topology.IsOpenEmbedding (f' i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hdisj' : Pairwise fun i j => Disjoint (range (f' i)) (range (f' j)))
    (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
    (hmap : ∀ i z, f' i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩)
    (b : ι × Bool) :
    cuttingSphereComponent hδ f' hf' hdisj' b ∈ scalarSublevelComponents U g f' K ↔
      cuttingSphereComponent hδ f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U g K
    (cutCore_eq_of_sphere_reparametrization e hmap)]
  change _ ∈ scalarSublevelComponents U g f K ↔ _
  rw [cuttingSphereComponent_map_of_sphere_reparametrization hδ hf hf' hdisj hdisj' e hmap b]

end Scalar
section Rotation
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable (f : ∀ i, bufferedCylinder (δ i) → M) (e : ι → E3 ≃ₗᵢ[ℝ] E3)

omit [TopologicalSpace M] in
theorem cutCore_comp_bufferedCylinderRotation :
    cutCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) = cutCore f := by
  apply cutCore_eq_of_sphere_reparametrization (fun i => (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (e i)).toEquiv)
  intro i z
  apply congrArg (f i)
  apply Subtype.ext
  exact bufferedCylinderRotation_apply (δ i) (e i) z

theorem isOpenEmbedding_comp_bufferedCylinderRotation
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (i : ι) :
    _root_.Topology.IsOpenEmbedding (f i ∘ bufferedCylinderRotation (δ i) (e i)) :=
  (hf i).comp (bufferedCylinderRotation (δ i) (e i)).toHomeomorph.isOpenEmbedding

omit [TopologicalSpace M] in
theorem pairwise_disjoint_range_comp_bufferedCylinderRotation
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j))) :
    Pairwise fun i j => Disjoint (range (f i ∘ bufferedCylinderRotation (δ i) (e i)))
      (range (f j ∘ bufferedCylinderRotation (δ j) (e j))) := by
  intro i j hij
  exact (hdisj hij).mono (range_comp_subset_range _ _) (range_comp_subset_range _ _)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem retainedCore_image_comp_bufferedCylinderRotation
    (U : Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ) :
    (Subtype.val : cutCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) → M) ''
      retainedCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i))
        (scalarSublevelComponents U g (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) K) =
      (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f K) :=
  retainedCore_image_of_cutCore_eq U g K (cutCore_comp_bufferedCylinderRotation f e)

theorem cuttingSphereComponent_mem_comp_bufferedCylinderRotation
    [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
    (U : Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ) (hδ : ∀ i, 0 < δ i)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j))) (b : ι × Bool) :
    cuttingSphereComponent hδ (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i))
      (isOpenEmbedding_comp_bufferedCylinderRotation f e hf)
      (pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj) b ∈
      scalarSublevelComponents U g (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) K ↔
    cuttingSphereComponent hδ f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  apply cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization U g K hδ hf
    (isOpenEmbedding_comp_bufferedCylinderRotation f e hf)
    hdisj (pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj)
    (fun i => (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (e i)).toEquiv) _ b
  intro i z
  apply congrArg (f i)
  apply Subtype.ext
  exact bufferedCylinderRotation_apply (δ i) (e i) z

end Rotation
end DifferentialGeometry.Topology.ThreeManifold.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.ThreeManifold.Surgery
universe u
private instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] {ι : Type*}
  (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
  {δ : ι → ℝ} {k : ι → ℕ} (N : ∀ i, NormalizedNeck g (δ i) (k i))
  (e : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
  (he : ∀ i, sphereDiffeo (n := 2) (e i) spherePoint = (N i).sphereMark)
  (side : ι → Bool)

theorem rotatedDatum_retainedCore_image (K : ℝ) :
    (Subtype.val : cutCore (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) → M) ''
      retainedCore (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i)))
        (scalarSublevelComponents U g (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) K) =
    (Subtype.val : cutCore (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) → M) ''
      retainedCore (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) (scalarSublevelComponents U g (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) K) := by
  have hf : (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) =
      (fun i => (fun q : bufferedCylinder (δ i) => ((N i).chart q).val) ∘ bufferedCylinderRotation (δ i) (e i)) := rfl
  rw [hf]
  exact retainedCore_image_comp_bufferedCylinderRotation (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) e U g K

theorem rotatedDatum_cuttingSphereComponent_mem [Finite ι] (K : ℝ)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding ((fun q : bufferedCylinder (δ i) => ((N i).chart q).val)))
    (hdisj : Pairwise fun i j => Disjoint (range ((fun q : bufferedCylinder (δ i) => ((N i).chart q).val))) (range ((fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) j)))
    (b : ι × Bool) :
    let f := (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val)
    let f' := fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))
    let hf' := isOpenEmbedding_comp_bufferedCylinderRotation f e hf
    let hdisj' := pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj
    cuttingSphereComponent (fun i => (N i).delta_pos) f' hf' hdisj' b ∈ scalarSublevelComponents U g f' K ↔
      cuttingSphereComponent (fun i => (N i).delta_pos) f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
  exact cuttingSphereComponent_mem_comp_bufferedCylinderRotation (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) e U g K
    (fun i => (N i).delta_pos) hf hdisj b

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
