import DifferentialGeometry.Topology.ThreeManifold.SmoothUncapping
import DifferentialGeometry.Topology.Manifold.ClosedBall.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoverClassification
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem nonempty_capCore_image_coreInclusion
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core) :
    Nonempty (CapCore (C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core))) := by
  obtain ⟨x,hx⟩ := cap.nonempty_carrier
  obtain ⟨F,hFs,_,hF,_⟩ := C.exists_core_neighborhood_partialDiffeomorph ⟨x,hK hx⟩
  have heq : F '' K = C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hK hz⟩,hz,(hF ⟨z,hK hz⟩).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,hF z⟩
  rw [← heq]
  exact cap.image_of_partialDiffeomorph F (hK.trans hFs)


theorem isPoincareStandard_component_of_capCore_union_cap
    {K : Set N.Carrier} (cap : CapCore K) (b : T.Boundary)
    (c : ConnectedComponents N.Carrier)
    (hcover : K ∪ range (C.cap b) = N.componentSet c) :
    isPoincareStandard (N.component c).Carrier := by
  let U := N.componentOpen c
  have hKU : K ⊆ U := by
    intro x hx
    change x ∈ N.componentSet c
    rw [← hcover]
    exact Or.inl hx
  have hfU (x : ClosedCell 3) : C.cap b x ∈ U := by
    change C.cap b x ∈ N.componentSet c
    rw [← hcover]
    exact Or.inr (mem_range_self x)
  obtain ⟨capU⟩ := cap.nonempty_preimage_open U hKU
  let f : ClosedCell 3 → U := fun x => ⟨C.cap b x, hfU x⟩
  have hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f := by
    apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph
      (I := 𝓡∂ 3) (J := 𝓡 3) (N := U) (g := f)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val U) (C.cap_embedding b)
      ((C.cap b).continuous.subtype_mk hfU)
    intro x
    rfl
  obtain ⟨B, hB, hBf⟩ := Manifold.exists_partialDiffeomorph_extension_closedCell f hf
  have hBimage : B '' Metric.closedBall (0 : ThreeSpace) 1 = range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_closedBall_zero_iff.mp hx⟩, (hBf _).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, mem_closedBall_zero_iff.mpr x.property, hBf x⟩
  have hcov : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪
      (Subtype.val ⁻¹' K : Set U) = univ := by
    rw [hBimage]
    apply eq_univ_of_forall
    intro y
    have hy : y.val ∈ K ∪ range (C.cap b) := by
      rw [hcover]
      exact y.property
    rcases hy with hy | ⟨x, hx⟩
    · exact Or.inr hy
    · exact Or.inl ⟨x, Subtype.ext hx⟩
  obtain ⟨W⟩ := nonempty_positiveComponent_of_ball_cap_cover B hB capU hcov
  exact isPoincareStandard_of_positiveComponent W


theorem isPoincareStandard_component_of_capCore_and_cap_cover
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ T.core)
    (b : T.Boundary) (c : ConnectedComponents N.Carrier)
    (hcover : (C.coreInclusion '' (Subtype.val ⁻¹' K : Set T.core)) ∪
      range (C.cap b) = N.componentSet c) :
    isPoincareStandard (N.component c).Carrier := by
  obtain ⟨capA⟩ := C.nonempty_capCore_image_coreInclusion cap hK
  exact C.isPoincareStandard_component_of_capCore_union_cap capA b c hcover


end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_capCore_and_cap_cover
    {K : Set M.Carrier} (cap : CapCore K) (hK : K ⊆ E.tubes.core)
    (b : E.tubes.Boundary) (x : E.tubes.core) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d)
    (hcover : (E.capping.coreInclusion '' (Subtype.val ⁻¹' K : Set E.tubes.core)) ∪
      range (E.capping.cap b) =
        E.capped.componentSet (ConnectedComponents.mk (E.capping.coreInclusion x))) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_capCore_and_cap_cover cap hK b
    (ConnectedComponents.mk (E.capping.coreInclusion x)) hcover
  obtain ⟨f⟩ := E.cappedDiscardedPresentationRealization x d hd
  exact isPoincareStandard_of_diffeomorph f.val.symm hstd

end DifferentialGeometry.Topology.SphericalCutCapTransition
