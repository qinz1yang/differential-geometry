import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreComponentRetraction
import DifferentialGeometry.Topology.Manifold.InteriorImage

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.Topology.Manifold

theorem isOpen_image_of_isImmersion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I' : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {f : M → N} (hf : IsImmersion I' J ∞ f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E')
    {W : Set M} (hW : IsOpen W) (hWi : W ⊆ I'.interior M) : IsOpen (f '' W) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxW, rfl⟩
  exact immersion_image_mem_nhds (hf.isImmersionAt x) hdim (hWi hxW) (hW.mem_nhds hxW)

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem isOpen_childCap_image_of_disjoint_boundary (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {W : Set ThreeBall} (hW : IsOpen W)
    (hWi : W ⊆ (Set.range sphereToThreeBall)ᶜ) :
    IsOpen (E.childCap c b '' W) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := E.ballSmooth
  have hInt : W ⊆ (𝓡∂ 3).interior ThreeBall := by
    intro x hx
    simp only [ModelWithCorners.interior, Set.mem_ofPred_eq]
    rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
    intro hb
    exact hWi hx (by rw [← E.ball_boundary]; exact hb)
  have hcap : IsOpen ((E.trace.capping.cap b.1) '' W) :=
    DifferentialGeometry.Topology.Manifold.isOpen_image_of_isImmersion
      (E.cap_smooth b.1).isImmersion rfl hW hInt
  have hpres : IsOpen (E.trace.presentation '' ((E.trace.capping.cap b.1) '' W)) :=
    E.trace.presentation.isOpenMap _ hcap
  have hEq : (Sum.inl '' (Subtype.val '' (E.childCap c b '' W)) :
        Set (Q.Carrier ⊕ D.Carrier)) =
      E.trace.presentation '' ((E.trace.capping.cap b.1) '' W) := by
    rw [Set.image_image]
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨z, ⟨x, hxW, rfl⟩, hzy⟩
      exact ⟨E.trace.capping.cap b.1 x, ⟨x, hxW, rfl⟩, (E.childCapFun_eq c b x).trans hzy⟩
    · rintro y ⟨z, ⟨x, hxW, rfl⟩, hzy⟩
      exact ⟨E.childCap c b x, ⟨x, hxW, rfl⟩, (E.childCapFun_eq c b x).symm.trans hzy⟩
  have hQ : IsOpen ((Subtype.val '' (E.childCap c b '' W)) : Set Q.Carrier) := by
    have hsum : IsOpen (Sum.inl '' (Subtype.val '' (E.childCap c b '' W)) :
        Set (Q.Carrier ⊕ D.Carrier)) := hEq ▸ hpres
    have h1 : IsOpen (Sum.inl ⁻¹' (Sum.inl '' (Subtype.val '' (E.childCap c b '' W)) :
        Set (Q.Carrier ⊕ D.Carrier))) := (isOpen_sum_iff.mp hsum).1
    rwa [Set.preimage_image_eq _ Sum.inl_injective] at h1
  exact isOpen_induced_iff.mpr ⟨_, hQ, Set.preimage_image_eq _ Subtype.val_injective⟩

noncomputable def childCapSeam (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) :
    C(Sphere 2, E.ChildCore c) where
  toFun y := ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 y), b.2 _⟩
  continuous_toFun :=
    Continuous.subtype_mk ((E.trace.tubes.coreBoundarySphere b.1).continuous.comp
      (E.trace.capping.attaching b.1).continuous) _

theorem childCap_comp_sphereToThreeBall (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    (E.childCap c b).comp sphereToThreeBall =
      (E.childCoreInclusion c).comp (E.childCapSeam c b) := by
  ext y
  exact congrArg Subtype.val (E.childCap_boundary_eq c b y)

def childCoreCapCoverProducer : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier → Nonempty (E.ChildCarrierCoreCapCover c)

theorem simplyConnectedSpace_childCarrier_of_cover_univ_V (c : ConnectedComponents Q.Carrier)
    (d : E.ChildCarrierCoreCapCover c) (hV : d.V = univ) :
    SimplyConnectedSpace (E.ChildCarrier c) :=
  (Homeomorph.Set.univ (E.ChildCarrier c)).toHomotopyEquiv.simplyConnectedSpace_iff.mp
    (hV ▸ d.simplyConnected_V)

theorem range_childCoreInclusion_eq_univ_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    Set.range (E.childCoreInclusion c) = univ := by
  have h := E.range_childCoreInclusion_union_range_childCap c
  rw [Set.iUnion_eq_empty.mpr fun b => (IsEmpty.false b).elim, Set.union_empty] at h
  exact h

noncomputable def childCoreHomeomorphOfIsEmptyChildCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    E.ChildCore c ≃ₜ E.ChildCarrier c :=
  ((E.childCoreInclusion_isEmbedding c).toHomeomorph.trans
      (Homeomorph.setCongr (E.range_childCoreInclusion_eq_univ_of_isEmpty_childCapBoundary c))).trans
    (Homeomorph.Set.univ (E.ChildCarrier c))

theorem nonempty_childCarrierCoreCapCover_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)]
    (hsc : SimplyConnectedSpace (E.ChildCarrier c)) :
    Nonempty (E.ChildCarrierCoreCapCover c) := by
  let Φ := E.childCoreHomeomorphOfIsEmptyChildCapBoundary c
  have hΦ : ∀ x : E.ChildCore c, Φ x = E.childCoreInclusion c x := fun _ => rfl
  obtain ⟨y₀, hy₀⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  let ρ : C(↥(univ : Set (E.ChildCarrier c)), E.ChildCore c) :=
    ⟨fun y => Φ.symm (y : E.ChildCarrier c), Φ.symm.continuous.comp continuous_subtype_val⟩
  have hρ : ∀ x : E.ChildCore c, ρ ⟨E.childCoreInclusion c x, mem_univ _⟩ = x := by
    intro x
    change Φ.symm (E.childCoreInclusion c x) = x
    rw [← hΦ x, Φ.symm_apply_apply]
  have hVsc : SimplyConnectedSpace ↥(univ : Set (E.ChildCarrier c)) :=
    (Homeomorph.Set.univ (E.ChildCarrier c)).toHomotopyEquiv.simplyConnectedSpace_iff.mpr hsc
  have hpc : PathConnectedSpace ↥(univ ∩ univ : Set (E.ChildCarrier c)) := by
    rw [Set.inter_self]
    exact (Homeomorph.Set.univ (E.ChildCarrier c)).symm.surjective.pathConnectedSpace
      (Homeomorph.Set.univ (E.ChildCarrier c)).symm.continuous
  have hcomp : (childCoreInclusionRestrict E c fun _ _ => mem_univ _).comp ρ =
      ContinuousMap.id ↥(univ : Set (E.ChildCarrier c)) := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    change E.childCoreInclusion c (ρ y) = (y : E.ChildCarrier c)
    rw [← hΦ (ρ y)]
    change Φ (Φ.symm (y : E.ChildCarrier c)) = (y : E.ChildCarrier c)
    exact Φ.apply_symm_apply _
  exact ⟨univ, univ, Φ ⟨y₀, hy₀⟩, isOpen_univ, isOpen_univ, Set.union_self univ, mem_univ _,
    mem_univ _, fun _ _ => mem_univ _, fun _ _ => mem_univ _, hVsc, hpc, ρ, (by
      apply ContinuousMap.ext
      intro x
      exact hρ x), hcomp ▸ ContinuousMap.Homotopic.refl _⟩

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
