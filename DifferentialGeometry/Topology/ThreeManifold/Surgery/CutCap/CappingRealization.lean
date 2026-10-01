import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.ChildComponents
import DifferentialGeometry.Topology.Attachment.Basic

noncomputable section

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def SphericalTubeSystem.ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    DifferentialGeometry.Topology.SphericalTubeSystem P where
  Index := X.trace.tubes.Index
  finiteIndex := X.trace.tubes.finiteIndex
  tube := X.trace.tubes.tube
  smooth := X.tube_smooth
  disjoint := X.trace.tubes.disjoint

theorem SphericalTubeSystem.core_ofSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).core = X.trace.tubes.core := rfl

theorem SphericalTubeSystem.removedBand_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (a : X.trace.tubes.Index) :
    (SphericalTubeSystem.ofSmoothCutCapTransition X).removedBand a =
      X.trace.tubes.removedBand a := rfl

theorem SphericalTubeSystem.mem_surgeryRegion_ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (x : X.trace.tubes.core) :
    x.1 ∈ (SphericalTubeSystem.ofSmoothCutCapTransition X).surgeryRegion ↔
      ∃ a : X.trace.tubes.Index,
        x.1 ∈ X.trace.tubes.tube a ''
          {z : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeDomain |
            (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2} := by
  rw [DifferentialGeometry.Topology.SphericalTubeSystem.surgeryRegion]
  exact Set.mem_iUnion

theorem SmoothCutCapTransition.presentation_linearEquiv_eq {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (x : N.Carrier)
    (hf : Function.Bijective (mfderiv ThreeModel ThreeModel X.presentation x)) :
    (X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel X.presentation x).toLinearMap hf := by
  ext v
  rw [LinearEquiv.ofBijective_apply]
  change (X.presentation.mfderivToContinuousLinearEquiv (by simp) x :
    TangentSpace ThreeModel x → TangentSpace ThreeModel (X.presentation x)) v =
    mfderiv ThreeModel ThreeModel X.presentation x v
  rfl

theorem SmoothCutCapTransition.presentation_positive_toSurgery {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.orientation.orientation q
    | Sum.inr d => D.orientation.orientation d := by
  intro x
  obtain ⟨hf, hfx⟩ := X.presentation_positive x
  rw [X.presentation_linearEquiv_eq x hf]
  exact hfx

structure SphericalCappingCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) where
  capping : DifferentialGeometry.Topology.SphericalCapping P
    N (SphericalTubeSystem.ofSmoothCutCapTransition X)
  coreInclusion_eq : ∀ x, capping.coreInclusion x = X.trace.capping.coreInclusion x

structure SmoothCutCapCompletion {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) extends SphericalCappingCompletion X where
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core, ∃ q : Q.Carrier,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q ∧
        ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core,
      X.presentation (toSphericalCappingCompletion.capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : DifferentialGeometry.Topology.ClosedCell 3,
        X.presentation (toSphericalCappingCompletion.capping.cap b z) = Sum.inl q}
  presentation_positive :
    ∀ x : N.Carrier, (Orientation.map (Fin 3)
      ((X.presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv))
      (N.orientation.orientation x) =
    match X.presentation x with
    | Sum.inl q => Q.orientation.orientation q
    | Sum.inr d => D.orientation.orientation d

def SphericalCutCapTransition.ofSmoothCutCapTransition
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    DifferentialGeometry.Topology.SphericalCutCapTransition P
      Q where
  source_nonempty := X.source_nonempty
  tubes := SphericalTubeSystem.ofSmoothCutCapTransition X
  capped := N
  capping := h.capping
  discarded := D
  presentation := X.presentation
  presentation_positive := fun x => by
    exact h.presentation_positive x
  every_component_meets_core := h.every_component_meets_core
  retained_complement := h.retained_complement
  nontrivial := X.trace.nontrivial

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_tubes
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).tubes = SphericalTubeSystem.ofSmoothCutCapTransition X := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_presentation
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X) :
    ((SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = X.presentation := rfl

theorem SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion
    {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).capping.coreInclusion x = X.trace.capping.coreInclusion x :=
  h.coreInclusion_eq x

theorem SphericalCutCapTransition.retainedCore_iff {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (h : SmoothCutCapCompletion X)
    (x : X.trace.tubes.core) :
    x ∈ (SphericalCutCapTransition.ofSmoothCutCapTransition
        X h).retainedCore ↔ x ∈ X.trace.retainedCore := by
  rw [DifferentialGeometry.Topology.SphericalCutCapTransition.retainedCore,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology.retainedCore,
    SphericalCutCapTransition.ofSmoothCutCapTransition_presentation]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq] at hq
      exact hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by
      rw [SphericalCutCapTransition.ofSmoothCutCapTransition_coreInclusion X h x,
        X.presentation_eq]
      exact hq⟩

set_option autoImplicit false

local instance : ChartedSpace (EuclideanHalfSpace 3) (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance : IsManifold (𝓡∂ 3) ∞ (DifferentialGeometry.Topology.ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

private theorem sphereToClosedCell_norm
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ‖(DifferentialGeometry.Topology.sphereToClosedCell z).1‖ = 1 := by
  have h : dist z.1 (0 : EuclideanSpace ℝ (Fin 3)) = 1 := z.2
  rw [dist_eq_norm, sub_zero] at h
  exact h

private theorem closedCell_mem_closure_ballInterior (z : DifferentialGeometry.Topology.ClosedCell 3) :
    z ∈ closure {w : DifferentialGeometry.Topology.ClosedCell 3 | ‖w.1‖ < 1} := by
  rw [_root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ''
      {w : DifferentialGeometry.Topology.ClosedCell 3 | ‖w.1‖ < 1} = Metric.ball 0 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact hy
    · intro hx
      have h : ‖x‖ < 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
        exact hx
      exact ⟨⟨x, h.le⟩, h, rfl⟩
  rw [he, closure_ball (0 : EuclideanSpace ℝ (Fin 3)) one_ne_zero, mem_preimage,
    Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact z.property

theorem SmoothCutCapCompletion.retained_complement_of_sphericalCapping
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (K : DifferentialGeometry.Topology.SphericalCapping P
      N (SphericalTubeSystem.ofSmoothCutCapTransition X)) :
    (interior {q : Q.Carrier | ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core,
      X.presentation (K.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : DifferentialGeometry.Topology.ClosedCell 3,
        X.presentation (K.cap b z) = Sum.inl q} := by
  classical
  let T := SphericalTubeSystem.ofSmoothCutCapTransition X
  let e := X.presentation
  let S : Set Q.Carrier := {q | ∃ x : T.core, e (K.coreInclusion x) = Sum.inl q}
  let Tc : Set Q.Carrier := {q | ∃ b : T.Boundary,
    ∃ z : DifferentialGeometry.Topology.ClosedCell 3, e (K.cap b z) = Sum.inl q}
  have hUnion : IsCompact (⋃ b : T.Boundary, range (K.cap b)) :=
    isCompact_iUnion fun b => isCompact_range (K.cap b).continuous
  have hAclosed : IsClosed (e.toHomeomorph ⁻¹'
      (range (Sum.inl : Q.Carrier → Q.Carrier ⊕ D.Carrier))) :=
    (isClopen_range_inl (X := Q.Carrier) (Y := D.Carrier)).isClosed.preimage
      e.toHomeomorph.continuous
  have hTc : Tc = (fun q : Q.Carrier => Sum.inl q) ⁻¹'
      (e.toHomeomorph '' ((⋃ b : T.Boundary, range (K.cap b)) ∩
        (e.toHomeomorph ⁻¹' (range (Sum.inl : Q.Carrier → Q.Carrier ⊕ D.Carrier))))) := by
    ext q
    constructor
    · rintro ⟨b, z, hz⟩
      exact ⟨K.cap b z, ⟨mem_iUnion.mpr ⟨b, mem_range_self z⟩, ⟨q, hz.symm⟩⟩, hz⟩
    · rintro ⟨n, ⟨hnU, hnA⟩, hnq⟩
      obtain ⟨b, hb⟩ := mem_iUnion.mp hnU
      obtain ⟨z, rfl⟩ := hb
      exact ⟨b, z, hnq⟩
  have hTc_closed : IsClosed Tc := by
    rw [hTc]
    exact ((hUnion.inter_right hAclosed).image e.toHomeomorph.continuous).isClosed.preimage
      continuous_inl
  have hcover : S ∪ Tc = univ := by
    refine eq_univ_iff_forall.mpr fun q => ?_
    have hmem : e.toHomeomorph.symm (Sum.inl q) ∈
        range K.coreInclusion ∪ ⋃ b : T.Boundary, range (K.cap b) := by
      rw [K.exhaustive]
      trivial
    rcases hmem with h | h
    · left
      obtain ⟨x, hx⟩ := mem_range.mp h
      exact ⟨x, by rw [hx]; exact e.apply_symm_apply (Sum.inl q)⟩
    · right
      obtain ⟨b, hb⟩ := mem_iUnion.mp h
      obtain ⟨z, hz⟩ := mem_range.mp hb
      exact ⟨b, z, by rw [hz]; exact e.apply_symm_apply (Sum.inl q)⟩
  have hsub : Tcᶜ ⊆ interior S := by
    refine interior_maximal (fun q hq => ?_) hTc_closed.isOpen_compl
    have hmem : q ∈ S ∪ Tc := by rw [hcover]; trivial
    rcases hmem with h | h
    · exact h
    · exact absurd h hq
  have hmain : Tc ⊆ (interior S)ᶜ := by
    intro q hqT hqint
    obtain ⟨b, z, hz⟩ := hqT
    have hn : e.toHomeomorph.symm (Sum.inl q) = K.cap b z := by
      rw [← hz]
      exact Homeomorph.symm_apply_apply e.toHomeomorph _
    have hOpenMap1 : IsOpenMap (e.toHomeomorph.symm ∘ (Sum.inl : Q.Carrier → Q.Carrier ⊕ D.Carrier)) :=
      (Homeomorph.isOpenMap e.toHomeomorph.symm).comp isOpenMap_inl
    have hVopen : IsOpen (e.toHomeomorph.symm '' (Sum.inl '' interior S)) := by
      rw [← Set.image_comp]
      exact hOpenMap1 (interior S) isOpen_interior
    have hVsub : e.toHomeomorph.symm '' (Sum.inl '' interior S) ⊆ range K.coreInclusion := by
      rintro n ⟨u, ⟨v, hv, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := interior_subset hv
      refine ⟨x, ?_⟩
      rw [← hx]
      exact (Homeomorph.symm_apply_apply e.toHomeomorph _).symm
    have hnV : e.toHomeomorph.symm (Sum.inl q) ∈
        e.toHomeomorph.symm '' (Sum.inl '' interior S) :=
      ⟨Sum.inl q, ⟨q, hqint, rfl⟩, rfl⟩
    have hnint : e.toHomeomorph.symm (Sum.inl q) ∈ interior (range K.coreInclusion) :=
      interior_maximal hVsub hVopen hnV
    have hninter : e.toHomeomorph.symm (Sum.inl q) ∈
        range K.coreInclusion ∩ range (K.cap b) :=
      ⟨interior_subset hnint, ⟨z, hn.symm⟩⟩
    rw [K.core_cap_intersection b] at hninter
    obtain ⟨y, hy⟩ := mem_range.mp hninter
    have hcapz : K.cap b z = K.coreInclusion ((T.coreBoundarySphere b) y) := by
      rw [← hn]
      exact hy.symm
    obtain ⟨w, hw⟩ : ∃ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        DifferentialGeometry.Topology.sphereToClosedCell w = z := by
      refine ⟨(K.attaching b).symm y, ?_⟩
      have hb := K.boundary_eq b ((K.attaching b).symm y)
      have hat : K.attaching b ((K.attaching b).symm y) = y :=
        Diffeomorph.apply_symm_apply (K.attaching b) y
      rw [hat] at hb
      exact (K.cap_embedding b).isEmbedding.injective (hb.trans hcapz.symm)
    have hzc : z ∈ closure {w : DifferentialGeometry.Topology.ClosedCell 3 | ‖w.1‖ < 1} := by
      rw [← hw]
      exact closedCell_mem_closure_ballInterior _
    have himg : K.cap b z ∈
        closure (K.cap b '' {w : DifferentialGeometry.Topology.ClosedCell 3 | ‖w.1‖ < 1}) :=
      (image_closure_subset_closure_image (K.cap b).continuous) (mem_image_of_mem _ hzc)
    have hsubc : K.cap b '' {w : DifferentialGeometry.Topology.ClosedCell 3 | ‖w.1‖ < 1} ⊆
        (range K.coreInclusion)ᶜ := by
      rintro _ ⟨w, hwlt, rfl⟩
      have hwlt' : ‖w.1‖ < 1 := hwlt
      rintro ⟨x, hx⟩
      have hmem : K.cap b w ∈ range K.coreInclusion ∩ range (K.cap b) :=
        ⟨⟨x, hx⟩, mem_range_self w⟩
      rw [K.core_cap_intersection b] at hmem
      obtain ⟨y', hy'⟩ := mem_range.mp hmem
      have hy'' : K.coreInclusion ((T.coreBoundarySphere b) y') = K.cap b w := by
        simpa only [ContinuousMap.comp_apply] using hy'
      obtain ⟨w', hw'⟩ : ∃ w' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          DifferentialGeometry.Topology.sphereToClosedCell w' = w := by
        refine ⟨(K.attaching b).symm y', ?_⟩
        have hb := K.boundary_eq b ((K.attaching b).symm y')
        have hat : K.attaching b ((K.attaching b).symm y') = y' :=
          Diffeomorph.apply_symm_apply (K.attaching b) y'
        rw [hat] at hb
        exact (K.cap_embedding b).isEmbedding.injective (hb.trans hy'')
      have hnorm : ‖w.1‖ = 1 := by
        rw [← hw']
        exact sphereToClosedCell_norm w'
      exact absurd hnorm (by linarith)
    have hcl := closure_mono hsubc himg
    rw [closure_compl] at hcl
    have hnint' : K.cap b z ∈ interior (range K.coreInclusion) := by
      rw [← hn]
      exact hnint
    exact hcl hnint'
  refine Set.Subset.antisymm ?_ hmain
  intro q hq
  by_contra hqT
  exact hq (hsub hqT)

theorem SmoothCutCapCompletion.every_component_meets_core_of_sphericalCappingCompletion
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : SphericalCappingCompletion X) :
    ∀ c : ConnectedComponents Q.Carrier,
      ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core, ∃ q : Q.Carrier,
        X.presentation (h.capping.coreInclusion x) = Sum.inl q ∧ ConnectedComponents.mk q = c := by
  intro c
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (X.childCoreComponent c)
  obtain ⟨y, hy, -⟩ := X.childCore_mapsTo_child c ⟨x, hx⟩
  refine ⟨x, y.1, ?_, y.2⟩
  rw [h.coreInclusion_eq x, X.presentation_eq]
  exact hy

theorem SmoothCutCapCompletion.retained_complement_of_sphericalCappingCompletion
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : SphericalCappingCompletion X) :
    (interior {q : Q.Carrier | ∃ x : (SphericalTubeSystem.ofSmoothCutCapTransition X).core,
      X.presentation (h.capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : DifferentialGeometry.Topology.ClosedCell 3,
        X.presentation (h.capping.cap b z) = Sum.inl q} :=
  SmoothCutCapCompletion.retained_complement_of_sphericalCapping X h.capping

def SmoothCutCapCompletion.ofSphericalCappingCompletion
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : SphericalCappingCompletion X) : SmoothCutCapCompletion X where
  toSphericalCappingCompletion := h
  every_component_meets_core :=
    SmoothCutCapCompletion.every_component_meets_core_of_sphericalCappingCompletion X h
  retained_complement :=
    SmoothCutCapCompletion.retained_complement_of_sphericalCappingCompletion X h
  presentation_positive := X.presentation_positive_toSurgery

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
