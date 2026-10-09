import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierSeamCollarReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierStarCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreComponent
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.VanKampen.HomotopyRetract

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff ContinuousMap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem disjoint_range_childCap {c : ConnectedComponents Q.Carrier}
    {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂) :
    Disjoint (Set.range (E.childCap c b₁)) (Set.range (E.childCap c b₂)) := by
  refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  obtain ⟨z₁, rfl⟩ := hx₁
  obtain ⟨z₂, hz⟩ := hx₂
  have hne' : b₁.1 ≠ b₂.1 := fun h => hne (Subtype.ext h)
  have hpres : E.trace.presentation (E.trace.capping.cap b₂.1 z₂) =
      E.trace.presentation (E.trace.capping.cap b₁.1 z₁) := by
    rw [E.childCapFun_eq c b₁ z₁, E.childCapFun_eq c b₂ z₂]
    exact congrArg Sum.inl (congrArg Subtype.val hz)
  have hcap : E.trace.capping.cap b₂.1 z₂ = E.trace.capping.cap b₁.1 z₁ :=
    E.trace.presentation.injective hpres
  exact Set.disjoint_left.mp (E.trace.capping.cap_disjoint hne')
    (Set.mem_range_self z₁) ⟨z₂, hcap⟩

theorem isClosed_range_childCap (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) : IsClosed (Set.range (E.childCap c b)) :=
  (isCompact_range (E.childCap c b).continuous).isClosed

private theorem eq_empty_or_eq_empty_of_isPreconnected_of_isClosed_disjoint
    {α : Type*} [TopologicalSpace α] {s t t' : Set α} (hs : IsPreconnected s)
    (ht : IsClosed t) (ht' : IsClosed t') (hsub : s ⊆ t ∪ t')
    (hdisj : Disjoint t t') : s ∩ t = ∅ ∨ s ∩ t' = ∅ := by
  rcases Set.eq_empty_or_nonempty (s ∩ t) with h1 | h1
  · exact Or.inl h1
  rcases Set.eq_empty_or_nonempty (s ∩ t') with h2 | h2
  · exact Or.inr h2
  exact absurd ((isPreconnected_closed_iff.mp hs) t t' ht ht' hsub h1 h2) (by
    rintro ⟨z, _, hzt, hzt'⟩
    exact Set.disjoint_left.mp hdisj hzt hzt')

theorem not_simplyConnectedSpace_of_capRange_subset_of_two_caps
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    {W : Set (E.ChildCarrier c)}
    (h₁ : Set.range (E.childCap c b₁) ⊆ W) (h₂ : Set.range (E.childCap c b₂) ⊆ W)
    (hW : W ⊆ ⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) :
    ¬ SimplyConnectedSpace ↥W := by
  classical
  intro hsc
  have hpre : IsPreconnected (univ : Set ↥W) :=
    (pathConnectedSpace_iff_univ.mp (inferInstance : PathConnectedSpace ↥W)).isConnected.isPreconnected
  set t : Set ↥W := {x | (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b₁)} with ht_def
  set t' : Set ↥W := ⋃ b : E.ChildCapBoundary c,
    {x | b ≠ b₁ ∧ (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b)} with ht'_def
  have ht : IsClosed t := (E.isClosed_range_childCap c b₁).preimage continuous_subtype_val
  have ht' : IsClosed t' := by
    rw [ht'_def]
    refine isClosed_iUnion_of_finite fun b => ?_
    by_cases hb : b = b₁
    · have hset : {x : ↥W | b ≠ b₁ ∧ (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b)} =
          ∅ := by
        ext x
        simp [hb]
      rw [hset]
      exact isClosed_empty
    · have hset : {x : ↥W | b ≠ b₁ ∧ (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b)} =
          {x : ↥W | (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b)} := by
        ext x
        simp [hb]
      rw [hset]
      exact ((E.isClosed_range_childCap c b).preimage continuous_subtype_val)
  have hsub : (univ : Set ↥W) ⊆ t ∪ t' := by
    intro x _
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hW x.2)
    by_cases hbb : b = b₁
    · refine Or.inl ?_
      rw [ht_def]
      simpa [hbb] using hb
    · refine Or.inr ?_
      rw [ht'_def]
      exact Set.mem_iUnion.mpr ⟨b, hbb, hb⟩
  have hdisj : Disjoint t t' := by
    refine Set.disjoint_left.mpr fun x hxt hxt' => ?_
    rw [ht'_def] at hxt'
    obtain ⟨b, hbne, hb⟩ := Set.mem_iUnion.mp hxt'
    have hx₁ : (x : E.ChildCarrier c) ∈ Set.range (E.childCap c b₁) := by
      rw [ht_def] at hxt
      exact hxt
    exact Set.disjoint_left.mp
      (E.disjoint_range_childCap (b₁ := b) (b₂ := b₁) hbne) hb hx₁
  rcases eq_empty_or_eq_empty_of_isPreconnected_of_isClosed_disjoint hpre ht ht' hsub hdisj
    with h | h
  · have ht0 : t = ∅ := by simpa using h
    have hmem : (⟨E.childCap c b₁ ⟨(0 : ThreeSpace), by simp⟩,
        h₁ (Set.mem_range_self _)⟩ : ↥W) ∈ t := by
      rw [ht_def]
      exact Set.mem_range_self _
    rw [ht0] at hmem
    exact hmem
  · have ht'0 : t' = ∅ := by simpa using h
    have hmem : (⟨E.childCap c b₂ ⟨(0 : ThreeSpace), by simp⟩,
        h₂ (Set.mem_range_self _)⟩ : ↥W) ∈ t' := by
      rw [ht'_def]
      exact Set.mem_iUnion.mpr ⟨b₂, Ne.symm hne, Set.mem_range_self _⟩
    rw [ht'0] at hmem
    exact hmem

theorem not_simplyConnectedSpace_iUnion_range_childCap_of_two_caps
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂) :
    ¬ SimplyConnectedSpace ↥(⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) :=
  E.not_simplyConnectedSpace_of_capRange_subset_of_two_caps c hne
    (Set.subset_iUnion (fun b => Set.range (E.childCap c b)) b₁)
    (Set.subset_iUnion (fun b => Set.range (E.childCap c b)) b₂) (Subset.refl _)

structure ChildCarrierCollaredStarCover (c : ConnectedComponents Q.Carrier) : Type u where
  U : Set (E.ChildCarrier c)
  V : E.ChildCapBoundary c → Set (E.ChildCarrier c)
  isOpen_U : IsOpen U
  isOpen_V : ∀ b, IsOpen (V b)
  cover : U ∪ (⋃ b, V b) = univ
  disjoint_V : Pairwise fun b b' => Disjoint (V b) (V b')
  core_subset_U : Set.range (E.childCoreInclusion c) ⊆ U
  cap_subset_V : ∀ b, Set.range (E.childCap c b) ⊆ V b
  retraction : C(↥U, E.ChildCore c)
  retraction_comp_inclusion :
    retraction.comp (E.childCoreInclusionRestrict c core_subset_U) =
      ContinuousMap.id (E.ChildCore c)
  inclusion_comp_retraction_homotopic :
    ((E.childCoreInclusionRestrict c core_subset_U).comp retraction).Homotopic
      (ContinuousMap.id ↥U)
  ball_homotopy_V : ∀ b, Nonempty (↥(V b) ≃ₕ ThreeBall)
  sphere_homotopy_inter : ∀ b, Nonempty (↥(U ∩ V b) ≃ₕ Sphere 2)

namespace ChildCarrierCollaredStarCover

variable {E : SmoothCutCapTransition P Q D N} {c : ConnectedComponents Q.Carrier}
  (d : E.ChildCarrierCollaredStarCover c)

theorem simplyConnectedSpace_U (hcore : SimplyConnectedSpace (E.ChildCore c)) :
    SimplyConnectedSpace ↥d.U :=
  (homotopyEquivOfRetraction (E.childCoreInclusionRestrict c d.core_subset_U) d.retraction
    d.retraction_comp_inclusion d.inclusion_comp_retraction_homotopic).simplyConnectedSpace_iff.mp
    hcore

theorem simplyConnectedSpace_V (b : E.ChildCapBoundary c) : SimplyConnectedSpace ↥(d.V b) :=
  (Classical.choice (d.ball_homotopy_V b)).simplyConnectedSpace

theorem simplyConnectedSpace_inter (b : E.ChildCapBoundary c) :
    SimplyConnectedSpace ↥(d.U ∩ d.V b) :=
  @ContinuousMap.HomotopyEquiv.simplyConnectedSpace _ ↥(Sphere 2) _ _
    DifferentialGeometry.Topology.sphereTwoSimplyConnectedSpace
    (Classical.choice (d.sphere_homotopy_inter b))

theorem pathConnectedSpace_inter (b : E.ChildCapBoundary c) : PathConnectedSpace ↥(d.U ∩ d.V b) :=
  ((simply_connected_iff_paths_homotopic (Y := ↥(d.U ∩ d.V b))).mp
    (d.simplyConnectedSpace_inter b)).1

end ChildCarrierCollaredStarCover

theorem simplyConnectedSpace_childCarrier_of_collaredStarCover (c : ConnectedComponents Q.Carrier)
    (hcore : SimplyConnectedSpace (E.ChildCore c)) (d : E.ChildCarrierCollaredStarCover c) :
    SimplyConnectedSpace (E.ChildCarrier c) :=
  @child_simplyConnected_of_starCover P Q D N E c d.U d.V d.isOpen_U d.isOpen_V d.cover
    d.disjoint_V (d.simplyConnectedSpace_U hcore) (fun b => d.simplyConnectedSpace_V b)
    (fun b => d.simplyConnectedSpace_inter b)

def childCollaredStarCoverProducer : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      Nonempty (E.ChildCarrierCollaredStarCover c)

def ChildCoreSimplyConnected : Prop :=
  ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (E.ChildCore c)

def ComponentwisePuncturedCoreSimplyConnected : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

def childCoreSimplyConnectedOfParent : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      SimplyConnectedSpace (E.ChildCore c)

def ComponentwisePuncturedCoreOfParent : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
      SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

theorem simplyConnectedSpace_puncturedCoreComponent_iff_childCore
    (c : ConnectedComponents Q.Carrier) :
    SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)) ↔
      SimplyConnectedSpace (E.ChildCore c) :=
  E.trace.tubes.simplyConnectedSpace_puncturedCoreComponent_iff_coreComponent
    (fun a => E.tube_smooth a) (E.childCoreComponent c)

theorem componentwisePuncturedCore_iff_childCoreSimplyConnected :
    E.ComponentwisePuncturedCoreSimplyConnected ↔ E.ChildCoreSimplyConnected :=
  ⟨fun h c => (E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mp (h c),
    fun h c => (E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mpr (h c)⟩

theorem componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent :
    E.ComponentwisePuncturedCoreOfParent ↔ E.childCoreSimplyConnectedOfParent :=
  ⟨fun h c hpar => (E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mp (h c hpar),
    fun h c hpar => (E.simplyConnectedSpace_puncturedCoreComponent_iff_childCore c).mpr (h c hpar)⟩

theorem childCoreSimplyConnectedOfParent_of_childCoreSimplyConnected
    (h : E.ChildCoreSimplyConnected) : E.childCoreSimplyConnectedOfParent :=
  fun c _ => h c

theorem child_simplyConnected_of_producers (hcover : E.childCollaredStarCoverProducer)
    (hcore : E.childCoreSimplyConnectedOfParent) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.simplyConnectedSpace_childCarrier_of_collaredStarCover c (hcore c inferInstance)
    (hcover c inferInstance).some

theorem child_simplyConnected_of_puncturedCoreProducer
    (hcover : E.childCollaredStarCoverProducer)
    (hpc : E.ComponentwisePuncturedCoreOfParent) (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_producers hcover
    ((E.componentwisePuncturedCoreOfParent_iff_childCoreSimplyConnectedOfParent).mp hpc) c

theorem childCoreSimplyConnectedOfParent_of_childCarrierSimplyConnected
    (hhe : ∀ c : ConnectedComponents Q.Carrier, Nonempty (E.ChildCore c ≃ₕ E.ChildCarrier c))
    (hcar : ∀ c : ConnectedComponents Q.Carrier,
      SimplyConnectedSpace (P.component (E.childParent c)).Carrier →
        SimplyConnectedSpace (E.ChildCarrier c)) :
    E.childCoreSimplyConnectedOfParent :=
  fun c h => @ContinuousMap.HomotopyEquiv.simplyConnectedSpace _ (E.ChildCarrier c) _ _
    (hcar c h) (hhe c).some

theorem nonempty_childCarrierCollaredStarCover_of_isEmpty_childCapBoundary
    (c : ConnectedComponents Q.Carrier) [IsEmpty (E.ChildCapBoundary c)] :
    Nonempty (E.ChildCarrierCollaredStarCover c) := by
  classical
  let Φ := E.childCoreHomeomorphOfIsEmptyChildCapBoundary c
  have hΦ : ∀ x : E.ChildCore c, Φ x = E.childCoreInclusion c x := fun _ => rfl
  let ρ : C(↥(univ : Set (E.ChildCarrier c)), E.ChildCore c) :=
    ⟨fun y => Φ.symm (y : E.ChildCarrier c), Φ.symm.continuous.comp continuous_subtype_val⟩
  have hρ : ∀ x : E.ChildCore c, ρ ⟨E.childCoreInclusion c x, mem_univ _⟩ = x := by
    intro x
    change Φ.symm (E.childCoreInclusion c x) = x
    rw [← hΦ x, Φ.symm_apply_apply]
  have hri : ρ.comp (E.childCoreInclusionRestrict c fun _ _ => mem_univ _) =
      ContinuousMap.id (E.ChildCore c) := by
    apply ContinuousMap.ext
    intro x
    exact hρ x
  have hir : (E.childCoreInclusionRestrict c fun _ _ => mem_univ _).comp ρ =
      ContinuousMap.id ↥(univ : Set (E.ChildCarrier c)) := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    change E.childCoreInclusion c (ρ y) = (y : E.ChildCarrier c)
    rw [← hΦ (ρ y)]
    change Φ (Φ.symm (y : E.ChildCarrier c)) = (y : E.ChildCarrier c)
    exact Φ.apply_symm_apply _
  exact ⟨{ U := univ
           V := fun b => (IsEmpty.false b).elim
           isOpen_U := isOpen_univ
           isOpen_V := fun b => (IsEmpty.false b).elim
           cover := by
             rw [Set.iUnion_eq_empty.mpr fun b => (IsEmpty.false b).elim, Set.union_empty]
           disjoint_V := fun b => (IsEmpty.false b).elim
           core_subset_U := fun _ _ => mem_univ _
           cap_subset_V := fun b => (IsEmpty.false b).elim
           retraction := ρ
           retraction_comp_inclusion := hri
           inclusion_comp_retraction_homotopic := hir ▸ ContinuousMap.Homotopic.refl _
           ball_homotopy_V := fun b => (IsEmpty.false b).elim
           sphere_homotopy_inter := fun b => (IsEmpty.false b).elim }⟩

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
