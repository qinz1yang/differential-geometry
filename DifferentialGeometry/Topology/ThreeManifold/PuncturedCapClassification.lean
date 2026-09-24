import DifferentialGeometry.Topology.ThreeManifold.PuncturedCapCover
import DifferentialGeometry.Topology.ThreeManifold.SphericalBoundaryBallHoles
import DifferentialGeometry.Topology.ThreeManifold.CoreComponentGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapCoreCapping

noncomputable section

open Set Metric Manifold
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  {Ω : Set M.Carrier} (cap : CapCore Ω) (outer : T.Boundary)
  (hfront : frontier Ω = range (T.boundarySphere outer))
  (s : Finset T.Boundary)
  (B : T.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
  (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
  (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
  (hdis : (s : Set T.Boundary).Pairwise (fun b c =>
    Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
  (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
  (x : T.core)
  (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
    (Subtype.val : T.core → M.Carrier) '' connectedComponent x)

include hfront hinside hsphere in
private theorem outer_not_mem : outer ∉ s := by
  intro hout
  let q : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hq : T.boundarySphere outer q ∈ frontier Ω := hfront.symm ▸ mem_range_self q
  have hbq : T.boundarySphere outer q ∈ B outer '' sphere (0 : ThreeSpace) 1 :=
    (hsphere outer hout).symm ▸ mem_range_self q
  exact hq.2 (hinside outer hout (image_mono sphere_subset_closedBall hbq))

include cap hfront hB hinside hdis hsphere hcomponent

theorem frontier_coreComponent_union_caps_of_finite_ball_complement :
    frontier (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b)) =
      range (C.coreInclusion.comp (T.coreBoundarySphere outer)) := by
  obtain ⟨_,J,hJ,hJimage,hcoreEq,_,_⟩ :=
    C.nonempty_capCore_union_caps_of_finite_ball_complement cap s B hB hinside hdis hsphere x hcomponent
  have hinc := (T.toTopological.boundary_incidence_of_finite_ball_complement_component
    cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent).1
  rw [← hJimage, ← J.image_frontier_of_isCompact cap.isCompact_carrier hJ, hfront]
  ext y
  constructor
  · rintro ⟨_,⟨q,rfl⟩,rfl⟩
    exact ⟨q,(hcoreEq (T.coreBoundarySphere outer q) (hinc outer (Or.inl rfl) q)).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨T.boundarySphere outer q,mem_range_self q,
      hcoreEq (T.coreBoundarySphere outer q) (hinc outer (Or.inl rfl) q)⟩

theorem coreComponent_union_caps_inter_cap_of_finite_ball_complement :
    (C.coreInclusion '' connectedComponent x ∪ ⋃ b ∈ s, range (C.cap b)) ∩
        range (C.cap outer) = range (C.coreInclusion.comp (T.coreBoundarySphere outer)) := by
  have hnot : outer ∉ s := outer_not_mem outer hfront s B hinside hsphere
  have hinc := (T.toTopological.boundary_incidence_of_finite_ball_complement_component
    cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent).1
  apply Subset.antisymm
  · rintro y ⟨hy,hycap⟩
    rcases hy with hycore | hy
    · exact (C.core_cap_intersection outer).subset
        ⟨image_subset_range _ _ hycore,hycap⟩
    · obtain ⟨b,hb,hyb⟩ := mem_iUnion₂.mp hy
      exact False.elim (disjoint_left.mp (C.cap_disjoint (i := b) (j := outer) (fun he => hnot (he ▸ hb))) hyb hycap)
  · rintro y ⟨q,rfl⟩
    refine ⟨Or.inl ⟨T.coreBoundarySphere outer q,hinc outer (Or.inl rfl) q,rfl⟩,?_⟩
    refine ⟨sphereToClosedCell ((C.attaching outer).symm q),?_⟩
    exact (C.boundary_eq outer _).trans (congrArg C.coreInclusion
      (congrArg (T.coreBoundarySphere outer) ((C.attaching outer).apply_symm_apply q)))

theorem isPoincareStandard_component_of_finite_ball_complement :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  obtain ⟨hcap,_⟩ :=
    C.nonempty_capCore_union_caps_of_finite_ball_complement cap s B hB hinside hdis hsphere x hcomponent
  exact C.isPoincareStandard_component_of_capCore_union_cap hcap.some outer _
    (C.image_coreComponent_union_caps_eq_componentSet_of_finite_ball_complement
      cap.isCompact_carrier.isClosed outer hfront s B hB hinside hdis hsphere x hcomponent)

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_finite_ball_complement
    {Ω : Set M.Carrier} (cap : CapCore Ω) (outer : E.tubes.Boundary)
    (hfront : frontier Ω = range (E.tubes.boundarySphere outer))
    (s : Finset E.tubes.Boundary)
    (B : E.tubes.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hB : ∀ b ∈ s, closedBall (0 : ThreeSpace) 1 ⊆ (B b).source)
    (hinside : ∀ b ∈ s, B b '' closedBall (0 : ThreeSpace) 1 ⊆ interior Ω)
    (hdis : (s : Set E.tubes.Boundary).Pairwise (fun b c =>
      Disjoint (B b '' closedBall (0 : ThreeSpace) 1) (B c '' closedBall (0 : ThreeSpace) 1)))
    (hsphere : ∀ b ∈ s, B b '' sphere (0 : ThreeSpace) 1 = range (E.tubes.boundarySphere b))
    (x : E.tubes.core)
    (hcomponent : Ω \ ⋃ b ∈ s, B b '' ball (0 : ThreeSpace) 1 =
      (Subtype.val : E.tubes.core → M.Carrier) '' connectedComponent x)
    (d : E.discarded.Carrier) (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_finite_ball_complement
    cap outer hfront s B hB hinside hdis hsphere x hcomponent
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization x d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

end DifferentialGeometry.Topology.SphericalCutCapTransition

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_spherical_frontier
    (x : T.core) (A : PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (outer : T.Boundary) (houter : A '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere outer))
    (s : Finset T.Boundary)
    (hregular : closure (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)) =
      (Subtype.val : T.core → M.Carrier) '' connectedComponent x)
    (hconnected : IsPreconnected (interior ((Subtype.val : T.core → M.Carrier) '' connectedComponent x)))
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆
      A '' closedBall (0 : ThreeSpace) 1)
    (hinside : ∀ b ∈ s, range (T.boundarySphere b) ⊆ A '' ball (0 : ThreeSpace) 1)
    (hfront : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      range (T.boundarySphere outer) ∪ ⋃ b ∈ s, range (T.boundarySphere b)) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let I := {b : T.Boundary // b ∈ s}
  have hsmooth (b : I) : IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere b.val) :=
    T.toTopological.isSmoothEmbedding_boundarySphere b.val (T.smooth b.val.1)
  have hfr : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      A '' sphere (0 : ThreeSpace) 1 ∪ ⋃ b : I, range (T.boundarySphere b.val) := by
    rw [houter,iUnion_subtype]
    exact hfront
  have hpair : Pairwise (fun b c : I => Disjoint (range (T.boundarySphere b.val))
      (range (T.boundarySphere c.val))) := by
    intro b c hbc
    exact T.toTopological.pairwise_disjoint_range_boundarySphere (fun he => hbc (Subtype.ext he))
  obtain ⟨B,hB,hBs,hBA,hdis,hW⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_finite_disjoint_ball_holes_of_spherical_frontier
      A hA hregular hconnected hcontained (fun b : I => T.boundarySphere b.val)
      hsmooth (fun b => hinside b.val b.property) hfr hpair
  let B' : T.Boundary → PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞ :=
    fun b => if hb : b ∈ s then B ⟨b,hb⟩ else A
  have hB'eq (b : T.Boundary) (hb : b ∈ s) : B' b = B ⟨b,hb⟩ := dif_pos hb
  have hAint : interior (A '' closedBall (0 : ThreeSpace) 1) = A '' ball (0 : ThreeSpace) 1 := by
    have hh := A.toOpenPartialHomeomorph.image_interior_of_subset_source hA
    change A '' interior (closedBall (0 : ThreeSpace) 1) = interior (A '' closedBall 0 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hAf : frontier (A '' closedBall (0 : ThreeSpace) 1) = range (T.boundarySphere outer) := by
    rw [← A.image_frontier_of_isCompact (isCompact_closedBall _ _) hA,frontier_closedBall _ one_ne_zero,houter]
  have hholes : (⋃ b ∈ s, B' b '' ball (0 : ThreeSpace) 1) =
      ⋃ b : I, B b '' ball (0 : ThreeSpace) 1 := by
    ext y
    constructor
    · intro hy
      obtain ⟨b,hb,hy⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion.mpr ⟨⟨b,hb⟩,hB'eq b hb ▸ hy⟩
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      exact mem_iUnion₂.mpr ⟨b.val,b.property,(hB'eq b.val b.property).symm ▸ hb⟩
  apply C.isPoincareStandard_component_of_finite_ball_complement
    (CapCore.ball A hA rfl) outer hAf s B'
    (fun b hb => hB'eq b hb ▸ hB ⟨b,hb⟩)
  · intro b hb
    rw [hB'eq b hb,hAint]
    exact hBA ⟨b,hb⟩
  · intro b hb c hc hbc
    rw [hB'eq b hb,hB'eq c hc]
    exact hdis (fun he => hbc (congrArg Subtype.val he))
  · intro b hb
    rw [hB'eq b hb]
    exact hBs ⟨b,hb⟩
  · rw [hholes]
    exact hW.symm

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_containing_coreComponent
    (x : T.core) (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (outer : T.Boundary)
    (houter : A '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere outer))
    (houter_mem : ∃ q : Sphere 2, T.coreBoundarySphere outer q ∈ connectedComponent x)
    (hcontained : (Subtype.val : T.core → M.Carrier) '' connectedComponent x ⊆
      A '' closedBall (0 : ThreeSpace) 1) :
    isPoincareStandard (N.component (ConnectedComponents.mk (C.coreInclusion x))).Carrier := by
  classical
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hAint : interior (A '' closedBall (0 : ThreeSpace) 1) = A '' ball (0 : ThreeSpace) 1 := by
    have hh := A.toOpenPartialHomeomorph.image_interior_of_subset_source hA
    change A '' interior (closedBall (0 : ThreeSpace) 1) = interior (A '' closedBall 0 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hAfr : frontier (A '' closedBall (0 : ThreeSpace) 1) = range (T.boundarySphere outer) := by
    rw [← A.image_frontier_of_isCompact (isCompact_closedBall _ _) hA,
      frontier_closedBall _ one_ne_zero,houter]
  have hinside (b : T.Boundary) (hb : b ≠ outer)
      (hbmem : ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x) :
      range (T.boundarySphere b) ⊆ A '' ball (0 : ThreeSpace) 1 := by
    obtain ⟨q₀,hq₀⟩ := hbmem
    rintro y ⟨q,rfl⟩
    have hpre := isPreconnected_range (T.coreBoundarySphere b).continuous
    have hq : T.coreBoundarySphere b q ∈ connectedComponent x := by
      have hh := hpre.subset_connectedComponent (mem_range_self q₀) (mem_range_self q)
      rwa [← connectedComponent_eq hq₀] at hh
    have hclosed : T.boundarySphere b q ∈ A '' closedBall (0 : ThreeSpace) 1 :=
      hcontained (mem_image_of_mem Subtype.val hq)
    rw [← hAint]
    apply (mem_interior_iff_notMem_frontier hclosed).mpr
    intro hyfront
    obtain ⟨r,hr⟩ := hAfr ▸ hyfront
    exact hb ((T.toTopological.boundarySphere_eq_iff b outer q r).mp hr.symm).1
  let s : Finset T.Boundary := Finset.univ.filter (fun b => b ≠ outer ∧
    ∃ q : Sphere 2, T.coreBoundarySphere b q ∈ connectedComponent x)
  obtain ⟨_,_,hregular,hconnected,hfront⟩ := C.coreComponent_geometry x
  have hinside' : ∀ b ∈ s, range (T.boundarySphere b) ⊆ A '' ball (0 : ThreeSpace) 1 := by
    intro b hb
    obtain ⟨hne,hbcomp⟩ := (Finset.mem_filter.mp hb).2
    exact hinside b hne hbcomp
  have hfront' : frontier ((Subtype.val : T.core → M.Carrier) '' connectedComponent x) =
      range (T.boundarySphere outer) ∪ ⋃ b ∈ s, range (T.boundarySphere b) := by
    rw [hfront]
    ext y
    constructor
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      by_cases he : b.val = outer
      · exact Or.inl (he ▸ hb)
      · exact Or.inr (mem_iUnion₂.mpr ⟨b.val,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,he,b.property⟩,hb⟩)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨⟨outer,houter_mem⟩,hy⟩
      · obtain ⟨b,hb,hy⟩ := mem_iUnion₂.mp hy
        exact mem_iUnion.mpr ⟨⟨b,(Finset.mem_filter.mp hb).2.2⟩,hy⟩
  exact C.isPoincareStandard_component_of_ball_spherical_frontier x A hA outer houter s
    hregular hconnected hcontained hinside' hfront'

end DifferentialGeometry.Topology.SphericalCapping

end

section

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem isPoincareStandard_component_of_ball_cutting_side
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (b : T.Boundary) (hfront : A '' sphere (0 : ThreeSpace) 1 = range (T.boundarySphere b))
    (hdis : Disjoint (A '' closedBall (0 : ThreeSpace) 1) (T.removedBand b.1))
    (q : Sphere 2) :
    isPoincareStandard
      (N.component (ConnectedComponents.mk (C.coreInclusion (T.coreBoundarySphere b q)))).Carrier := by
  have hAf : frontier (A '' closedBall (0 : ThreeSpace) 1) = range (T.boundarySphere b) := by
    rw [← A.image_frontier_of_isCompact (isCompact_closedBall _ _) hA,
      frontier_closedBall _ one_ne_zero,hfront]
  have hq : T.boundarySphere b q ∈ A '' closedBall (0 : ThreeSpace) 1 :=
    image_mono sphere_subset_closedBall (hfront.symm ▸ mem_range_self q)
  apply C.isPoincareStandard_component_of_ball_containing_coreComponent
    (T.coreBoundarySphere b q) A hA b hfront ⟨q,mem_connectedComponent⟩
  rintro y ⟨z,hz,rfl⟩
  exact T.toTopological.connectedComponent_subset_preimage_of_capCore_of_boundarySphere
    (CapCore.ball A hA rfl) b hdis hAf (T.smooth b.1) (T.coreBoundarySphere b q) hq hz

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isPoincareStandard_discardedComponent_of_ball_cutting_side
    (A : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace M.Carrier ∞)
    (hA : closedBall (0 : ThreeSpace) 1 ⊆ A.source)
    (b : E.tubes.Boundary)
    (hfront : A '' sphere (0 : ThreeSpace) 1 = range (E.tubes.boundarySphere b))
    (hdis : Disjoint (A '' closedBall (0 : ThreeSpace) 1) (E.tubes.removedBand b.1))
    (q : Sphere 2) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion (E.tubes.coreBoundarySphere b q)) = Sum.inr d) :
    isPoincareStandard (E.discarded.component (ConnectedComponents.mk d)).Carrier := by
  have hstd := E.capping.isPoincareStandard_component_of_ball_cutting_side A hA b hfront hdis q
  obtain ⟨e⟩ := E.cappedDiscardedPresentationRealization (E.tubes.coreBoundarySphere b q) d hd
  exact isPoincareStandard_of_diffeomorph e.val.symm hstd

end DifferentialGeometry.Topology.SphericalCutCapTransition

end
