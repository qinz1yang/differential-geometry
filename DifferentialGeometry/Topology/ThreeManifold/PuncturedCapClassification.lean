import DifferentialGeometry.Topology.ThreeManifold.PuncturedCapCover
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
