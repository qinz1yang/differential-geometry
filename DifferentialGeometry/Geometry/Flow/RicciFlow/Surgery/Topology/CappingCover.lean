import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open Set Function
open scoped unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

instance instCompactSpaceThreeBall : CompactSpace ThreeBall :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ThreeSpace) 1)

instance instContractibleSpaceThreeBall : ContractibleSpace ThreeBall :=
  (convex_closedBall (0 : ThreeSpace) 1).contractibleSpace ⟨0, by simp⟩

instance instSimplyConnectedSpaceThreeBall : SimplyConnectedSpace ThreeBall :=
  SimplyConnectedSpace.ofContractible ThreeBall

noncomputable def sphereNorth : Sphere 2 :=
  ⟨EuclideanSpace.single 0 1, by simp [Sphere, PiLp.norm_single]⟩

noncomputable def threeBallNorth : ThreeBall := sphereToThreeBall sphereNorth

noncomputable def ballSegmentMap (y : ThreeBall) : C(I, ThreeBall) where
  toFun t :=
    ⟨(1 - (t : ℝ)) • y.1 + (t : ℝ) • threeBallNorth.1, by
      have h1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
      have h2 : 0 ≤ (t : ℝ) := t.2.1
      have h3 : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
      exact convex_closedBall (0 : ThreeSpace) 1 y.2 threeBallNorth.2 h1 h2 h3⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

noncomputable def segmentPath (y : ThreeBall) : Path y threeBallNorth :=
  Path.mk (ballSegmentMap y) (by apply Subtype.ext; simp [ballSegmentMap])
    (by apply Subtype.ext; simp [ballSegmentMap])

namespace Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {T : TubeSystem M}
    (K : Capping T N)

def capInterior (b : T.Boundary) : Set N := Set.range (K.cap b) \ Set.range K.coreInclusion

theorem mem_capInterior_iff {b : T.Boundary} {x : N} :
    x ∈ K.capInterior b ↔ x ∈ Set.range (K.cap b) ∧ x ∉ Set.range K.coreInclusion :=
  Iff.rfl

theorem capInterior_subset_range (b : T.Boundary) : K.capInterior b ⊆ Set.range (K.cap b) :=
  Set.sdiff_subset

theorem capInterior_disjoint_coreInclusion (b : T.Boundary) :
    Disjoint (K.capInterior b) (Set.range K.coreInclusion) := by
  rw [Set.disjoint_left]
  exact fun _ hx hxc => hx.2 hxc

theorem pairwise_disjoint_capInterior : Pairwise (Disjoint on K.capInterior) := by
  intro b b' hbb'
  rw [Function.onFun, Set.disjoint_left]
  exact fun _ hx hy => Set.disjoint_left.mp (K.cap_disjoint hbb') hx.1 hy.1

theorem iUnion_capInterior_disjoint_coreInclusion :
    Disjoint (⋃ b, K.capInterior b) (Set.range K.coreInclusion) := by
  rw [Set.disjoint_left]
  intro x hx hxc
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
  exact (Set.disjoint_left.mp (K.capInterior_disjoint_coreInclusion b)) hb hxc

theorem range_coreInclusion_union_iUnion_capInterior :
    Set.range K.coreInclusion ∪ (⋃ b, K.capInterior b) = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hx : x ∈ Set.range K.coreInclusion ∪ ⋃ b, Set.range (K.cap b) := by
    rw [K.exhaustive]
    exact Set.mem_univ x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    by_cases hcore : x ∈ Set.range K.coreInclusion
    · exact Or.inl hcore
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b, hb, hcore⟩)

theorem capInterior_subset_compl_coreInclusion (b : T.Boundary) :
    K.capInterior b ⊆ (Set.range K.coreInclusion)ᶜ :=
  fun _ hx hxc => hx.2 hxc

theorem exists_path_cap_to_coreInclusion (b : T.Boundary) (y : ThreeBall) :
    ∃ (p : N) (_ : p ∈ Set.range K.coreInclusion) (γ : Path (K.cap b y) p),
      ∀ t, (γ t : N) ∈ Set.range (K.cap b) := by
  refine ⟨K.coreInclusion (T.coreBoundarySphere b (K.attaching b sphereNorth)),
    ⟨_, rfl⟩, ?_, ?_⟩
  · exact ((segmentPath y).map (K.cap b).continuous).cast rfl
      (K.boundary_eq b sphereNorth).symm
  · intro t
    exact ⟨segmentPath y t, rfl⟩

theorem isSimplyConnected_range_cap (b : T.Boundary) :
    IsSimplyConnected (Set.range (K.cap b)) :=
  ((K.capEmbedding b).toHomeomorph.toHomotopyEquiv).symm.simplyConnectedSpace

theorem isSimplyConnected_image_componentCarrier (D : ConnectedComponents T.core)
    (hD : SimplyConnectedSpace (ComponentCarrier D)) :
    IsSimplyConnected (K.coreInclusion '' {x : T.core | ConnectedComponents.mk x = D}) :=
  (K.coreEmbedding.isSimplyConnected_image).mpr hD

end Capping

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
