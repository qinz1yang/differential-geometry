import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCapping
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOwnership
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
Actual sphere capping preserves the finite connected component cover. Each ball is assigned by its
actual attaching sphere, and the resulting clopen pieces have connected intrinsic interiors.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C) (D : C.Components)

def sphereCapComponentOwner (i : Fin B.sphereCount) : Fin D.count :=
  (D.exists_owner (B.sphereMap i) (B.sphereMap i).continuous).choose

theorem sphereCapComponentOwner_mem (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.sphereMap i z ∈ D.piece (B.sphereCapComponentOwner D i) :=
  (D.exists_owner (B.sphereMap i) (B.sphereMap i).continuous).choose_spec ⟨z, rfl⟩

def sphereCapComponentSet (j : Fin D.count) : Set B.sphereCapCarrier.Carrier :=
  B.sphereCapCore '' (D.piece j : Set C.Carrier) ∪
    ⋃ i, {x | B.sphereCapComponentOwner D i = j ∧ x ∈ range (B.sphereCapBall i)}

private theorem sphereCapCore_ball_owner {j : Fin D.count} {i : Fin B.sphereCount}
    {x : C.Carrier} {y : ClosedCell 3} (hx : x ∈ D.piece j)
    (hxy : B.sphereCapCore x = B.sphereCapBall i y) :
    B.sphereCapComponentOwner D i = j := by
  have hmem : B.sphereCapCore x ∈ range B.sphereCapCore ∩ range (B.sphereCapBall i) :=
    ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
  rw [B.sphereCapCore_ball_intersection] at hmem
  obtain ⟨z, hz⟩ := hmem
  have he : B.sphereMap i z = x := B.sphereCapCore_injective hz
  have ho := B.sphereCapComponentOwner_mem D i z
  rw [he] at ho
  by_contra hne
  exact disjoint_left.mp (D.disjoint hne) ho hx

theorem sphereCapComponentSet_core_mem (j : Fin D.count) (x : C.Carrier) :
    B.sphereCapCore x ∈ B.sphereCapComponentSet D j ↔ x ∈ D.piece j := by
  constructor
  · rintro (⟨y, hy, he⟩ | hb)
    · exact B.sphereCapCore_injective he ▸ hy
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      obtain ⟨ho, y, hy⟩ := hi
      have hmem : B.sphereCapCore x ∈ range B.sphereCapCore ∩ range (B.sphereCapBall i) :=
        ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
      rw [B.sphereCapCore_ball_intersection] at hmem
      obtain ⟨z, hz⟩ := hmem
      have he := B.sphereCapCore_injective hz
      rw [← he, ← ho]
      exact B.sphereCapComponentOwner_mem D i z
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

theorem sphereCapComponentSet_ball_mem (j : Fin D.count) (i : Fin B.sphereCount)
    (x : ClosedCell 3) :
    B.sphereCapBall i x ∈ B.sphereCapComponentSet D j ↔
      B.sphereCapComponentOwner D i = j := by
  constructor
  · rintro (⟨y, hy, he⟩ | hb)
    · exact B.sphereCapCore_ball_owner D hy he
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
      obtain ⟨ho, y, hy⟩ := hk
      have hik : i = k := by
        by_contra hne
        exact disjoint_left.mp (B.sphereCapBall_disjoint hne)
          (mem_range_self x) ⟨y, hy⟩
      exact hik.symm ▸ ho
  · intro hi
    exact Or.inr (mem_iUnion.mpr ⟨i, hi, mem_range_self x⟩)

set_option backward.isDefEq.respectTransparency false in
theorem sphereCapComponentSet_closed (j : Fin D.count) :
    IsClosed (B.sphereCapComponentSet D j) := by
  change IsClosed (B.sphereCapCore '' (D.piece j : Set C.Carrier) ∪
    ⋃ i, {x : B.SphereCapQuotient | B.sphereCapComponentOwner D i = j ∧
      x ∈ range (B.sphereCapBall i)})
  exact ((D.piece_compact j).image B.sphereCapCore.continuous).isClosed.union
    (isClosed_iUnion_of_finite fun i => by
      by_cases hi : B.sphereCapComponentOwner D i = j
      · have he : {x | B.sphereCapComponentOwner D i = j ∧
            x ∈ range (B.sphereCapBall i)} = range (B.sphereCapBall i) := by
          ext x
          simp only [mem_ofPred_eq, hi, true_and]
        rw [he]
        exact (isCompact_range (B.sphereCapBall i).continuous).isClosed
      · simp only [hi, false_and, ofPred_false]
        exact isClosed_empty)

theorem sphereCapComponentSet_disjoint :
    Pairwise fun i j => Disjoint (B.sphereCapComponentSet D i) (B.sphereCapComponentSet D j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  have hcover : x ∈ range B.sphereCapCore ∪ ⋃ k, range (B.sphereCapBall k) := by
    rw [B.sphereCap_covers]
    exact mem_univ x
  rcases hcover with ⟨y, rfl⟩ | hb
  · exact disjoint_left.mp (D.disjoint hij)
      ((B.sphereCapComponentSet_core_mem D i y).mp hi)
      ((B.sphereCapComponentSet_core_mem D j y).mp hj)
  · obtain ⟨k, y, rfl⟩ := mem_iUnion.mp hb
    exact hij (((B.sphereCapComponentSet_ball_mem D i k y).mp hi).symm.trans
      ((B.sphereCapComponentSet_ball_mem D j k y).mp hj))

theorem sphereCapComponentSet_covers : ⋃ j, B.sphereCapComponentSet D j = univ := by
  apply eq_univ_of_forall
  intro x
  have hcover : x ∈ range B.sphereCapCore ∪ ⋃ k, range (B.sphereCapBall k) := by
    rw [B.sphereCap_covers]
    exact mem_univ x
  rcases hcover with ⟨y, rfl⟩ | hb
  · have hy : y ∈ ⋃ j, (D.piece j : Set C.Carrier) := D.covers.symm ▸ mem_univ y
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨j, (B.sphereCapComponentSet_core_mem D j y).mpr hj⟩
  · obtain ⟨k, y, rfl⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨B.sphereCapComponentOwner D k,
      (B.sphereCapComponentSet_ball_mem D _ k y).mpr rfl⟩

theorem sphereCapComponentSet_open (j : Fin D.count) :
    IsOpen (B.sphereCapComponentSet D j) := by
  have he : (B.sphereCapComponentSet D j)ᶜ =
      ⋃ k, ⋃ h : k ≠ j, B.sphereCapComponentSet D k := by
    ext x
    constructor
    · intro hx
      have hcov : x ∈ ⋃ k, B.sphereCapComponentSet D k :=
        (B.sphereCapComponentSet_covers D).symm ▸ mem_univ x
      obtain ⟨k, hk⟩ := mem_iUnion.mp hcov
      have hkj : k ≠ j := fun heq => hx (heq ▸ hk)
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkj, hk⟩⟩
    · intro hx hj
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      obtain ⟨hkj, hmem⟩ := mem_iUnion.mp hk
      exact disjoint_left.mp (B.sphereCapComponentSet_disjoint D hkj) hmem hj
  have hclosed : IsClosed (B.sphereCapComponentSet D j)ᶜ := by
    rw [he]
    exact isClosed_iUnion_of_finite fun k =>
      isClosed_iUnion_of_finite fun h => by
        have hclosed := B.sphereCapComponentSet_closed D k
        exact hclosed
  simpa only [compl_compl] using hclosed.isOpen_compl

private theorem sphereCapBall_preconnected (i : Fin B.sphereCount) :
    IsPreconnected (range (B.sphereCapBall i)) := by
  let : PreconnectedSpace (ClosedCell 3) := by
    apply Subtype.preconnectedSpace
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)
    exact hconv.isPreconnected
  exact isPreconnected_range (B.sphereCapBall i).continuous

theorem sphereCapComponentSet_connected (j : Fin D.count) :
    IsConnected (B.sphereCapComponentSet D j) := by
  let := D.connected j
  have hcore : IsConnected (B.sphereCapCore '' (D.piece j : Set C.Carrier)) :=
    (isConnected_iff_connectedSpace.mpr inferInstance).image B.sphereCapCore
      B.sphereCapCore.continuous.continuousOn
  obtain ⟨a, ha⟩ := hcore.nonempty
  let I := {i : Fin B.sphereCount // B.sphereCapComponentOwner D i = j}
  let A : Option I → Set B.sphereCapCarrier.Carrier := fun i =>
    match i with
    | none => B.sphereCapCore '' (D.piece j : Set C.Carrier)
    | some k => B.sphereCapCore '' (D.piece j : Set C.Carrier) ∪ range (B.sphereCapBall k.val)
  have hA : ∀ i, IsPreconnected (A i) := by
    intro i
    cases i with
    | none => exact hcore.isPreconnected
    | some k =>
      apply hcore.isPreconnected.union' ?_ (B.sphereCapBall_preconnected k.val)
      let z : ClosureSphere.{u} := Classical.choice inferInstance
      have ho : B.sphereMap k.val z ∈ D.piece j :=
        by
          have hm := B.sphereCapComponentOwner_mem D k.val z
          rwa [k.property] at hm
      exact ⟨B.sphereCapCore (B.sphereMap k.val z), ⟨B.sphereMap k.val z, ho, rfl⟩,
        ⟨closureSphereToBall z, (B.sphereCap_attachment k.val z).symm⟩⟩
  have hcommon : (⋂ i, A i).Nonempty := by
    refine ⟨a, mem_iInter.mpr ?_⟩
    intro i
    cases i with
    | none => exact ha
    | some k => exact Or.inl ha
  have he : (⋃ i, A i) = B.sphereCapComponentSet D j := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact Or.inl hi
      | some k =>
        rcases hi with hc | hb
        · exact Or.inl hc
        · exact Or.inr (mem_iUnion.mpr ⟨k.val, k.property, hb⟩)
    · rintro (hc | hb)
      · exact mem_iUnion.mpr ⟨none, hc⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
        obtain ⟨ho, hm⟩ := hi
        exact mem_iUnion.mpr ⟨some (⟨i, ho⟩ : I), Or.inr hm⟩
  refine ⟨⟨a, Or.inl ha⟩, ?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hA

def sphereCapComponentOpen (j : Fin D.count) : Opens B.sphereCapCarrier.Carrier :=
  ⟨B.sphereCapComponentSet D j, B.sphereCapComponentSet_open D j⟩

private theorem sphereCapComponentInterior_connected (j : Fin D.count) :
    ConnectedSpace (B.sphereCapCarrier.pieceInterior (B.sphereCapComponentOpen D j)) := by
  let K := B.sphereCapCarrier
  let U := B.sphereCapComponentOpen D j
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp
    (B.sphereCapComponentSet_connected D j)
  have he : (K.pieceInterior U : Set K.Carrier) = K.model.interior K.Carrier ∩ U := by
    ext x
    exact and_comm
  apply isConnected_iff_connectedSpace.mp
  rw [he]
  have hp : IsPreconnected (U : Set K.Carrier) :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hd := DifferentialGeometry.Topology.Manifold.dense_manifold_interior
    (I := K.model) (M := U)
  obtain ⟨x, hx⟩ := hd.nonempty
  refine ⟨⟨x.val, ?_, x.property⟩,
    DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior_inter_open U hp⟩
  exact K.model.isInteriorPoint_iff_isInteriorPoint_val.mp hx

def sphereCapComponents : B.sphereCapCarrier.Components where
  count := D.count
  count_pos := D.count_pos
  piece := B.sphereCapComponentOpen D
  closed := B.sphereCapComponentSet_closed D
  connected j := isConnected_iff_connectedSpace.mp (B.sphereCapComponentSet_connected D j)
  disjoint := B.sphereCapComponentSet_disjoint D
  covers := B.sphereCapComponentSet_covers D
  interior_connected := B.sphereCapComponentInterior_connected D

theorem sphereCapComponents_count : (B.sphereCapComponents D).count = D.count := rfl

theorem sphereCapComponents_piece (j : Fin D.count) :
    ((B.sphereCapComponents D).piece j : Set B.sphereCapCarrier.Carrier) =
      B.sphereCapCore '' (D.piece j : Set C.Carrier) ∪
        ⋃ i, {x | B.sphereCapComponentOwner D i = j ∧ x ∈ range (B.sphereCapBall i)} := rfl

theorem sphereCapComponents_core_mem (j : Fin D.count) (x : C.Carrier) :
    B.sphereCapCore x ∈ (B.sphereCapComponents D).piece j ↔ x ∈ D.piece j :=
  B.sphereCapComponentSet_core_mem D j x

theorem sphereCapComponents_cap_mem (i : Fin B.sphereCount) (x : ClosedCell 3) :
    B.sphereCapReparameterizedCap i x ∈
      (B.sphereCapComponents D).piece (B.sphereCapComponentOwner D i) :=
  (B.sphereCapComponentSet_ball_mem D _ i
    (B.sphereCapOrientationData.reparameterization i x)).mpr rfl

theorem exists_sphereCapComponents :
    ∃ E : B.sphereCapCarrier.Components, ∃ hc : E.count = D.count,
      (∀ j : Fin D.count, ∀ x : C.Carrier,
        B.sphereCapCore x ∈ E.piece (Fin.cast hc.symm j) ↔ x ∈ D.piece j) ∧
      (∀ i : Fin B.sphereCount, ∀ x : ClosedCell 3,
        B.sphereCapReparameterizedCap i x ∈
          E.piece (Fin.cast hc.symm (B.sphereCapComponentOwner D i))) :=
  ⟨B.sphereCapComponents D, rfl, B.sphereCapComponents_core_mem D,
    B.sphereCapComponents_cap_mem D⟩

end GC.GraphManifold.MixedBoundaryCertificate
