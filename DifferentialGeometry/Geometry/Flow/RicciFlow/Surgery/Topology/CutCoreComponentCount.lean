import DifferentialGeometry.Topology.Connected.CompactCoverCardinality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent

noncomputable section

open Set Function
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] [T2Space M]

private abbrev ClosedBand := Sphere 2 × Icc (-1 : ℝ) 1

omit [T2Space M] in
private def bandMap (T : TubeSystem M) (i : T.Index) : C(ClosedBand, M) where
  toFun z := T.tube i (z.1, ⟨z.2.1, by constructor <;> linarith [z.2.2.1, z.2.2.2]⟩)
  continuous_toFun := by
    apply (T.tube i).continuous.comp
    apply continuous_fst.prodMk
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _

omit [T2Space M] in
private theorem boundary_component_eq
    (T : TubeSystem M) [LocallyConnectedSpace T.core] (i : T.Index) (side : Bool) (p q : Sphere 2) :
    ConnectedComponents.mk (T.coreBoundarySphere (i, side) p) =
      ConnectedComponents.mk (T.coreBoundarySphere (i, side) q) := by
  have hconn : IsPreconnected (Set.univ : Set (Sphere 2)) := by
    have : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
        (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
    exact isPreconnected_univ
  exact hconn.constant
    (ConnectedComponents.continuous_coe.comp
      (T.coreBoundarySphere (i, side)).continuous).continuousOn
    (mem_univ p) (mem_univ q)

theorem card_connectedComponents_core_le
    (T : TubeSystem M) [CompactSpace T.core] [LocallyConnectedSpace T.core]
    [Finite (ConnectedComponents M)] :
    Nat.card (ConnectedComponents T.core) ≤
      Nat.card (ConnectedComponents M) + Nat.card T.Index := by
  classical
  let p : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let a : T.Index → ConnectedComponents T.core :=
    fun i => ConnectedComponents.mk (T.coreBoundarySphere (i, false) p)
  let b : T.Index → ConnectedComponents T.core :=
    fun i => ConnectedComponents.mk (T.coreBoundarySphere (i, true) p)
  have hcover : Surjective (Sum.elim (Subtype.val : T.core → M)
      (fun z : Σ i : T.Index, ClosedBand => bandMap T z.1 z.2)) := by
    intro x
    by_cases hx : x ∈ T.core
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · have hband : x ∈ ⋃ i, T.removedBand i := by
        simpa only [core, mem_compl_iff, not_not] using hx
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hband
      refine ⟨Sum.inr ⟨i, (z.1, ⟨z.2.1, hz.1.le, hz.2.le⟩)⟩, ?_⟩
      exact hzx
  have hdisj : Pairwise fun i j => Disjoint (range (bandMap T i)) (range (bandMap T j)) := by
    intro i j hij
    apply (T.disjoint hij).mono
    · rintro x ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · rintro x ⟨z, rfl⟩
      exact ⟨_, rfl⟩
  have hattach (i : T.Index) (x : T.core) (z : ClosedBand)
      (hx : x.1 = bandMap T i z) : ConnectedComponents.mk x = a i ∨
        ConnectedComponents.mk x = b i := by
    have hnot : ¬ ((-1 : ℝ) < z.2.1 ∧ z.2.1 < 1) := by
      intro hz
      apply x.2
      exact mem_iUnion.mpr ⟨i, (z.1, ⟨z.2.1, by
        constructor <;> linarith [z.2.2.1, z.2.2.2]⟩), hz, hx.symm⟩
    have hlevel : z.2.1 = -1 ∨ z.2.1 = 1 := by
      by_cases hleft : z.2.1 = -1
      · exact Or.inl hleft
      · have hzlo : (-1 : ℝ) < z.2.1 := lt_of_le_of_ne z.2.2.1 (Ne.symm hleft)
        exact Or.inr (le_antisymm z.2.2.2 (le_of_not_gt (fun hzhi => hnot ⟨hzlo, hzhi⟩)))
    rcases hlevel with hlevel | hlevel
    · left
      have heq : x = T.coreBoundarySphere (i, false) z.1 := by
        apply Subtype.ext
        rw [hx]
        change T.tube i _ = T.tube i _
        congr 1
        exact Prod.ext rfl (Subtype.ext (by simpa [boundaryLevel] using hlevel))
      rw [heq]
      exact boundary_component_eq T i false z.1 p
    · right
      have heq : x = T.coreBoundarySphere (i, true) z.1 := by
        apply Subtype.ext
        rw [hx]
        change T.tube i _ = T.tube i _
        congr 1
        exact Prod.ext rfl (Subtype.ext (by simpa [boundaryLevel] using hlevel))
      rw [heq]
      exact boundary_component_eq T i true z.1 p
  exact DifferentialGeometry.Topology.card_connectedComponents_le_of_compact_cover
    (K := T.core) (M := M) (I := T.Index)
    (B := fun _ : T.Index => ClosedBand)
    (Subtype.val : T.core → M) continuous_subtype_val Subtype.val_injective
    (fun i => (bandMap T i : ClosedBand → M)) (fun i => (bandMap T i).continuous)
    a b hcover hdisj hattach

end TubeSystem

namespace SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}}

theorem card_connectedComponents_core_le (X : SmoothCutCapTransition P Q D N) :
    Nat.card (ConnectedComponents X.trace.tubes.core) ≤
      Nat.card (ConnectedComponents P.Carrier) + Nat.card X.trace.tubes.Index := by
  let _ := X.core_compact
  let _ := X.core_locallyConnected
  let _ : LocallyConnectedSpace P.Carrier := ChartedSpace.locallyConnectedSpace ThreeSpace P.Carrier
  exact X.trace.tubes.card_connectedComponents_core_le

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
