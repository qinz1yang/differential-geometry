import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerKept

/-!
# Actual protected seams and frozen components after contraction

Protected seams retain the native unpaired-seam numbering. Frozen components retain the
native kept-component numbering. These bijections give exact finite ledger cardinalities.
-/

set_option autoImplicit false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

def contractAlongProtected (K P : Finset (Fin T.pairing.count)) :
    Finset (Fin (Fintype.card (T.AlongUnpairedSeam K))) := by
  classical
  exact Finset.univ.filter fun c =>
    ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val ∈ P

theorem mem_contractAlongProtected (K P : Finset (Fin T.pairing.count))
    (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) :
    c ∈ T.contractAlongProtected K P ↔
      ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val ∈ P := by
  classical
  simp [contractAlongProtected]

def contractAlongProtectedEquiv (K P : Finset (Fin T.pairing.count))
    (hPK : Disjoint P K) :
    {k : Fin T.pairing.count // k ∈ P} ≃
      {c : Fin (Fintype.card (T.AlongUnpairedSeam K)) //
        c ∈ T.contractAlongProtected K P} where
  toFun k := ⟨Fintype.equivFin (T.AlongUnpairedSeam K)
    ⟨k.val, fun hk => Finset.disjoint_left.mp hPK k.property hk⟩,
      (T.mem_contractAlongProtected K P _).mpr (by simp)⟩
  invFun c := ⟨((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c.val).val,
    (T.mem_contractAlongProtected K P c.val).mp c.property⟩
  left_inv k := by simp
  right_inv c := by simp

theorem contractAlongProtectedEquiv_original (K P : Finset (Fin T.pairing.count))
    (hPK : Disjoint P K) (k : {k : Fin T.pairing.count // k ∈ P}) :
    ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
      (T.contractAlongProtectedEquiv K P hPK k).val).val = k.val := by
  simp [contractAlongProtectedEquiv]

theorem card_contractAlongProtected (K P : Finset (Fin T.pairing.count))
    (hPK : Disjoint P K) : (T.contractAlongProtected K P).card = P.card := by
  have hc := Fintype.card_congr (T.contractAlongProtectedEquiv K P hPK)
  simpa using hc.symm

theorem contractAlong_innerCount_singleton (P : Finset (Fin T.pairing.count))
    (j : Fin T.pairing.count) (hj : j ∉ P) :
    (T.contractAlongProtected {j} P)ᶜ.card + 1 = Pᶜ.card := by
  classical
  have hPK : Disjoint P {j} := Finset.disjoint_singleton_right.mpr hj
  have hc := T.card_contractAlongProtected {j} P hPK
  have hn := T.alongUnpairedSeam_card {j}
  have hP : P.card < T.pairing.count := by
    have hproper := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ P, fun he => hj (he.symm ▸ Finset.mem_univ j)⟩)
    simpa using hproper
  rw [Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin, hc, hn]
  simp only [Finset.card_singleton] at *
  omega

variable (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

theorem contractAlongProtected_seam (P : Finset (Fin T.pairing.count))
    (hPK : Disjoint P K) (k : {k : Fin T.pairing.count // k ∈ P}) :
    (T.contractAlong S K hK hext hk hconn).seam
      (T.contractAlongProtectedEquiv K P hPK k).val = T.seam k.val := by
  change T.seam ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
    (T.contractAlongProtectedEquiv K P hPK k).val).val = _
  rw [T.contractAlongProtectedEquiv_original K P hPK k]

theorem contractAlongFrozen_not_mem (F : Finset (Fin T.components.count)) (hFS : Disjoint F S)
    (i : {i : Fin T.components.count // i ∈ F}) : i.val ∉ S :=
  fun hi => Finset.disjoint_left.mp hFS i.property hi

def contractAlongFrozen (F : Finset (Fin T.components.count)) (hFS : Disjoint F S) :
    Finset (Fin (T.contractAlong S K hK hext hk hconn).components.count) := by
  classical
  exact Finset.univ.image fun i : {i : Fin T.components.count // i ∈ F} =>
    T.contractAlongKeptIndex S K hK hext hk hconn (T.contractAlongFrozen_not_mem S F hFS i)

private theorem frozenIndex_injective (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) :
    Injective (fun i : {i : Fin T.components.count // i ∈ F} =>
      T.contractAlongKeptIndex S K hK hext hk hconn (T.contractAlongFrozen_not_mem S F hFS i)) := by
  intro i j hij
  apply Subtype.ext
  change (T.subIndexOf Sᶜ _).castSucc = (T.subIndexOf Sᶜ _).castSucc at hij
  have hs := congrArg (T.subIndex Sᶜ) (Fin.castSucc_inj.mp hij)
  simpa using hs

def contractAlongFrozenEquiv (F : Finset (Fin T.components.count)) (hFS : Disjoint F S) :
    {i : Fin T.components.count // i ∈ F} ≃
      {i : Fin (T.contractAlong S K hK hext hk hconn).components.count //
        i ∈ T.contractAlongFrozen S K hK hext hk hconn F hFS} := by
  classical
  let f := fun i : {i : Fin T.components.count // i ∈ F} =>
    T.contractAlongKeptIndex S K hK hext hk hconn (T.contractAlongFrozen_not_mem S F hFS i)
  refine Equiv.ofBijective (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨?_, ?_⟩
  · intro i j hij
    exact T.frozenIndex_injective S K hK hext hk hconn F hFS (congrArg Subtype.val hij)
  · intro i
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp i.property
    exact ⟨j, Subtype.ext he⟩

theorem contractAlongFrozenEquiv_apply (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) (i : {i : Fin T.components.count // i ∈ F}) :
    (T.contractAlongFrozenEquiv S K hK hext hk hconn F hFS i).val =
      T.contractAlongKeptIndex S K hK hext hk hconn (T.contractAlongFrozen_not_mem S F hFS i) := rfl

theorem card_contractAlongFrozen (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) : (T.contractAlongFrozen S K hK hext hk hconn F hFS).card =
      F.card := by
  have hc := Fintype.card_congr (T.contractAlongFrozenEquiv S K hK hext hk hconn F hFS)
  simpa using hc.symm

theorem contractAlongFrozenEquiv_native (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) (i : {i : Fin T.components.count // i ∈ F}) :
    (T.contractAlongFrozenEquiv S K hK hext hk hconn F hFS i).val =
      (T.subIndexOf Sᶜ (Finset.mem_compl.mpr
        (T.contractAlongFrozen_not_mem S F hFS i))).castSucc := rfl

private theorem geometryFiniteSide_owner (a : T.AlongLedgerRetainedSide K) :
    (T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn) a).1 =
      T.alongLedgerOwner S K a := by
  change T.alongGeometryIndexEquiv S (T.alongGeometryOwner S K a) = _
  exact (T.alongGeometryIndexEquiv S).apply_symm_apply _

theorem contractAlong_leftPiece (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) :
    (T.contractAlong S K hK hext hk hconn).leftPiece c =
      T.alongPieceIndex S (T.leftPiece
        ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val) := by
  change (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    (T.alongLedgerSideSum K
      (.inl ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c, true)))).1 = _
  rw [T.geometryFiniteSide_owner S K hK hext hk hconn]
  rfl

theorem contractAlong_rightPiece (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) :
    (T.contractAlong S K hK hext hk hconn).rightPiece c =
      T.alongPieceIndex S (T.rightPiece
        ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val) := by
  change (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    (T.alongLedgerSideSum K
      (.inl ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c, false)))).1 = _
  rw [T.geometryFiniteSide_owner S K hK hext hk hconn]
  rfl

theorem alongPieceIndex_mem_contractAlongFrozen_iff
    (F : Finset (Fin T.components.count)) (hFS : Disjoint F S)
    (i : Fin T.components.count) :
    T.alongPieceIndex S i ∈ T.contractAlongFrozen S K hK hext hk hconn F hFS ↔ i ∈ F := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hi
    have he' : T.alongPieceIndex S i =
        (T.subIndexOf Sᶜ (Finset.mem_compl.mpr
          (T.contractAlongFrozen_not_mem S F hFS a))).castSucc := he.symm
    have hi' := (T.alongLedgerPieceIndex_castSucc_iff S i _).mp he'
    rw [T.subIndex_subIndexOf] at hi'
    exact hi' ▸ a.property
  · intro hi
    have hn := T.contractAlongFrozen_not_mem S F hFS ⟨i, hi⟩
    refine Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    change (T.subIndexOf Sᶜ _).castSucc = T.alongPieceIndex S i
    simp [alongPieceIndex, hn]

theorem contractAlong_leftPiece_mem_frozen_iff (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) :
    (T.contractAlong S K hK hext hk hconn).leftPiece c ∈
      T.contractAlongFrozen S K hK hext hk hconn F hFS ↔
      T.leftPiece ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val ∈ F := by
  rw [T.contractAlong_leftPiece S K hK hext hk hconn]
  exact T.alongPieceIndex_mem_contractAlongFrozen_iff S K hK hext hk hconn F hFS _

theorem contractAlong_rightPiece_mem_frozen_iff (F : Finset (Fin T.components.count))
    (hFS : Disjoint F S) (c : Fin (Fintype.card (T.AlongUnpairedSeam K))) :
    (T.contractAlong S K hK hext hk hconn).rightPiece c ∈
      T.contractAlongFrozen S K hK hext hk hconn F hFS ↔
      T.rightPiece ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm c).val ∈ F := by
  rw [T.contractAlong_rightPiece S K hK hext hk hconn]
  exact T.alongPieceIndex_mem_contractAlongFrozen_iff S K hK hext hk hconn F hFS _

end GC.Seifert.TorusPresentation
