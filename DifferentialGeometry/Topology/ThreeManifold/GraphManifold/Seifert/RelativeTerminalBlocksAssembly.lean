import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksAssets
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksGroup
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFrozen

/-!
# Finite actual grouping with protected seams and frozen compact pieces

A grouping stores actual disjoint selected stars and compact transports of the frozen
pieces. Each contraction absorbs exactly one arm family, preserves every protected signed
seam, and composes the full compact transports of the frozen pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

structure RelativeGrouping {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
    (T : TorusPresentation (NoCuts.carrier Q)) (n : ℕ) where
  data : Fin n → SeifertData
  group : ∀ a, SelectedStarGroup T (data a)
  arm_pos : ∀ a, 0 < (data a).fillingCount
  good : ∀ a, GoodData.{u} (data a)
  disjoint : ∀ a b, a ≠ b → Disjoint (group a).set (group b).set
  protectedIndex : σ.ProtSeam ↪ Fin T.pairing.count
  protected_seam : ∀ j, T.seam (protectedIndex j) = σ.toTorus.seam j.val
  protected_matching : ∀ j, T.pairing.matching (protectedIndex j) =
    σ.toTorus.pairing.matching j.val
  protected_outside : ∀ j a, protectedIndex j ∉ (group a).selected
  frozen : σ.Frozen ↪ Fin T.components.count
  transfer : ∀ f, PieceTransfer σ.toTorus f.val T (frozen f)
  oriented : ∀ f, (transfer f).map.preservesOrientation
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components f.val).orientation
    (componentCarrier T.cutCarrier T.components (frozen f)).orientation
  cutMap : ∀ f x, T.cutMap ((transfer f).map x).val = σ.toTorus.cutMap x.val
  frozen_outside : ∀ f a, frozen f ∉ (group a).set
  rest : ∀ i, (∀ a, i ∉ (group a).set) → (∀ f, frozen f ≠ i) →
    {B : PieceBlock T i // GoodData.{u} B.data}

structure RelativeGroupedPresentation {Q : ConnectedClosedOrientedManifold.{u} 3}
    (σ : MixedStage Q) where
  base : TorusPresentation (NoCuts.carrier Q)
  protectedIndex : σ.ProtSeam ↪ Fin base.pairing.count
  protected_seam : ∀ j, base.seam (protectedIndex j) = σ.toTorus.seam j.val
  protected_matching : ∀ j, base.pairing.matching (protectedIndex j) =
    σ.toTorus.pairing.matching j.val
  frozen : σ.Frozen ↪ Fin base.components.count
  transfer : ∀ f, PieceTransfer σ.toTorus f.val base (frozen f)
  oriented : ∀ f, (transfer f).map.preservesOrientation
    (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components f.val).orientation
    (componentCarrier base.cutCarrier base.components (frozen f)).orientation
  cutMap : ∀ f x, base.cutMap ((transfer f).map x).val = σ.toTorus.cutMap x.val
  block : ∀ i, (∀ f, frozen f ≠ i) → {B : PieceBlock base i // GoodData.{u} B.data}

namespace RelativeGrouping

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {T : TorusPresentation (NoCuts.carrier Q)} {n : ℕ}

def finish (Γ : RelativeGrouping σ T 0) : RelativeGroupedPresentation σ where
  base := T
  protectedIndex := Γ.protectedIndex
  protected_seam := Γ.protected_seam
  protected_matching := Γ.protected_matching
  frozen := Γ.frozen
  transfer := Γ.transfer
  oriented := Γ.oriented
  cutMap := Γ.cutMap
  block i hi := Γ.rest i (fun a => a.elim0) hi

variable (Γ : RelativeGrouping σ T (n + 1))

def firstSet : Finset (Fin T.components.count) := (Γ.group 0).set

def firstSelected : Finset (Fin T.pairing.count) := (Γ.group 0).selected

theorem firstExternal : ∀ i, T.externalPiece i ∉ Γ.firstSet :=
  T.externalPiece_not_mem_of_closed Γ.firstSet

include Γ in
theorem firstKind : T.cutCarrier.kind = .withBoundary :=
  T.cutCarrier_kind_of_pos (Fin.pos ((Γ.group 0).arm ⟨0, Γ.arm_pos 0⟩))

def next : TorusPresentation (NoCuts.carrier Q) :=
  (Γ.group 0).relativeSelectedContraction Γ.firstExternal Γ.firstKind

theorem firstDisjoint (a : Fin n) : Disjoint (Γ.group a.succ).set Γ.firstSet :=
  Γ.disjoint _ _ (Fin.succ_ne_zero a)

def nextGroup (a : Fin n) : SelectedStarGroup Γ.next (Γ.data a.succ) :=
  (Γ.group a.succ).relativeSelectedTransfer Γ.firstSet Γ.firstSelected
    (Γ.group 0).selected_internal Γ.firstExternal Γ.firstKind
    ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) (Γ.firstDisjoint a)

def keptIndex {i : Fin T.components.count} (hi : i ∉ Γ.firstSet) :
    Fin Γ.next.components.count :=
  T.contractAlongKeptIndex Γ.firstSet Γ.firstSelected (Γ.group 0).selected_internal
    Γ.firstExternal Γ.firstKind ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) hi

def keptTransfer {i : Fin T.components.count} (hi : i ∉ Γ.firstSet) :
    PieceTransfer T i Γ.next (Γ.keptIndex hi) :=
  T.contractAlongKeptTransfer Γ.firstSet Γ.firstSelected (Γ.group 0).selected_internal
    Γ.firstExternal Γ.firstKind ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) hi

theorem keptOriented {i : Fin T.components.count} (hi : i ∉ Γ.firstSet) :
    (Γ.keptTransfer hi).map.preservesOrientation
      (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier Γ.next.cutCarrier Γ.next.components (Γ.keptIndex hi)).orientation :=
  T.contractAlongKeptTransfer_oriented Γ.firstSet Γ.firstSelected (Γ.group 0).selected_internal
    Γ.firstExternal Γ.firstKind ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) hi

theorem keptCutMap {i : Fin T.components.count} (hi : i ∉ Γ.firstSet)
    (x : T.components.piece i) : Γ.next.cutMap ((Γ.keptTransfer hi).map x).val = T.cutMap x.val :=
  T.contractAlongKeptTransfer_cutMap Γ.firstSet Γ.firstSelected (Γ.group 0).selected_internal
    Γ.firstExternal Γ.firstKind ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal)
    hi x

theorem keptInjective {i k : Fin T.components.count} (hi : i ∉ Γ.firstSet)
    (hk : k ∉ Γ.firstSet) (he : Γ.keptIndex hi = Γ.keptIndex hk) : i = k :=
  T.relativeKeptIndex_injective Γ.firstSet Γ.firstSelected (Γ.group 0).selected_internal
    Γ.firstExternal Γ.firstKind ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal)
    hi hk he

theorem nextGroup_mem {j : Fin Γ.next.components.count} (a : Fin n)
    (hj : j ∈ (Γ.nextGroup a).set) :
    ∃ i, ∃ hi : i ∉ Γ.firstSet, i ∈ (Γ.group a.succ).set ∧ j = Γ.keptIndex hi :=
  (Γ.group a.succ).relativeSelectedTransfer_mem_set Γ.firstSet Γ.firstSelected
    (Γ.group 0).selected_internal Γ.firstExternal Γ.firstKind
    ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) (Γ.firstDisjoint a) hj

theorem nextGroup_index_mem {i : Fin T.components.count} (hi : i ∉ Γ.firstSet) (a : Fin n)
    (h : i ∈ (Γ.group a.succ).set) : Γ.keptIndex hi ∈ (Γ.nextGroup a).set :=
  (Γ.group a.succ).relativeSelectedTransfer_index_mem_set Γ.firstSet Γ.firstSelected
    (Γ.group 0).selected_internal Γ.firstExternal Γ.firstKind
    ((Γ.group 0).relativeSelected_interior_connected Γ.firstExternal) (Γ.firstDisjoint a) hi h

theorem nextDisjoint (a b : Fin n) (hab : a ≠ b) :
    Disjoint (Γ.nextGroup a).set (Γ.nextGroup b).set := by
  refine Finset.disjoint_left.mpr fun j ha hb => ?_
  obtain ⟨i, hi, hia, rfl⟩ := Γ.nextGroup_mem a ha
  obtain ⟨k, hk, hkb, he⟩ := Γ.nextGroup_mem b hb
  obtain rfl := Γ.keptInjective hi hk he
  exact Finset.disjoint_left.mp
    (Γ.disjoint _ _ (fun e => hab (Fin.succ_injective _ e))) hia hkb

def nextProtected : σ.ProtSeam ↪ Fin Γ.next.pairing.count where
  toFun j := (Γ.group 0).relativeSelectedSeamEquiv Γ.firstExternal Γ.firstKind
    ⟨Γ.protectedIndex j, Γ.protected_outside j 0⟩
  inj' j k he := by
    have hv : Γ.protectedIndex j = Γ.protectedIndex k := congrArg Subtype.val
      (((Γ.group 0).relativeSelectedSeamEquiv Γ.firstExternal Γ.firstKind).injective he)
    exact Γ.protectedIndex.injective hv

theorem nextProtected_seam (j : σ.ProtSeam) :
    Γ.next.seam (Γ.nextProtected j) = σ.toTorus.seam j.val :=
  ((Γ.group 0).relativeSelected_seam Γ.firstExternal Γ.firstKind _).trans
    (Γ.protected_seam j)

theorem nextProtected_matching (j : σ.ProtSeam) :
    Γ.next.pairing.matching (Γ.nextProtected j) = σ.toTorus.pairing.matching j.val :=
  ((Γ.group 0).relativeSelected_matching Γ.firstExternal Γ.firstKind _).trans
    (Γ.protected_matching j)

theorem nextProtected_outside (j : σ.ProtSeam) (a : Fin n) :
    Γ.nextProtected j ∉ (Γ.nextGroup a).selected := by
  intro hj
  obtain ⟨l, hl⟩ := (Γ.nextGroup a).internal hj
  have he : Γ.protectedIndex j = (Γ.group a.succ).arm l := by
    exact congrArg Subtype.val
      ((Fintype.equivFin (T.AlongUnpairedSeam Γ.firstSelected)).injective hl)
  exact Γ.protected_outside j a.succ (he ▸ (Γ.group a.succ).arm_mem l)

def nextFrozen : σ.Frozen ↪ Fin Γ.next.components.count where
  toFun f := Γ.keptIndex (Γ.frozen_outside f 0)
  inj' f g he := Γ.frozen.injective
    (Γ.keptInjective (Γ.frozen_outside f 0) (Γ.frozen_outside g 0) he)

theorem nextFrozen_outside (f : σ.Frozen) (a : Fin n) :
    Γ.nextFrozen f ∉ (Γ.nextGroup a).set := by
  intro hf
  obtain ⟨i, hi, hia, he⟩ := Γ.nextGroup_mem a hf
  have hei := Γ.keptInjective (Γ.frozen_outside f 0) hi he
  exact Γ.frozen_outside f a.succ (hei.symm ▸ hia)

def nextTransfer (f : σ.Frozen) : PieceTransfer σ.toTorus f.val Γ.next (Γ.nextFrozen f) :=
  (Γ.transfer f).relativeTrans (Γ.keptTransfer (Γ.frozen_outside f 0))

theorem nextOriented (f : σ.Frozen) :
    (Γ.nextTransfer f).map.preservesOrientation
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components f.val).orientation
      (componentCarrier Γ.next.cutCarrier Γ.next.components (Γ.nextFrozen f)).orientation :=
  Diffeomorph.preservesOrientation_trans (Γ.oriented f)
    (Γ.keptOriented (Γ.frozen_outside f 0))

theorem nextCutMap (f : σ.Frozen) (x : σ.toTorus.components.piece f.val) :
    Γ.next.cutMap ((Γ.nextTransfer f).map x).val = σ.toTorus.cutMap x.val :=
  (Γ.keptCutMap (Γ.frozen_outside f 0) ((Γ.transfer f).map x)).trans (Γ.cutMap f x)

theorem not_mem_first_of_castPred (j : Fin Γ.next.components.count)
    (h : j ≠ Fin.last Γ.firstSetᶜ.card) :
    T.subIndex Γ.firstSetᶜ (j.castPred h) ∉ Γ.firstSet :=
  Finset.mem_compl.mp (T.subIndex_mem _ _)

theorem keptIndex_castPred (j : Fin Γ.next.components.count)
    (h : j ≠ Fin.last Γ.firstSetᶜ.card) :
    Γ.keptIndex (Γ.not_mem_first_of_castPred j h) = j := by
  unfold keptIndex TorusPresentation.contractAlongKeptIndex
  rw [TorusPresentation.subIndexOf_subIndex]
  exact Fin.castSucc_castPred j h

theorem rest_cond (j : Fin Γ.next.components.count)
    (h : j ≠ Fin.last Γ.firstSetᶜ.card) (hj : ∀ a, j ∉ (Γ.nextGroup a).set) :
    ∀ a, T.subIndex Γ.firstSetᶜ (j.castPred h) ∉ (Γ.group a).set := by
  intro a
  induction a using Fin.cases with
  | zero => exact Γ.not_mem_first_of_castPred j h
  | succ b =>
    intro hb
    apply hj b
    rw [← Γ.keptIndex_castPred j h]
    exact Γ.nextGroup_index_mem (Γ.not_mem_first_of_castPred j h) b hb

theorem rest_frozen_cond (j : Fin Γ.next.components.count)
    (h : j ≠ Fin.last Γ.firstSetᶜ.card) (hf : ∀ f, Γ.nextFrozen f ≠ j) :
    ∀ f, Γ.frozen f ≠ T.subIndex Γ.firstSetᶜ (j.castPred h) := by
  intro f he
  apply hf f
  change Γ.keptIndex (Γ.frozen_outside f 0) = j
  calc
    Γ.keptIndex (Γ.frozen_outside f 0) =
        Γ.keptIndex (Γ.not_mem_first_of_castPred j h) := by
      apply congrArg Fin.castSucc
      exact (T.subIndexOf_eq_iff _ _).mpr he
    _ = j := Γ.keptIndex_castPred j h

open Classical in
def nextRest (j : Fin Γ.next.components.count) (hj : ∀ a, j ∉ (Γ.nextGroup a).set)
    (hf : ∀ f, Γ.nextFrozen f ≠ j) : {B : PieceBlock Γ.next j // GoodData.{u} B.data} :=
  if h : j = Fin.last Γ.firstSetᶜ.card then
    ⟨((Γ.group 0).relativeSelectedGroupBlock Γ.firstExternal Γ.firstKind).congrIndex h.symm,
      (congrArg GoodData.{u} (PieceBlock.congrIndex_data _ _)).mpr (Γ.good 0)⟩
  else
    ⟨(((Γ.rest _ (Γ.rest_cond j h hj) (Γ.rest_frozen_cond j h hf)).val.transfer
      (Γ.keptTransfer (Γ.not_mem_first_of_castPred j h))
      (Γ.keptOriented (Γ.not_mem_first_of_castPred j h))).congrIndex
      (Γ.keptIndex_castPred j h)),
      (congrArg GoodData.{u} (PieceBlock.congrIndex_data _ _)).mpr
        (Γ.rest _ (Γ.rest_cond j h hj) (Γ.rest_frozen_cond j h hf)).property⟩

def nextGrouping : RelativeGrouping σ Γ.next n where
  data a := Γ.data a.succ
  group := Γ.nextGroup
  arm_pos a := Γ.arm_pos a.succ
  good a := Γ.good a.succ
  disjoint := Γ.nextDisjoint
  protectedIndex := Γ.nextProtected
  protected_seam := Γ.nextProtected_seam
  protected_matching := Γ.nextProtected_matching
  protected_outside := Γ.nextProtected_outside
  frozen := Γ.nextFrozen
  transfer := Γ.nextTransfer
  oriented := Γ.nextOriented
  cutMap := Γ.nextCutMap
  frozen_outside := Γ.nextFrozen_outside
  rest := Γ.nextRest

end RelativeGrouping

theorem RelativeGrouping.exists_groupedPresentation
    {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q} :
    ∀ n {T : TorusPresentation (NoCuts.carrier Q)}, RelativeGrouping σ T n →
      Nonempty (RelativeGroupedPresentation σ)
  | 0, _, Γ => ⟨Γ.finish⟩
  | n + 1, _, Γ => RelativeGrouping.exists_groupedPresentation n Γ.nextGrouping

end GC.Seifert.RelativeNormalization
