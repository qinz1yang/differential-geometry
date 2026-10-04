import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
Actual signed spherical cuts have two prescribed components when their ordinary complement has
two connected open sides. Native half collars prove zero-copy density and fix the side labels.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}} (c : SphereCutSignedCollars W)
  (hs : ∀ j, (c j).source = sphereSignedCollarSource)
  (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
  (A : Bool → Set W.Carrier)
  (hconnected : ∀ b, IsConnected (A b)) (hopen : ∀ b, IsOpen (A b))
  (hdisjoint : Disjoint (A false) (A true))
  (hcover : (sphereCutAmbientZero c)ᶜ = A false ∪ A true)
  (hgerm : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ b z s, 0 < s → s < η →
    c 0 (z, sphereCutSign b s) ∈ A b)

def sphereCutSideCore (b : Bool) : Set (SphereCutSpace c) := sphereCutFold c ⁻¹' A b

def sphereCutSideSet (b : Bool) : Set (SphereCutSpace c) :=
  sphereCutSideCore c A b ∪ range (sphereCutZero c 0 b)

include hcover in
private theorem sphereCutSide_subset (b : Bool) : A b ⊆ (sphereCutAmbientZero c)ᶜ := by
  rw [hcover]
  cases b
  · exact subset_union_left
  · exact subset_union_right

private theorem sphereCutZero_fold_mem (b : Bool) (z : ClosureSphere.{u}) :
    sphereCutFold c (sphereCutZero c 0 b z) ∈ sphereCutAmbientZero c := by
  exact mem_iUnion.mpr ⟨0, z, (sphereCutZero_fold c 0 b z).symm⟩

include hs hd hcover in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutSideCore_image (b : Bool) :
    sphereCutSideCore c A b = sphereCutAmbientPartialDiffeomorph c hs hd '' A b := by
  let e := sphereCutAmbientPartialDiffeomorph c hs hd
  ext x
  constructor
  · intro hx
    have hxoff : x ∈ sphereCutOffZero c := sphereCutSide_subset c A hcover b hx
    have hxt : x ∈ e.target := by
      change x ∈ (sphereCutAmbientPatch c hs hd).target
      rwa [sphereCutAmbientPatch_target]
    have hsym : e.symm x = sphereCutFold c x := sphereCutAmbientPatch_symm c hs hd x hxt
    exact ⟨sphereCutFold c x, hx, hsym ▸ e.right_inv hxt⟩
  · rintro ⟨y, hy, rfl⟩
    change sphereCutFold c (e y) ∈ A b
    rw [sphereCutAmbientPartialDiffeomorph_fold c hs hd y
      (sphereCutSide_subset c A hcover b hy)]
    exact hy

include hs hd hconnected hcover in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutSideCore_connected (b : Bool) : IsConnected (sphereCutSideCore c A b) := by
  rw [sphereCutSideCore_image c hs hd A hcover b]
  exact (hconnected b).image _
    ((sphereCutAmbientPartialDiffeomorph c hs hd).toOpenPartialHomeomorph.continuousOn.mono
      fun y hy =>
      (sphereCutAmbientPartialDiffeomorph_source c hs hd).symm.subset
        (sphereCutSide_subset c A hcover b hy))

private theorem sphereCutComponentsHalfCoordinate_continuous : Continuous halfSpaceOneLift := by
  change Continuous (fun s : ℝ => halfSpaceOneLift s)
  simp_rw [halfSpaceOneLift_eq]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk fun s => le_max_left 0 s)

private theorem sphereCutHalfLift_zero : halfSpaceOneLift 0 = halfZero := by
  exact (halfPoint_eq_self (halfSpaceOneLift 0) le_rfl (by
    change (0 : ℝ) = max 0 0
    exact (max_self 0).symm)).symm

include hs hd hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutZero_mem_closure_sideCore (b : Bool) (z : ClosureSphere.{u}) :
    sphereCutZero c 0 b z ∈ closure (sphereCutSideCore c A b) := by
  obtain ⟨η, hη, hη1, hsign⟩ := hgerm
  let e := sphereCutFullCollar c hs hd 0 b
  let f : ℝ → SphereCutSpace c := fun s => e (z, halfSpaceOneLift s)
  have hp0 : (z, halfSpaceOneLift 0) ∈ e.source := by
    rw [sphereCutFullCollar_source, sphereCutHalfLift_zero]
    change (0 : ℝ) < 1
    norm_num
  have hparam : ContinuousAt (fun s : ℝ => (z, halfSpaceOneLift s)) 0 :=
    (continuous_const.prodMk sphereCutComponentsHalfCoordinate_continuous).continuousAt
  have he : ContinuousAt (fun p => e p) (z, halfSpaceOneLift 0) :=
    e.toOpenPartialHomeomorph.continuousOn.continuousAt (e.open_source.mem_nhds hp0)
  have hf : ContinuousAt f 0 :=
    ContinuousAt.comp (f := fun s : ℝ => (z, halfSpaceOneLift s)) (x := 0) he hparam
  have hzero : f 0 = sphereCutZero c 0 b z := by
    change e (z, halfSpaceOneLift 0) = _
    rw [sphereCutHalfLift_zero, sphereCutFullCollar_zero]
  rw [← hzero]
  apply hf.continuousWithinAt.mem_closure
    (s := Ioo (0 : ℝ) η) ?_ ?_
  · rw [closure_Ioo hη.ne]
    exact ⟨le_rfl, hη.le⟩
  · intro s hsη
    have hcoord : (halfSpaceOneLift s).val 0 = s := max_eq_left hsη.1.le
    have hp : (z, halfSpaceOneLift s) ∈ sphereHalfCollarSource := by
      change (halfSpaceOneLift s).val 0 < 1
      rw [hcoord]
      linarith [hsη.2]
    change sphereCutFold c (e (z, halfSpaceOneLift s)) ∈ A b
    rw [sphereCutFullCollar_fold c hs hd 0 b _ hp]
    change c 0 (z, sphereCutSign b ((halfSpaceOneLift s).val 0)) ∈ A b
    rw [hcoord]
    exact hsign b z s hsη.1 hsη.2

include hs hd hgerm in
theorem sphereCutSideSet_subset_closure (b : Bool) :
    sphereCutSideSet c A b ⊆ closure (sphereCutSideCore c A b) := by
  rintro x (hx | ⟨z, rfl⟩)
  · exact subset_closure hx
  · exact sphereCutZero_mem_closure_sideCore c hs hd A hgerm b z

include hs hd hconnected hcover hgerm in
theorem sphereCutSideSet_connected (b : Bool) : IsConnected (sphereCutSideSet c A b) :=
  (sphereCutSideCore_connected c hs hd A hconnected hcover b).subset_closure
    subset_union_left (sphereCutSideSet_subset_closure c hs hd A hgerm b)

theorem sphereCutSideSet_offZero (b : Bool) (x : SphereCutSpace c)
    (hx : x ∈ sphereCutOffZero c) : x ∈ sphereCutSideSet c A b ↔ sphereCutFold c x ∈ A b := by
  constructor
  · rintro (h | ⟨z, rfl⟩)
    · exact h
    · exact (hx (sphereCutZero_fold_mem c b z)).elim
  · exact Or.inl

include hdisjoint hcover in
theorem sphereCutSideSet_disjoint : Disjoint (sphereCutSideSet c A false)
    (sphereCutSideSet c A true) := by
  apply disjoint_left.mpr
  rintro x (hx | ⟨z, rfl⟩) (hy | ⟨w, hw⟩)
  · exact disjoint_left.mp hdisjoint hx hy
  · exact sphereCutSide_subset c A hcover false hx
      (hw ▸ sphereCutZero_fold_mem c true w)
  · exact sphereCutSide_subset c A hcover true hy (sphereCutZero_fold_mem c false z)
  · exact sphereCutZero_ne c 0 w z hw

include hs hd hcover in
theorem sphereCutSideSet_cover : sphereCutSideSet c A false ∪ sphereCutSideSet c A true =
    univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : sphereCutFold c x ∈ sphereCutAmbientZero c
  · obtain ⟨j, z, hz⟩ := mem_iUnion.mp hx
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    obtain ⟨b, rfl⟩ := sphereCutFold_fiber_zero c hs hd 0 z x hz.symm
    cases b
    · exact Or.inl (Or.inr (mem_range_self z))
    · exact Or.inr (Or.inr (mem_range_self z))
  · have hside : sphereCutFold c x ∈ A false ∪ A true := hcover ▸ hx
    rcases hside with hf | ht
    · exact Or.inl (Or.inl hf)
    · exact Or.inr (Or.inl ht)

include hs hd hgerm hopen in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutSideSet_open (b : Bool) : IsOpen (sphereCutSideSet c A b) := by
  obtain ⟨η, hη, hη1, hsign⟩ := hgerm
  let e := sphereCutFullCollar c hs hd 0 b
  let V : Set (ClosureSphere.{u} × EuclideanHalfSpace 1) := {p | p.2.val 0 < η}
  have hV : IsOpen V := isOpen_lt
    (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd) continuous_const
  have hVs : V ⊆ e.source := by
    intro p hp
    rw [sphereCutFullCollar_source]
    change p.2.val 0 < 1
    change p.2.val 0 < η at hp
    linarith
  have himage : e '' V ⊆ sphereCutSideSet c A b := by
    rintro x ⟨p, hp, rfl⟩
    have hps : p ∈ sphereHalfCollarSource :=
      (sphereCutFullCollar_source c hs hd 0 b).subset (hVs hp)
    by_cases hzero : p.2.val 0 = 0
    · have he : p.2 = halfZero := (halfPoint_eq_self p.2 le_rfl hzero.symm).symm
      right
      refine ⟨p.1, ?_⟩
      change sphereCutZero c 0 b p.1 = sphereCutFullCollar c hs hd 0 b (p.1, p.2)
      rw [he, sphereCutFullCollar_zero]
    · left
      change sphereCutFold c (e p) ∈ A b
      rw [sphereCutFullCollar_fold c hs hd 0 b p hps]
      exact hsign b p.1 (p.2.val 0) (lt_of_le_of_ne p.2.property (Ne.symm hzero)) hp
  apply isOpen_iff_mem_nhds.mpr
  rintro x (hx | ⟨z, rfl⟩)
  · exact mem_of_superset (((hopen b).preimage (sphereCutFold_continuous c)).mem_nhds hx)
      subset_union_left
  · have hz : sphereCutZero c 0 b z ∈ e '' V := by
      refine ⟨(z, halfZero), hη, ?_⟩
      exact sphereCutFullCollar_zero c hs hd 0 b z
    exact mem_of_superset
      ((e.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hVs).mem_nhds hz) himage

include hs hd hcover hdisjoint in
theorem sphereCutSideSet_compl (b : Bool) :
    (sphereCutSideSet c A b)ᶜ = sphereCutSideSet c A (!b) := by
  have hcov := sphereCutSideSet_cover c hs hd A hcover
  have hdis := sphereCutSideSet_disjoint c A hdisjoint hcover
  ext x
  cases b <;> constructor
  · intro hx
    exact (hcov.symm ▸ mem_univ x : x ∈ sphereCutSideSet c A false ∪
      sphereCutSideSet c A true).resolve_left hx
  · intro hx hy
    exact disjoint_left.mp hdis hy hx
  · intro hx
    exact (hcov.symm ▸ mem_univ x : x ∈ sphereCutSideSet c A false ∪
      sphereCutSideSet c A true).resolve_right hx
  · intro hx hy
    exact disjoint_left.mp hdis hx hy

include hs hd hcover hgerm hopen hdisjoint in
theorem sphereCutSideSet_closed (b : Bool) : IsClosed (sphereCutSideSet c A b) := by
  rw [← isOpen_compl_iff, sphereCutSideSet_compl c hs hd A hdisjoint hcover b]
  exact sphereCutSideSet_open c hs hd A hopen hgerm (!b)


include hs hd hopen hdisjoint hcover hgerm in
theorem sphereCutSideSet_closure (b : Bool) :
    closure (sphereCutSideCore c A b) = sphereCutSideSet c A b :=
  subset_antisymm
    ((sphereCutSideSet_closed c hs hd A hopen hdisjoint hcover hgerm b).closure_subset_iff.mpr
      subset_union_left)
    (sphereCutSideSet_subset_closure c hs hd A hgerm b)

include hcover in
theorem sphereCutSideSet_zero_mem (b d : Bool) (z : ClosureSphere.{u}) :
    sphereCutZero c 0 d z ∈ sphereCutSideSet c A b ↔ d = b := by
  constructor
  · rintro (hx | ⟨w, hw⟩)
    · exact (sphereCutSide_subset c A hcover b hx (sphereCutZero_fold_mem c d z)).elim
    · cases b <;> cases d
      · rfl
      · exact (sphereCutZero_ne c 0 z w hw.symm).elim
      · exact (sphereCutZero_ne c 0 w z hw).elim
      · rfl
  · rintro rfl
    exact Or.inr (mem_range_self z)

private theorem sphereCutBoundarySide_injective : Injective sphereCutBoundarySide := by
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | cases he

include hs hd hconnected hopen hdisjoint hcover hgerm in
def sphereCutSideOpen (b : Bool) : Opens (sphereCutCarrier c hs hd).Carrier :=
  ⟨sphereCutSideSet c A b, sphereCutSideSet_open c hs hd A hopen hgerm b⟩

include hs hd hconnected hopen hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutSideInterior_connected (b : Bool) :
    ConnectedSpace ((sphereCutCarrier c hs hd).pieceInterior
      (sphereCutSideOpen c hs hd A hopen hgerm b)) := by
  let K := sphereCutCarrier c hs hd
  let U := sphereCutSideOpen c hs hd A hopen hgerm b
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp
    (sphereCutSideSet_connected c hs hd A hconnected hcover hgerm b)
  have he : (K.pieceInterior U : Set K.Carrier) = K.model.interior K.Carrier ∩ U := by
    ext x
    exact and_comm
  apply isConnected_iff_connectedSpace.mp
  rw [he]
  have hp : IsPreconnected (U : Set K.Carrier) :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hdense := dense_manifold_interior (I := K.model) (M := U)
  obtain ⟨x, hx⟩ := hdense.nonempty
  refine ⟨⟨x.val, ?_, x.property⟩, isPreconnected_manifold_interior_inter_open U hp⟩
  exact K.model.isInteriorPoint_iff_isInteriorPoint_val.mp hx

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
def sphereCutComponents : (sphereCutCarrier c hs hd).Components where
  count := 2
  count_pos := by norm_num
  piece i := sphereCutSideOpen c hs hd A hopen hgerm
    (sphereCutBoundarySide i)
  closed i := sphereCutSideSet_closed c hs hd A hopen hdisjoint hcover hgerm
    (sphereCutBoundarySide i)
  connected i := isConnected_iff_connectedSpace.mp
    (sphereCutSideSet_connected c hs hd A hconnected hcover hgerm (sphereCutBoundarySide i))
  disjoint := by
    intro i j hij
    have hbij := (sphereCutBoundarySide_injective.ne hij)
    have hdis := sphereCutSideSet_disjoint c A hdisjoint hcover
    cases hi : sphereCutBoundarySide i <;> cases hj : sphereCutBoundarySide j
    · exact (hbij (hi.trans hj.symm)).elim
    · exact hdis
    · exact hdis.symm
    · exact (hbij (hi.trans hj.symm)).elim
  covers := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx := (sphereCutSideSet_cover c hs hd A hcover).symm ▸ mem_univ x
    rcases hx with hf | ht
    · exact ⟨0, hf⟩
    · exact ⟨1, ht⟩
  interior_connected i := sphereCutSideInterior_connected c hs hd A hconnected hopen
    hcover hgerm (sphereCutBoundarySide i)

include hs hd hconnected hopen hdisjoint hcover hgerm in
theorem sphereCutComponents_count :
    (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).count = 2 := rfl

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_piece (i : Fin 2) :
    ((sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece i :
      Set (sphereCutCarrier c hs hd).Carrier) = sphereCutFold c ⁻¹' A (sphereCutBoundarySide i) ∪
        range (sphereCutZero c 0 (sphereCutBoundarySide i)) := rfl

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_offZero_mem (i : Fin 2) (x : SphereCutSpace c)
    (hx : x ∈ sphereCutOffZero c) :
    x ∈ (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece i ↔
      sphereCutFold c x ∈ A (sphereCutBoundarySide i) :=
  sphereCutSideSet_offZero c A (sphereCutBoundarySide i) x hx

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_zero_mem (i : Fin 2) (b : Bool) (z : ClosureSphere.{u}) :
    sphereCutZero c 0 b z ∈
      (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece i ↔
        b = sphereCutBoundarySide i :=
  sphereCutSideSet_zero_mem c A hcover (sphereCutBoundarySide i) b z

private theorem sphereCutHalfSource_connected {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] : IsConnected {p : X × EuclideanHalfSpace 1 | p.2.val 0 < 1} := by
  let H : Set (EuclideanHalfSpace 1) := {h | h.val 0 < 1}
  have he : H = halfSpaceOneLift '' Ico (0 : ℝ) 1 := by
    ext h
    constructor
    · intro hh
      refine ⟨h.val 0, ⟨h.property, hh⟩, ?_⟩
      apply Subtype.ext
      ext i
      fin_cases i
      change max (h.val 0) 0 = h.val 0
      exact max_eq_left h.property
    · rintro ⟨s, hs, rfl⟩
      change max s 0 < 1
      rw [max_eq_left hs.1]
      exact hs.2
  have hH : IsConnected H := by
    rw [he]
    exact (isConnected_Ico (by norm_num : (0 : ℝ) < 1)).image _
      sphereCutComponentsHalfCoordinate_continuous.continuousOn
  have hp := (isConnected_univ : IsConnected (univ : Set X)).prod hH
  convert hp using 1
  ext p
  simp only [H, mem_ofPred_eq, mem_prod, mem_univ, true_and]

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_fullCollar_owned (i : Fin 2) :
    (sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i)).target ⊆
      (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece i := by
  let e := sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i)
  have hsource : IsConnected e.source := by
    rw [sphereCutFullCollar_source]
    exact sphereCutHalfSource_connected
  have htarget : IsPreconnected e.target := by
    change IsPreconnected e.toOpenPartialHomeomorph.target
    rw [← e.toOpenPartialHomeomorph.image_source_eq_target]
    exact (hsource.image e e.toOpenPartialHomeomorph.continuousOn).isPreconnected
  change e.target ⊆ sphereCutSideSet c A (sphereCutBoundarySide i)
  apply htarget.subset_isClopen
    ⟨sphereCutSideSet_closed c hs hd A hopen hdisjoint hcover hgerm _,
      sphereCutSideSet_open c hs hd A hopen hgerm _⟩
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  refine ⟨sphereCutZero c 0 (sphereCutBoundarySide i) z, ?_, ?_⟩
  · rw [← sphereCutFullCollar_zero c hs hd 0 (sphereCutBoundarySide i) z]
    apply e.map_source
    rw [sphereCutFullCollar_source]
    change (0 : ℝ) < 1
    norm_num
  · exact Or.inr (mem_range_self z)

include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_retained_owned {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) (i : Fin n) (k : Fin 2)
    (howner : ∀ t : Torus, E.torusMap i t ∈ A (sphereCutBoundarySide k)) (t : Torus) :
    sphereCutRetainedCollar c hs hd E i (t, halfZero) ∈
      (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece k := by
  change sphereCutRetainedCollar c hs hd E i (t, halfZero) ∈
    sphereCutSideSet c A (sphereCutBoundarySide k)
  left
  change sphereCutFold c (sphereCutRetainedCollar c hs hd E i (t, halfZero)) ∈
    A (sphereCutBoundarySide k)
  rw [sphereCutRetainedCollar_fold c hs hd E havoid i _
    (zero_mem_halfCollarSource t)]
  exact howner t


include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem sphereCutComponents_retained_full_owned {n : ℕ} (E : BoundaryTori W n)
    (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target) (i : Fin n) (k : Fin 2)
    (howner : ∀ t : Torus, E.torusMap i t ∈ A (sphereCutBoundarySide k)) :
    (sphereCutRetainedCollar c hs hd E i).target ⊆
      (sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm).piece k := by
  let e := sphereCutRetainedCollar c hs hd E i
  have hsource : IsConnected e.source := by
    rw [sphereCutRetainedCollar_source c hs hd E havoid i]
    exact sphereCutHalfSource_connected
  have htarget : IsPreconnected e.target := by
    change IsPreconnected e.toOpenPartialHomeomorph.target
    rw [← e.toOpenPartialHomeomorph.image_source_eq_target]
    exact (hsource.image e e.toOpenPartialHomeomorph.continuousOn).isPreconnected
  change e.target ⊆ sphereCutSideSet c A (sphereCutBoundarySide k)
  apply htarget.subset_isClopen
    ⟨sphereCutSideSet_closed c hs hd A hopen hdisjoint hcover hgerm _,
      sphereCutSideSet_open c hs hd A hopen hgerm _⟩
  let t : Torus := (1, 1)
  refine ⟨e (t, halfZero), ?_, ?_⟩
  · apply e.map_source
    rw [sphereCutRetainedCollar_source c hs hd E havoid i]
    exact zero_mem_halfCollarSource t
  · exact sphereCutComponents_retained_owned c hs hd A hconnected hopen hdisjoint hcover
      hgerm E havoid i k howner t


include hs hd hconnected hopen hdisjoint hcover hgerm in
set_option backward.isDefEq.respectTransparency false in
theorem exists_sphereCutComponents :
    ∃ D : (sphereCutCarrier c hs hd).Components, ∃ hc : D.count = 2,
      (∀ i : Fin 2, (D.piece (Fin.cast hc.symm i) : Set (sphereCutCarrier c hs hd).Carrier) =
        sphereCutFold c ⁻¹' A (sphereCutBoundarySide i) ∪
          range (sphereCutZero c 0 (sphereCutBoundarySide i))) ∧
      (∀ i : Fin 2, ∀ b : Bool, ∀ z : ClosureSphere.{u},
        sphereCutZero c 0 b z ∈ D.piece (Fin.cast hc.symm i) ↔ b = sphereCutBoundarySide i) ∧
      (∀ i : Fin 2, (sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i)).target ⊆
        D.piece (Fin.cast hc.symm i)) :=
  ⟨sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm, rfl,
    sphereCutComponents_piece c hs hd A hconnected hopen hdisjoint hcover hgerm,
    sphereCutComponents_zero_mem c hs hd A hconnected hopen hdisjoint hcover hgerm,
    sphereCutComponents_fullCollar_owned c hs hd A hconnected hopen hdisjoint hcover hgerm⟩

end GC.GraphManifold
