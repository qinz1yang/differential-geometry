import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateSphereFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece

/-!
# FC42 sphere recursion, packet S1: ports of a capped component, circle-fibre labels

Lane ASM-SPH (review 40 §2.3 and §2.5, dispositions packet S1).

* `PortRestriction`: for boundary tori `T` of a compact carrier `Q` and a component decomposition
  `DQ`, every collar target is connected, hence lies in exactly one piece (`existsUnique_piece`);
  the index set of piece `i` is the reviewer's `I_i = {a | target (collar a) ⊆ piece i}`
  (`portPiece_eq_iff`), numbered by `Fintype.equivFin`. `restrictComponent` are the restricted
  boundary tori of the component carrier; on the WHOLE collar they are the old collars
  (`restrictComponent_collar_apply`), and when `T` exhausts `∂Q` they exhaust the boundary of the
  component (`boundary_restrictComponent`). Every port goes to exactly one component
  (`sum_card_componentPorts`).
* `SphereCutCapped.componentTori`: the ports `E_i` of a capped component of a sphere cut, with the
  reviewer's equation `ι_i (E_i.collar (a, p)) = retained.collar (ā, p) = core (B.tori.collar (ā, p))`
  (`componentTori_collar`, from `RelativeSphereCapping.retained_collar`) and the old port of `W`
  behind it (`componentTori_fold`).
* `CircleRegion`: a label continuous on a saturated set of the circle-region domain (for instance
  the component of the transported point) is constant on the connected circle fibres
  (`label_eq_of_proj_eq`); the base parts of the labels are open, pairwise disjoint and saturated
  back, so the base of each label is open and closed in the projected set.

Precision against the review text: the reviewer's `range (retained.collar a)` is the collar
TARGET (the `range` of the coercion of a partial diffeomorphism contains junk values off its
source).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## Ports restricted to a component -/

namespace PortRestriction

variable {Q : CompactCarrier.{u}} {m : ℕ} (T : BoundaryTori Q m) (DQ : Q.Components)

/-- The zero section of a collar lies in its target. -/
theorem torusMap_mem_target (a : Fin m) (t : Torus) : T.torusMap a t ∈ (T.collar a).target :=
  (T.collar a).map_source ((T.source_eq a).symm ▸ zero_mem_halfCollarSource t)

/-- A collar target meeting a piece lies in it (the target is connected, the piece clopen). -/
theorem target_subset_piece_of_mem (a : Fin m) {i : Fin DQ.count} {x : Q.Carrier}
    (hx : x ∈ (T.collar a).target) (hxi : x ∈ (DQ.piece i : Set Q.Carrier)) :
    (T.collar a).target ⊆ (DQ.piece i : Set Q.Carrier) := by
  obtain ⟨p, hp, rfl⟩ := exists_eq_of_mem_target_of_source_eq _ (T.source_eq a) hx
  exact target_subset_piece_of_source_eq DQ (T.collar a) (T.source_eq a)
    ((T.source_eq a).symm ▸ hp) hxi

/-- **S1.** A collar target lies in exactly one piece. -/
theorem existsUnique_piece (a : Fin m) :
    ∃! i, (T.collar a).target ⊆ (DQ.piece i : Set Q.Carrier) := by
  let t : Torus := (1, 1)
  obtain ⟨i, hi⟩ := exists_mem_componentsPiece DQ (T.torusMap a t)
  refine ⟨i, target_subset_piece_of_mem T DQ a (torusMap_mem_target T a t) hi, fun j hj => ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (DQ.disjoint hne) (hj (torusMap_mem_target T a t)) hi

/-- The piece containing the collar of port `a`. -/
def portPiece (a : Fin m) : Fin DQ.count :=
  (existsUnique_piece T DQ a).exists.choose

theorem target_subset_portPiece (a : Fin m) :
    (T.collar a).target ⊆ (DQ.piece (portPiece T DQ a) : Set Q.Carrier) :=
  (existsUnique_piece T DQ a).exists.choose_spec

variable {T DQ} in
/-- The reviewer's index set: `portPiece a = i` iff the whole collar target of `a` lies in the
piece `i`. -/
theorem portPiece_eq_iff {a : Fin m} {i : Fin DQ.count} :
    portPiece T DQ a = i ↔ (T.collar a).target ⊆ (DQ.piece i : Set Q.Carrier) :=
  ⟨fun h => h ▸ target_subset_portPiece T DQ a,
    fun h => (existsUnique_piece T DQ a).unique (target_subset_portPiece T DQ a) h⟩

/-- The ports of component `i`. -/
abbrev ComponentPorts (i : Fin DQ.count) : Type :=
  {a : Fin m // portPiece T DQ a = i}

/-- Numbering of the ports of component `i` (`Fintype.equivFin`). -/
def componentPortEquiv (i : Fin DQ.count) :
    Fin (Fintype.card (ComponentPorts T DQ i)) ≃ ComponentPorts T DQ i :=
  (Fintype.equivFin _).symm

theorem target_subset_of_port (i : Fin DQ.count) (a : ComponentPorts T DQ i) :
    (T.collar a.1).target ⊆ (DQ.piece i : Set Q.Carrier) :=
  portPiece_eq_iff.mp a.2

/-- The collar of a port of component `i`, with codomain the piece. -/
def portCollar (i : Fin DQ.count) (a : ComponentPorts T DQ i) :
    PartialDiffeomorph halfCollarModel Q.model (Torus × EuclideanHalfSpace 1) (DQ.piece i) ∞ :=
  codRestrictOpens (T.collar a.1) (DQ.piece i) (DQ.connected i).toNonempty

theorem portCollar_source (i : Fin DQ.count) (a : ComponentPorts T DQ i) :
    (portCollar T DQ i a).source = halfCollarSource :=
  (codRestrictOpens_source _ _ _ (target_subset_of_port T DQ i a)).trans (T.source_eq a.1)

theorem portCollar_target (i : Fin DQ.count) (a : ComponentPorts T DQ i) :
    (portCollar T DQ i a).target = Subtype.val ⁻¹' (T.collar a.1).target :=
  codRestrictOpens_target _ _ _

theorem portCollar_apply (i : Fin DQ.count) (a : ComponentPorts T DQ i)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (portCollar T DQ i a p : Q.Carrier) = T.collar a.1 p :=
  codRestrictOpens_apply _ _ _ (target_subset_of_port T DQ i a
    ((T.collar a.1).map_source' ((T.source_eq a.1).symm ▸ hp)))

/-- **S1.** The restricted ports `E_i : BoundaryTori Q_i |I_i|`. -/
def restrictComponent (i : Fin DQ.count) :
    BoundaryTori (GC.Topology.componentCarrier Q DQ i) (Fintype.card (ComponentPorts T DQ i)) where
  collar a := portCollar T DQ i (componentPortEquiv T DQ i a)
  source_eq a := portCollar_source T DQ i _
  boundary_zero a t := by
    refine (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := Q.model)
      (u := DQ.piece i)).mpr ?_
    have h := T.boundary_zero (componentPortEquiv T DQ i a).1 t
    rw [← portCollar_apply T DQ i _ (zero_mem_halfCollarSource t)] at h
    exact h
  disjoint a b hab := by
    change Disjoint (portCollar T DQ i _).target (portCollar T DQ i _).target
    rw [portCollar_target, portCollar_target]
    exact (T.disjoint fun e => hab ((componentPortEquiv T DQ i).injective (Subtype.ext e))).preimage _

/-- **S1, whole-collar commutation.** -/
theorem restrictComponent_collar_apply (i : Fin DQ.count)
    (a : Fin (Fintype.card (ComponentPorts T DQ i))) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    ((restrictComponent T DQ i).collar a p).val = T.collar (componentPortEquiv T DQ i a).1 p :=
  portCollar_apply T DQ i _ hp

theorem restrictComponent_collar_target (i : Fin DQ.count)
    (a : Fin (Fintype.card (ComponentPorts T DQ i))) :
    ((restrictComponent T DQ i).collar a).target =
      Subtype.val ⁻¹' (T.collar (componentPortEquiv T DQ i a).1).target :=
  portCollar_target T DQ i _

theorem restrictComponent_torusMap (i : Fin DQ.count)
    (a : Fin (Fintype.card (ComponentPorts T DQ i))) (t : Torus) :
    ((restrictComponent T DQ i).torusMap a t).val = T.torusMap (componentPortEquiv T DQ i a).1 t :=
  portCollar_apply T DQ i _ (zero_mem_halfCollarSource t)

/-- **S1.** When `T` exhausts `∂Q`, the restricted ports exhaust the boundary of the component. -/
theorem boundary_restrictComponent (hT : Q.model.boundary Q.Carrier = T.image)
    (i : Fin DQ.count) :
    (GC.Topology.componentCarrier Q DQ i).model.boundary
        (GC.Topology.componentCarrier Q DQ i).Carrier =
      (restrictComponent T DQ i).image := by
  ext x
  constructor
  · intro hx
    have hx' : x.val ∈ Q.model.boundary Q.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val (I := Q.model)
        (u := DQ.piece i)).mp hx
    rw [hT] at hx'
    obtain ⟨a, t, hat⟩ := mem_iUnion.mp hx'
    have ha : portPiece T DQ a = i := by
      by_contra hne
      have hmem := target_subset_portPiece T DQ a (torusMap_mem_target T a t)
      rw [hat] at hmem
      exact Set.disjoint_left.mp (DQ.disjoint hne) hmem x.property
    refine mem_iUnion.mpr ⟨(componentPortEquiv T DQ i).symm ⟨a, ha⟩, t, Subtype.ext ?_⟩
    rw [restrictComponent_torusMap, Equiv.apply_symm_apply]
    exact hat
  · intro hx
    obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hx
    exact (restrictComponent T DQ i).boundary_zero j t

/-- Every port goes to exactly one component. -/
theorem sum_card_componentPorts :
    ∑ i, Fintype.card (ComponentPorts T DQ i) = m := by
  simp only [Fintype.card_subtype]
  rw [← Finset.card_eq_sum_card_fiberwise (f := portPiece T DQ) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  exact Finset.card_fin m

end PortRestriction

/-! ## The ports of a capped component of a sphere cut -/

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E) (DQ : X.Q.Components)

/-- **S1.** `E_i`: the retained ports of the capped carrier restricted to component `i`. -/
abbrev componentTori (i : Fin DQ.count) :=
  PortRestriction.restrictComponent X.capping.retained DQ i

/-- **S1, the reviewer's equation** `ι_i (E_i.collar (a, p)) = retained.collar (ā, p) =
core (B.tori.collar (ā, p))`, on the whole collar. -/
theorem componentTori_collar (i : Fin DQ.count)
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((X.componentTori DQ i).collar a p).val =
        X.capping.retained.collar
          (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1 p ∧
      X.capping.retained.collar (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1 p =
        X.capping.core (X.B.tori.collar
          (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1 p) :=
  ⟨PortRestriction.restrictComponent_collar_apply _ DQ i a hp,
    X.capping.retained_collar _ p hp⟩

/-- The old port of `W` behind a restricted port: `fold (B.tori.collar ā p) = E.collar ā p`. -/
theorem componentTori_fold (i : Fin DQ.count)
    (a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i)))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    X.fold (X.B.tori.collar (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1 p) =
      E.collar (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1)
        p := by
  have h := X.tori (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1)
    p hp
  simpa using h

/-- **S1.** The ports `E_i` exhaust the boundary of the capped component. -/
theorem componentTori_boundary (i : Fin DQ.count) :
    (GC.Topology.componentCarrier X.Q DQ i).model.boundary
        (GC.Topology.componentCarrier X.Q DQ i).Carrier =
      (X.componentTori DQ i).image :=
  PortRestriction.boundary_restrictComponent _ DQ X.capping.boundary_exhausted i

end SphereCutCapped

/-! ## Labels on circle fibres -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W) {ι : Type*} [TopologicalSpace ι]
  [DiscreteTopology ι] {O : Set R.domain} {lab : R.domain → ι}

/-- A fibre of the projection, as a subset of the domain, is preconnected. -/
theorem isPreconnected_proj_preimage (y : R.domain) :
    IsPreconnected (R.proj ⁻¹' {R.proj y}) :=
  Topology.IsInducing.subtypeVal.isPreconnected_image.mp (R.isPreconnected_fibre y)

/-- **S1.** A label continuous on a saturated set is constant on the (connected) fibres. -/
theorem label_eq_of_proj_eq (hsat : ∀ x y, R.proj x = R.proj y → x ∈ O → y ∈ O)
    (hlab : ContinuousOn lab O) {x y : R.domain} (hx : x ∈ O) (hxy : R.proj x = R.proj y) :
    lab x = lab y := by
  have hsub : R.proj ⁻¹' {R.proj x} ⊆ O := fun z hz => hsat x z hz.symm hx
  exact (R.isPreconnected_proj_preimage x).constant (hlab.mono hsub) rfl
    (show R.proj y = R.proj x from hxy.symm)

/-- **S1.** The base part of one label is open. -/
theorem isOpen_proj_image_label (hO : IsOpen O) (hlab : ContinuousOn lab O) (i : ι) :
    IsOpen (R.proj '' (O ∩ lab ⁻¹' {i})) :=
  R.isOpenMap_proj _ (hlab.isOpen_inter_preimage hO (isOpen_discrete {i}))

/-- **S1.** Different labels have disjoint base parts. -/
theorem disjoint_proj_image_label (hsat : ∀ x y, R.proj x = R.proj y → x ∈ O → y ∈ O)
    (hlab : ContinuousOn lab O) {i j : ι} (hij : i ≠ j) :
    Disjoint (R.proj '' (O ∩ lab ⁻¹' {i})) (R.proj '' (O ∩ lab ⁻¹' {j})) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, ⟨hxO, hxi⟩, rfl⟩ ⟨y, ⟨-, hyj⟩, hyx⟩
  have h := R.label_eq_of_proj_eq hsat hlab hxO hyx.symm
  rw [mem_preimage, mem_singleton_iff] at hxi hyj
  exact hij (hxi.symm.trans (h.trans hyj))

/-- **S1.** The base part of a label is saturated back: its preimage is exactly the label set. -/
theorem preimage_proj_image_label (hsat : ∀ x y, R.proj x = R.proj y → x ∈ O → y ∈ O)
    (hlab : ContinuousOn lab O) (i : ι) :
    R.proj ⁻¹' (R.proj '' (O ∩ lab ⁻¹' {i})) = O ∩ lab ⁻¹' {i} := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨x, ⟨hxO, hxi⟩, hxy⟩
  exact ⟨hsat x y hxy hxO, (R.label_eq_of_proj_eq hsat hlab hxO hxy).symm.trans hxi⟩

omit [TopologicalSpace ι] [DiscreteTopology ι] in
/-- The base parts of the labels cover the projected set. -/
theorem iUnion_proj_image_label :
    (⋃ i, R.proj '' (O ∩ lab ⁻¹' {i})) = R.proj '' O := by
  ext b
  simp only [mem_iUnion, mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨i, x, ⟨hx, -⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨lab x, x, ⟨hx, rfl⟩, rfl⟩

end CircleRegion

end GC.GraphManifold.Assembly
