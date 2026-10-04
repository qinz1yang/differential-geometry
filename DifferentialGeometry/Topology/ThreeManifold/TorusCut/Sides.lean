import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Coverage
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.MarkedSeams
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder

set_option autoImplicit false

/-!
# Sides, seams and incompressibility of torus gluings

For a torus gluing of a compact carrier, the boundary splits into the labelled sides
`(i, false)` (left) and `(i, true)` (right), which are pairwise disjoint, exhaust the boundary,
are exchanged by the gluing involution and carry a fixed-point-free side pairing. The torus `i`
in the assembled space pulls back exactly to its two sides and is the image of each of them.
For a smooth assembly, the nonnegative and nonpositive halves of each seam are the glued right
and left collars and the open halves are disjoint. Injectivity on fundamental groups of a map
out of a path-connected space does not depend on the basepoint, so incompressibility of a
reconstruction may be checked at one basepoint or through the right-side parametrizations,
and no torus of a reconstruction of a simply connected manifold is incompressible.
-/

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Topology
universe u v w
variable {X : Type u} {X' : Type w} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

theorem fundamentalGroup_map_mulEquivOfPath (f : C(X, Y)) {x y : X} (γ : Path x y)
    (g : FundamentalGroup X x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map f.continuous)
        (FundamentalGroup.map f x g) := by
  have h : (FundamentalGroupoid.map f).mapIso ((Groupoid.isoEquivHom _ _).symm ⟦γ⟧) =
      (Groupoid.isoEquivHom _ _).symm ⟦γ.map f.continuous⟧ := Iso.ext rfl
  change (FundamentalGroupoid.map f).map (Iso.conj _ g) =
    Iso.conj _ ((FundamentalGroupoid.map f).map g)
  rw [Functor.map_conj, h]
  rfl

theorem injective_fundamentalGroup_map_iff_of_path (f : C(X, Y)) {x y : X} (γ : Path x y) :
    Function.Injective (FundamentalGroup.map f x) ↔
      Function.Injective (FundamentalGroup.map f y) := by
  have hc : ⇑(FundamentalGroup.map f y) ∘
      ⇑(FundamentalGroup.fundamentalGroupMulEquivOfPath γ) =
      ⇑(FundamentalGroup.fundamentalGroupMulEquivOfPath (γ.map f.continuous)) ∘
        ⇑(FundamentalGroup.map f x) :=
    funext (fundamentalGroup_map_mulEquivOfPath f γ)
  constructor
  · intro hx
    have h : Function.Injective (⇑(FundamentalGroup.map f y) ∘
        ⇑(FundamentalGroup.fundamentalGroupMulEquivOfPath γ)) := by
      rw [hc]
      exact (MulEquiv.injective _).comp hx
    exact h.of_comp_right (MulEquiv.surjective _)
  · intro hy
    have h : Function.Injective (⇑(FundamentalGroup.fundamentalGroupMulEquivOfPath
        (γ.map f.continuous)) ∘ ⇑(FundamentalGroup.map f x)) := by
      rw [← hc]
      exact hy.comp (MulEquiv.injective _)
    exact h.of_comp

theorem injective_fundamentalGroup_map_iff [PathConnectedSpace X] (f : C(X, Y)) (x y : X) :
    Function.Injective (FundamentalGroup.map f x) ↔
      Function.Injective (FundamentalGroup.map f y) :=
  injective_fundamentalGroup_map_iff_of_path f (PathConnectedSpace.somePath x y)

theorem forall_injective_fundamentalGroup_map_comp_iff (f : C(X', Y)) (e : X ≃ₜ X') :
    (∀ x, Function.Injective (FundamentalGroup.map (f.comp (e : C(X, X'))) x)) ↔
      ∀ y, Function.Injective (FundamentalGroup.map f y) := by
  constructor
  · intro h y
    have hf : f = (f.comp (e : C(X, X'))).comp (e.symm : C(X', X)) := by
      ext z
      simp
    rw [hf, fundamentalGroup_map_comp]
    exact (h _).comp (injective_fundamentalGroup_map_of_leftInverse (e.symm : C(X', X))
      (e : C(X, X')) e.apply_symm_apply y)
  · intro h x
    rw [fundamentalGroup_map_comp]
    exact (h _).comp (injective_fundamentalGroup_map_of_leftInverse (e : C(X, X'))
      (e.symm : C(X', X)) e.symm_apply_apply x)

end GC.Topology

namespace GC.Endpoint

theorem halfPoint_eq (h : EuclideanHalfSpace 1) (s : ℝ) (hs : 0 ≤ s) (e : s = h.val 0) :
    halfPoint s hs = h :=
  Subtype.ext (PiLp.ext fun j => by rw [Subsingleton.elim j 0]; exact e)

namespace TorusGluing
universe u
variable {C : CompactCarrier.{u}}

def side (G : TorusGluing C) (s : Fin G.count × Bool) : Set C.Carrier :=
  cond s.2 (G.gluing.right s.1) (G.gluing.left s.1)

def sidePairing (G : TorusGluing C) : GC.Topology.PairedSides (Fin G.count × Bool) where
  mate s := (s.1, !s.2)
  involutive s := by simp
  no_fixed s h := by simpa using congrArg Prod.snd h

theorem side_subset_block (G : TorusGluing C) (s : Fin G.count × Bool) :
    G.side s ⊆ G.gluing.block s.1 := by
  rcases s with ⟨i, _ | _⟩
  · exact Set.subset_union_left
  · exact Set.subset_union_right

theorem pairwise_disjoint_side (G : TorusGluing C) :
    Pairwise (fun s t => Disjoint (G.side s) (G.side t)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hst
  by_cases hij : i = j
  · subst hij
    have hab : a ≠ b := fun h => hst (by rw [h])
    rcases a with _ | _ <;> rcases b with _ | _
    · exact (hab rfl).elim
    · exact G.gluing.disjoint_left_right i
    · exact (G.gluing.disjoint_left_right i).symm
    · exact (hab rfl).elim
  · exact (G.gluing.disjoint_blocks i j hij).mono (G.side_subset_block (i, a))
      (G.side_subset_block (j, b))

theorem iUnion_side (G : TorusGluing C) : ⋃ s, G.side s = C.model.boundary C.Carrier := by
  rw [G.boundary_exhausted]
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun s => (G.side_subset_block s).trans (Set.subset_iUnion _ s.1)
  · refine Set.iUnion_subset fun i => Set.union_subset ?_ ?_
    · exact Set.subset_iUnion G.side (i, false)
    · exact Set.subset_iUnion G.side (i, true)

theorem flip_image_side (G : TorusGluing C) (s : Fin G.count × Bool) :
    G.gluing.flip s.1 '' G.side s = G.side (G.sidePairing.mate s) := by
  rcases s with ⟨i, _ | _⟩
  · change G.gluing.flip i '' G.gluing.left i = G.gluing.right i
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [G.gluing.flip_of_mem_left hx]
      exact (G.gluing.attaching i ⟨x, hx⟩).property
    · intro hy
      exact ⟨_, ((G.gluing.attaching i).symm ⟨y, hy⟩).property,
        G.gluing.flip_symm_attaching i ⟨y, hy⟩⟩
  · change G.gluing.flip i '' G.gluing.right i = G.gluing.left i
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [G.gluing.flip_of_mem_right hx]
      exact ((G.gluing.attaching i).symm ⟨x, hx⟩).property
    · intro hy
      exact ⟨_, (G.gluing.attaching i ⟨y, hy⟩).property,
        G.gluing.flip_attaching i ⟨y, hy⟩⟩

theorem flip_ne_self (G : TorusGluing C) {i : Fin G.count} {x : C.Carrier}
    (hx : x ∈ G.gluing.block i) : G.gluing.flip i x ≠ x := by
  obtain ⟨b, hb⟩ : ∃ b, x ∈ G.side (i, b) :=
    hx.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
  intro h
  have hm : G.gluing.flip i x ∈ G.side (G.sidePairing.mate (i, b)) :=
    G.flip_image_side (i, b) ▸ Set.mem_image_of_mem _ hb
  rw [h] at hm
  exact (G.pairwise_disjoint_side (G.sidePairing.no_fixed (i, b)).symm).le_bot ⟨hb, hm⟩

theorem quotientMap_preimage_range_torusMap (G : TorusGluing C) (i : Fin G.count) :
    G.quotientMap ⁻¹' Set.range (G.torusMap i) = G.gluing.block i := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact G.related_mem_block i (Or.inl (G.leftParam i t).property)
      ((G.quotientMap_eq_iff _ _).mp ht)
  · exact G.quotientMap_mem_range_torusMap

theorem range_torusMap_eq_image_block (G : TorusGluing C) (i : Fin G.count) :
    Set.range (G.torusMap i) = G.quotientMap '' G.gluing.block i := by
  have hs : Function.Surjective G.quotientMap := Quotient.mk''_surjective
  rw [← G.quotientMap_preimage_range_torusMap, Set.image_preimage_eq _ hs]

theorem range_torusMap_eq_image_left (G : TorusGluing C) (i : Fin G.count) :
    Set.range (G.torusMap i) = G.quotientMap '' G.gluing.left i := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, (G.leftParam i t).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(G.leftParam i).symm ⟨x, hx⟩, ?_⟩
    change G.quotientMap ((G.leftParam i) ((G.leftParam i).symm ⟨x, hx⟩)).val = _
    rw [Homeomorph.apply_symm_apply]

def rightTorusMap (G : TorusGluing C) (i : Fin G.count) : C(Torus, G.Assembled) :=
  G.quotientMap.comp ⟨fun t => (G.rightParam i t).val,
    continuous_subtype_val.comp (G.rightParam i).continuous⟩

theorem rightTorusMap_matching (G : TorusGluing C) (i : Fin G.count) (t : Torus) :
    G.rightTorusMap i (G.matching i t) = G.torusMap i t :=
  (G.matched_sides_equal i t).symm

theorem range_rightTorusMap (G : TorusGluing C) (i : Fin G.count) :
    Set.range (G.rightTorusMap i) = Set.range (G.torusMap i) := by
  ext q
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(G.matching i).symm u, ?_⟩
    rw [← G.rightTorusMap_matching, Diffeomorph.apply_symm_apply]
  · rintro ⟨t, rfl⟩
    exact ⟨G.matching i t, G.rightTorusMap_matching i t⟩

theorem range_torusMap_eq_image_right (G : TorusGluing C) (i : Fin G.count) :
    Set.range (G.torusMap i) = G.quotientMap '' G.gluing.right i := by
  rw [← G.range_rightTorusMap]
  ext q
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (G.rightParam i u).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(G.rightParam i).symm ⟨x, hx⟩, ?_⟩
    change G.quotientMap ((G.rightParam i) ((G.rightParam i).symm ⟨x, hx⟩)).val = _
    rw [Homeomorph.apply_symm_apply]

theorem range_torusMap_eq_image_side (G : TorusGluing C) (s : Fin G.count × Bool) :
    Set.range (G.torusMap s.1) = G.quotientMap '' G.side s := by
  rcases s with ⟨i, _ | _⟩
  · exact G.range_torusMap_eq_image_left i
  · exact G.range_torusMap_eq_image_right i

theorem range_leftCollar_zero (G : TorusGluing C) (i : Fin G.count) :
    Set.range (fun t => G.leftCollar i (t, halfZero)) = G.gluing.left i := by
  simp only [G.left_zero]
  rw [Set.range_comp' Subtype.val (G.leftParam i), Homeomorph.range_coe, Set.image_univ,
    Subtype.range_coe]

theorem range_rightCollar_zero (G : TorusGluing C) (i : Fin G.count) :
    Set.range (fun t => G.rightCollar i (t, halfZero)) = G.gluing.right i := by
  simp only [G.right_zero]
  rw [Set.range_comp' Subtype.val (G.rightParam i), Homeomorph.range_coe, Set.image_univ,
    Subtype.range_coe]

end TorusGluing

namespace SmoothAssembly
universe u
variable {C : CompactCarrier.{u}} {G : TorusGluing C}

def rightTorusInPrime (A : SmoothAssembly G) {P : ConnectedClosedOrientedManifold.{u} 3}
    (r : A.Reconstruction P) (i : Fin G.count) : C(Torus, P.Carrier) :=
  (show C(G.Assembled, P.Carrier) from ⟨r.val, r.val.continuous⟩).comp (G.rightTorusMap i)

theorem incompressible_iff_basepoint (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (x₀ : Torus) :
    A.Incompressible r ↔
      ∀ i, Function.Injective (FundamentalGroup.map (A.torusInPrime r i) x₀) :=
  ⟨fun h i => h i x₀, fun h i x =>
    (GC.Topology.injective_fundamentalGroup_map_iff _ x₀ x).mp (h i)⟩

theorem torusInPrime_eq_comp_matching (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    A.torusInPrime r i =
      (A.rightTorusInPrime r i).comp ((G.matching i).toHomeomorph : C(Torus, Torus)) :=
  ContinuousMap.ext fun t => congrArg r.val (G.rightTorusMap_matching i t).symm

theorem incompressible_iff_right (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) :
    A.Incompressible r ↔
      ∀ i x, Function.Injective (FundamentalGroup.map (A.rightTorusInPrime r i) x) := by
  refine forall_congr' fun i => ?_
  rw [A.torusInPrime_eq_comp_matching r i]
  exact GC.Topology.forall_injective_fundamentalGroup_map_comp_iff _ _

theorem not_incompressible_of_simplyConnected (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} [SimplyConnectedSpace P.Carrier]
    (r : A.Reconstruction P) (i : Fin G.count) : ¬ A.Incompressible r := by
  intro h
  obtain ⟨p, hp⟩ := GC.Topology.torus_has_nontrivial_loop
  apply hp
  apply h i (1, 1)
  have hs : Subsingleton (Path.Homotopic.Quotient (A.torusInPrime r i (1, 1))
      (A.torusInPrime r i (1, 1))) := inferInstance
  exact hs.elim _ _

theorem range_torusInPrime (A : SmoothAssembly G) {P : ConnectedClosedOrientedManifold.{u} 3}
    (r : A.Reconstruction P) (i : Fin G.count) :
    Set.range (A.torusInPrime r i) = r.val '' Set.range (G.torusMap i) := by
  rw [torusInPrime, ContinuousMap.coe_comp, Set.range_comp]
  rfl

theorem torusInPrime_pairwise_disjoint (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) :
    Pairwise (fun i j => Disjoint (Set.range (A.torusInPrime r i))
      (Set.range (A.torusInPrime r j))) := by
  intro i j hij
  rw [A.range_torusInPrime, A.range_torusInPrime]
  exact (Set.disjoint_image_iff r.val.injective).mpr (G.torusMap_pairwise_disjoint hij)

theorem seam_zero_eq_right (A : SmoothAssembly G) (i : Fin G.count) (t : Torus) :
    A.seam i (t, 0) = G.rightTorusMap i (G.matching i t) := by
  rw [A.seam_zero, G.rightTorusMap_matching]

theorem seam_image_nonneg (A : SmoothAssembly G) (i : Fin G.count) :
    A.seam i '' {p | 0 ≤ p.2 ∧ p.2 < 1} =
      G.quotientMap '' (G.rightCollar i '' halfCollarSource) := by
  ext q
  constructor
  · rintro ⟨⟨t, s⟩, ⟨hs, hs1⟩, rfl⟩
    exact ⟨_, ⟨(G.matching i t, halfPoint s hs), hs1, rfl⟩,
      (A.seam_positive i t s hs hs1).symm⟩
  · rintro ⟨_, ⟨⟨u, h⟩, hmem, rfl⟩, rfl⟩
    refine ⟨((G.matching i).symm u, h.val 0), ⟨h.property, hmem⟩, ?_⟩
    rw [A.seam_positive i _ _ h.property hmem, Diffeomorph.apply_symm_apply,
      halfPoint_eq h _ _ rfl]

theorem seam_image_nonpos (A : SmoothAssembly G) (i : Fin G.count) :
    A.seam i '' {p | -1 < p.2 ∧ p.2 ≤ 0} =
      G.quotientMap '' (G.leftCollar i '' halfCollarSource) := by
  ext q
  constructor
  · rintro ⟨⟨t, s⟩, ⟨hs1, hs⟩, rfl⟩
    refine ⟨_, ⟨(t, halfPoint (-s) (neg_nonneg.mpr hs)), ?_, rfl⟩,
      (A.seam_negative i t s hs hs1).symm⟩
    change -s < 1
    linarith
  · rintro ⟨_, ⟨⟨u, h⟩, hmem, rfl⟩, rfl⟩
    have hmem' : h.val 0 < 1 := hmem
    have hs : -h.val 0 ≤ 0 := neg_nonpos.mpr h.property
    refine ⟨(u, -h.val 0), ⟨by linarith, hs⟩, ?_⟩
    rw [A.seam_negative i _ _ hs (by linarith), halfPoint_eq h _ _ (neg_neg _)]

theorem disjoint_seam_pos_neg (A : SmoothAssembly G) (i : Fin G.count) :
    Disjoint (A.seam i '' {p | 0 < p.2 ∧ p.2 < 1})
      (A.seam i '' {p | -1 < p.2 ∧ p.2 < 0}) := by
  let := A.charts
  rw [Set.disjoint_left]
  rintro q ⟨p, ⟨hp0, hp1⟩, rfl⟩ ⟨p', ⟨hp0', hp1'⟩, hpp⟩
  have hs : p ∈ (A.seam i).source := by
    rw [A.seam_source]
    exact ⟨by linarith, hp1⟩
  have hs' : p' ∈ (A.seam i).source := by
    rw [A.seam_source]
    exact ⟨hp0', by linarith⟩
  have he := congrArg Prod.snd ((A.seam i).toPartialEquiv.injOn hs' hs hpp)
  linarith

end SmoothAssembly
end GC.Endpoint
