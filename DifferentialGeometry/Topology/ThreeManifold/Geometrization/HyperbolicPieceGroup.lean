import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeGraph

/-!
# Groups of torus-presentation pieces: interior comparison and peripheral tori

Tier T1 of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §1).

* A collar point of positive height is an interior point when the collars exhaust the boundary
  (`BoundaryTori.isInteriorPoint_collar`).
* For a piece of a torus presentation, freely indecomposable π₁ of the piece interior at one point
  gives freely indecomposable π₁ of the piece at every point: P4's collar push makes the inclusion
  of the interior π₁-bijective (`bijective_pieceInteriorToPiece`), and the piece is path connected
  (`freelyIndecomposable_piece_of_interior`).
* A π₁-injective port makes π₁ of the piece non-cyclic at every point, since `ℤ × ℤ` is not cyclic
  (`not_isCyclic_piece_of_port`). Hence `indecomposableNoncyclic_piece_of_interior`.
* The collar torus at height `s ∈ (0, 1)` lies in the piece interior
  (`interiorCollarTorus`), and it is π₁-injective there when the port is: composed with the
  inclusion it is homotopic to the boundary torus by lowering the height
  (`injective_interiorCollarTorus`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Set Topology
open scoped ContinuousMap unitInterval Manifold

universe u

namespace GC.GraphManifold.BoundaryTori

variable {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n)

theorem isInteriorPoint_collar (hb : C.model.boundary C.Carrier = B.image) (m : Fin n)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) (hpos : 0 < p.2.val 0) :
    C.model.IsInteriorPoint (B.collar m p) := by
  apply (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mpr
  intro hboundary
  have himage : B.collar m p ∈ B.image := hb ▸ hboundary
  obtain ⟨k, a, heq⟩ := mem_iUnion.mp himage
  change B.collar k (a, halfZero) = B.collar m p at heq
  have hk : (a, halfZero) ∈ (B.collar k).source := by
    rw [B.source_eq k]
    exact zero_mem_halfCollarSource a
  have hp' : p ∈ (B.collar m).source := by
    rw [B.source_eq m]
    exact hp
  have hkm : k = m := by
    by_contra hne
    exact (B.disjoint hne).le_bot
      ⟨heq ▸ (B.collar k).map_source' hk, (B.collar m).map_source' hp'⟩
  subst hkm
  have he : (a, halfZero) = p := (B.collar k).toOpenPartialHomeomorph.injOn hk hp' heq
  have h0 : p.2.val 0 = 0 := by
    rw [← he]
    rfl
  linarith

end GC.GraphManifold.BoundaryTori

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (i : Fin G.components.count)

theorem pathConnectedSpace_piece' : PathConnectedSpace (G.components.piece i) := by
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := G.cutCarrier.Carrier)
    G.cutCarrier.model
  have hc : IsConnected (G.components.piece i : Set G.cutCarrier.Carrier) :=
    isConnected_iff_connectedSpace.mpr (G.components.connected i)
  exact isPathConnected_iff_pathConnectedSpace.mp
    ((G.components.piece i).isOpen.isConnected_iff_isPathConnected.mp hc)

theorem freelyIndecomposable_piece_of_interior
    (y : G.cutCarrier.pieceInterior (G.components.piece i))
    (h : GC.Group.FreelyIndecomposable
      (FundamentalGroup (G.cutCarrier.pieceInterior (G.components.piece i)) y))
    (x : G.components.piece i) :
    GC.Group.FreelyIndecomposable (FundamentalGroup (G.components.piece i) x) := by
  have := G.pathConnectedSpace_piece' i
  have hy : GC.Group.FreelyIndecomposable
      (FundamentalGroup (G.components.piece i) (G.pieceInteriorToPiece i y)) :=
    h.of_mulEquiv (MulEquiv.ofBijective _ (G.bijective_pieceInteriorToPiece i y))
  exact hy.of_mulEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ x)

theorem not_isCyclic_piece_of_port (hports : (G.pieceBoundaryTori i).incompressible)
    (m : Fin (Fintype.card (G.OwnedSide i))) (x : G.components.piece i) :
    ¬ IsCyclic (FundamentalGroup (G.components.piece i) x) := by
  have := G.pathConnectedSpace_piece' i
  let t : Torus := (1, 1)
  have hnc : ¬ IsCyclic (FundamentalGroup (G.components.piece i)
      ((G.pieceBoundaryTori i).boundaryMap m t)) :=
    not_isCyclic_of_injective _ (hports m t) (indecomposableNoncyclic_torus t).2
  intro hc
  exact hnc ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x _).isCyclic.mp hc)

theorem indecomposableNoncyclic_piece_of_interior
    (hports : (G.pieceBoundaryTori i).incompressible)
    (hn : 0 < Fintype.card (G.OwnedSide i))
    (y : G.cutCarrier.pieceInterior (G.components.piece i))
    (h : GC.Group.FreelyIndecomposable
      (FundamentalGroup (G.cutCarrier.pieceInterior (G.components.piece i)) y))
    (x : G.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (G.components.piece i) x) :=
  ⟨G.freelyIndecomposable_piece_of_interior i y h x,
    G.not_isCyclic_piece_of_port i hports ⟨0, hn⟩ x⟩

def collarHeight (s : ℝ) (hs : 0 ≤ s) : EuclideanHalfSpace 1 :=
  halfSpaceOneHomeomorph.symm ⟨s, hs⟩

theorem collarHeight_coord (s : ℝ) (hs : 0 ≤ s) : (collarHeight s hs).val 0 = s :=
  congrArg Subtype.val (halfSpaceOneHomeomorph.apply_symm_apply ⟨s, hs⟩)

theorem collarHeight_zero : collarHeight 0 le_rfl = halfZero := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change (collarHeight 0 le_rfl).val 0 = (halfZero : EuclideanHalfSpace 1).val 0
  rw [collarHeight_coord]
  rfl

variable {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)

include hs1 in
theorem collarHeight_mem_source (t : Torus) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    (t, collarHeight r hr) ∈ halfCollarSource := by
  change (collarHeight r hr).val 0 < 1
  rw [collarHeight_coord]
  linarith

include hs0 hs1 in
theorem collarTorus_mem_pieceInterior (m : Fin (Fintype.card (G.OwnedSide i))) (t : Torus) :
    ((G.pieceBoundaryTori i).collar m (t, collarHeight s hs0.le)).val ∈
      G.cutCarrier.pieceInterior (G.components.piece i) := by
  refine ⟨((G.pieceBoundaryTori i).collar m (t, collarHeight s hs0.le)).property, ?_⟩
  apply (G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val
    (u := G.components.piece i)).mp
  apply (G.pieceBoundaryTori i).isInteriorPoint_collar (G.pieceBoundaryTori_image i) m
    (collarHeight_mem_source hs1 t hs0.le le_rfl)
  change 0 < (collarHeight s hs0.le).val 0
  rw [collarHeight_coord]
  exact hs0

theorem continuous_collarTorus (m : Fin (Fintype.card (G.OwnedSide i))) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r < 1) :
    Continuous fun t : Torus => (G.pieceBoundaryTori i).collar m (t, collarHeight r hr) := by
  apply ((G.pieceBoundaryTori i).collar m).toOpenPartialHomeomorph.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const)
  intro t
  change _ ∈ ((G.pieceBoundaryTori i).collar m).source
  rw [(G.pieceBoundaryTori i).source_eq m]
  exact collarHeight_mem_source hr1 t hr le_rfl

def interiorCollarTorus (m : Fin (Fintype.card (G.OwnedSide i))) :
    C(Torus, G.cutCarrier.pieceInterior (G.components.piece i)) :=
  ⟨fun t => ⟨_, G.collarTorus_mem_pieceInterior i hs0 hs1 m t⟩,
    (continuous_subtype_val.comp (G.continuous_collarTorus i m hs0.le hs1)).subtype_mk _⟩

theorem interiorCollarTorus_apply (m : Fin (Fintype.card (G.OwnedSide i))) (t : Torus) :
    (G.interiorCollarTorus i hs0 hs1 m t : G.cutCarrier.Carrier) =
      ((G.pieceBoundaryTori i).collar m (t, collarHeight s hs0.le)).val :=
  rfl

def collarLowering (m : Fin (Fintype.card (G.OwnedSide i))) :
    ((G.pieceInteriorToPiece i).comp (G.interiorCollarTorus i hs0 hs1 m)).Homotopy
      ((G.pieceBoundaryTori i).boundaryMap m) where
  toFun u := (G.pieceBoundaryTori i).collar m
    (u.2, collarHeight (s * (1 - (u.1 : ℝ)))
      (mul_nonneg hs0.le (sub_nonneg.mpr (unitInterval.le_one u.1))))
  continuous_toFun := by
    apply ((G.pieceBoundaryTori i).collar m).toOpenPartialHomeomorph.continuousOn.comp_continuous
    · refine continuous_snd.prodMk ?_
      exact halfSpaceOneHomeomorph.symm.continuous.comp ((continuous_const.mul
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).subtype_mk _)
    · intro u
      change _ ∈ ((G.pieceBoundaryTori i).collar m).source
      rw [(G.pieceBoundaryTori i).source_eq m]
      refine collarHeight_mem_source hs1 u.2 _ ?_
      have h1 : (1 : ℝ) - u.1 ≤ 1 := by linarith [unitInterval.nonneg u.1]
      nlinarith
  map_zero_left t := by
    change (G.pieceBoundaryTori i).collar m (t, collarHeight (s * (1 - 0)) _) =
      (G.pieceBoundaryTori i).collar m (t, collarHeight s hs0.le)
    congr 2
    apply halfSpaceOneHomeomorph.injective
    apply Subtype.ext
    change (collarHeight (s * (1 - 0)) _).val 0 = (collarHeight s hs0.le).val 0
    rw [collarHeight_coord, collarHeight_coord]
    ring
  map_one_left t := by
    change (G.pieceBoundaryTori i).collar m (t, collarHeight (s * (1 - 1)) _) =
      (G.pieceBoundaryTori i).collar m (t, halfZero)
    congr 2
    rw [← collarHeight_zero]
    apply halfSpaceOneHomeomorph.injective
    apply Subtype.ext
    change (collarHeight (s * (1 - 1)) _).val 0 = (collarHeight 0 le_rfl).val 0
    rw [collarHeight_coord, collarHeight_coord]
    ring

theorem injective_interiorCollarTorus (hports : (G.pieceBoundaryTori i).incompressible)
    (m : Fin (Fintype.card (G.OwnedSide i))) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.interiorCollarTorus i hs0 hs1 m) t) :=
  GC.Topology.injective_inner_of_composite _ (G.pieceInteriorToPiece i) t
    (injective_fundamentalGroup_map_of_homotopy (G.collarLowering i hs0 hs1 m) t (hports m t))

end GC.Seifert.TorusPresentation
