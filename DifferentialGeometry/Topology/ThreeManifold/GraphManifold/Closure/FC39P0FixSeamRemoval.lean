import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Faces

/-!
# FC39 producer, gate 1 (review 49, level-3 interface): removal of the relative seam collars

External review 49 asks for "removal of the relative collar of a shared face" as a CONCLUSION of
the existing contract fields, in GENERAL form (the S³ instance is
`sphereSharedSeam_slimSide_removed` / `sphereSharedSeam_target_disjoint_M2`,
`FC39P0SphereSlimRegions.lean`). For every seam of ANY joint link `SeamFacesLink`:

* `SeamFacesLink.sphereSeam_target_disjoint_M2` / `torusSeam_target_disjoint_M2` — the WHOLE seam
  collar misses `M₂`;
* `SeamFacesLink.sphere_slimSide_removed` / `torus_slimSide_removed` (and the `exists_` forms with
  the side of `sphere_owner` / `torus_owner`) — the closed slim half of the collar lies in the
  relative interior `int_{M₁} S` (the relative inward collar is removed with the shared face);
* `SeamFacesLink.sphere_neighbourSide_not_mem_M1` / `torus_neighbourSide_not_mem_M1` — the open
  neighbour half lies in `int_W (Z ∪ C)`, so outside `M₁`.

Inputs (all existing fields): the seam sides (`SeamLayer.sphereSide_neg/pos`,
`torusSide_neg/pos`), `SeamFacesLink.sphere_slim` / `torus_slim` (the zero slice is the shared
slim end), `torusSide_eq`, `sphere_owner` / `torus_owner`, `VertexModelLink.vertex_eq` with
`FC39RowsV2.rowVertex_image`, `JunctionsV2.shared_removed` and `JunctionsV2.interiors_disjoint`.
The one topological step is `JunctionsV2.slim_interior_subset_regionM1`: the interior of a slim
piece meets no interior point of the finite union of closed zero / cusp images
(`eq_empty_of_subset_iUnion_closed_FIX2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## Topological steps -/

section Topological

variable {X : Type*} [TopologicalSpace X]

/-- An open set covered by a closed set `A` and a set `T`, disjoint from the interior of `T`, lies
in `A`. -/
theorem subset_of_subset_union_closed_FIX2 {U A T : Set X} (hU : IsOpen U) (hA : IsClosed A)
    (hsub : U ⊆ A ∪ T) (hT : Disjoint U (interior T)) : U ⊆ A := by
  intro x hx
  by_contra hxA
  have hV : U \ A ⊆ interior T :=
    interior_maximal (fun y hy => (hsub hy.1).resolve_left hy.2) (hU.sdiff hA)
  exact Set.disjoint_left.1 hT hx (hV ⟨hx, hxA⟩)

/-- An open set inside a set and disjoint from its interior is empty. -/
theorem eq_empty_of_subset_disjoint_interior_FIX2 {U A : Set X} (hU : IsOpen U) (hsub : U ⊆ A)
    (hA : Disjoint U (interior A)) : U = ∅ :=
  subset_empty_iff.1 fun _ hx => Set.disjoint_left.1 hA hx (interior_maximal hsub hU hx)

/-- An open set covered by finitely many closed sets and disjoint from all their interiors is
empty (finite form of the Baire argument, by induction). -/
theorem eq_empty_of_subset_biUnion_closed_FIX2 {ι : Type*} (F : ι → Set X)
    (hF : ∀ i, IsClosed (F i)) (s : Finset ι) :
    ∀ U : Set X, IsOpen U → U ⊆ ⋃ i ∈ s, F i → (∀ i ∈ s, Disjoint U (interior (F i))) →
      U = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U _ hsub _
    simpa using hsub
  | insert a s ha ih =>
    intro U hU hsub hdis
    have h1 : U \ F a = ∅ := by
      refine ih (U \ F a) (hU.sdiff (hF a)) ?_ ?_
      · intro x hx
        have hx' := hsub hx.1
        rw [Finset.set_biUnion_insert] at hx'
        exact hx'.resolve_left hx.2
      · intro i hi
        exact (hdis i (Finset.mem_insert_of_mem hi)).mono_left sdiff_subset
    have h2 : U ⊆ F a := by
      intro x hx
      by_contra hxa
      have hmem : x ∈ U \ F a := ⟨hx, hxa⟩
      rw [h1] at hmem
      exact hmem
    exact eq_empty_of_subset_disjoint_interior_FIX2 hU h2 (hdis a (Finset.mem_insert_self a s))

/-- The same over a finite index type. -/
theorem eq_empty_of_subset_iUnion_closed_FIX2 {ι : Type*} [Finite ι] (F : ι → Set X)
    (hF : ∀ i, IsClosed (F i)) {U : Set X} (hU : IsOpen U) (hsub : U ⊆ ⋃ i, F i)
    (hdis : ∀ i, Disjoint U (interior (F i))) : U = ∅ := by
  classical
  have := Fintype.ofFinite ι
  refine eq_empty_of_subset_biUnion_closed_FIX2 F hF Finset.univ U hU ?_ fun i _ => hdis i
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hsub hx)
  exact mem_iUnion₂.2 ⟨i, Finset.mem_univ i, hi⟩

/-- Two closed sets and one more set: an open set covered by them and disjoint from their three
interiors is empty. -/
theorem eq_empty_of_subset_union_three_FIX2 {U A B G : Set X} (hU : IsOpen U) (hA : IsClosed A)
    (hB : IsClosed B) (hsub : U ⊆ A ∪ B ∪ G) (hdA : Disjoint U (interior A))
    (hdB : Disjoint U (interior B)) (hdG : Disjoint U (interior G)) : U = ∅ := by
  have h1 : U ⊆ A ∪ B := subset_of_subset_union_closed_FIX2 hU (hA.union hB) hsub hdG
  have h2 : U ⊆ A := subset_of_subset_union_closed_FIX2 hU hA h1 hdB
  exact eq_empty_of_subset_disjoint_interior_FIX2 hU h2 hdA

/-- Points of `A` in the interior of `S` lie in the interior of `S` relative to `A`. -/
theorem interior_inter_subset_relInt_FIX2 {A S : Set X} : interior S ∩ A ⊆ relInt A S := by
  rintro x ⟨hxS, hxA⟩
  refine ⟨⟨x, hxA⟩, ?_, rfl⟩
  have hO : IsOpen ((Subtype.val : A → X) ⁻¹' interior S) :=
    isOpen_interior.preimage continuous_subtype_val
  exact interior_maximal (preimage_mono interior_subset) hO hxS

end Topological

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## Row interiors and `M₂` -/

/-- No interior point of a row piece lies in `M₂`: a zero / cusp interior point is not in `M₁`, a
slim interior point of `M₁` lies in `int_{M₁} S`. -/
theorem interior_rowSet_disjoint_regionM2 {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) (a : S.RowIndex) :
    Disjoint (interior (S.rowSet a)) (regionM2 S) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨hx1, hx2⟩
  rcases a with i | b | j
  · exact hx1 (interior_mono ((subset_iUnion (fun i => range (Z.piece i).map) i).trans
      subset_union_left) hx)
  · exact hx1 (interior_mono ((subset_iUnion (fun b => range (C.piece b).map) b).trans
      subset_union_right) hx)
  · exact hx2 (interior_inter_subset_relInt_FIX2 ⟨interior_mono
      (subset_iUnion (fun j => range (S.piece j).map) j) hx, hx1⟩)

/-- **The interior of a slim piece lies in `M₁`** (`JunctionsV2.interiors_disjoint` and the
finite closed cover by the zero and cusp images). -/
theorem JunctionsV2.slim_interior_subset_regionM1 {Z : ZeroDomains W} {C : CuspCores W E}
    {S : SlimPiecesV2 W Z C} {P : EdgeBundle W} {R : CircleBundle W}
    (J : JunctionsV2 W E Z C S P R) (j : Fin S.count) :
    interior (range (S.piece j).map) ⊆ regionM1 Z C := by
  intro x hx hxZC
  let Fam : Fin Z.count ⊕ Fin n → Set W.Carrier :=
    Sum.elim (fun i => range (Z.piece i).map) (fun b => range (C.piece b).map)
  have hcl : ∀ a, IsClosed (Fam a) := by
    rintro (i | b)
    · exact (Z.piece i).isClosed_range
    · exact (C.piece b).isClosed_range
  have hU : interior (range (S.piece j).map) ∩
      interior ((⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map) = ∅ := by
    refine eq_empty_of_subset_iUnion_closed_FIX2 Fam hcl
      (isOpen_interior.inter isOpen_interior) ?_ ?_
    · intro y hy
      rcases interior_subset hy.2 with hy' | hy'
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hy'
        exact mem_iUnion.2 ⟨Sum.inl i, hi⟩
      · obtain ⟨b, hb⟩ := mem_iUnion.1 hy'
        exact mem_iUnion.2 ⟨Sum.inr b, hb⟩
    · rintro (i | b)
      · have hd := J.interiors_disjoint
          (show (Sum.inl (Sum.inr (Sum.inr j)) : S.RowIndex ⊕ Bool) ≠ Sum.inl (Sum.inl i) by simp)
        exact hd.mono_left inter_subset_left
      · have hd := J.interiors_disjoint
          (show (Sum.inl (Sum.inr (Sum.inr j)) : S.RowIndex ⊕ Bool) ≠
            Sum.inl (Sum.inr (Sum.inl b)) by simp)
        exact hd.mono_left inter_subset_left
  have hmem : x ∈ interior (range (S.piece j).map) ∩
      interior ((⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map) := ⟨hx, hxZC⟩
  rw [hU] at hmem
  exact hmem

/-- The interior of a slim piece lies in `int_{M₁} S`. -/
theorem JunctionsV2.slim_interior_subset_relInt {Z : ZeroDomains W} {C : CuspCores W E}
    {S : SlimPiecesV2 W Z C} {P : EdgeBundle W} {R : CircleBundle W}
    (J : JunctionsV2 W E Z C S P R) (j : Fin S.count) :
    interior (range (S.piece j).map) ⊆ relInt (regionM1 Z C) S.union := fun _ hx =>
  interior_inter_subset_relInt_FIX2
    ⟨interior_mono (subset_iUnion (fun j => range (S.piece j).map) j) hx,
      J.slim_interior_subset_regionM1 j hx⟩

/-! ## The two halves of a signed seam collar -/

/-- The closed half of the signed collar on side `b` (`true`: `s ∈ (-1, 0]`, the side of
`SeamLayer.sphereSide_neg`; `false`: `s ∈ [0, 1)`). -/
def seamSideInterval : Bool → Set ℝ
  | true => Ioc (-1) 0
  | false => Ico 0 1

/-- The open half of the signed collar on side `b` (zero slice removed). -/
def seamOpenSideInterval : Bool → Set ℝ
  | true => Ioo (-1) 0
  | false => Ioo 0 1

theorem isOpen_seamOpenSideInterval (b : Bool) : IsOpen (seamOpenSideInterval b) := by
  cases b
  · exact isOpen_Ioo
  · exact isOpen_Ioo

theorem seamOpenSideInterval_subset (b : Bool) : seamOpenSideInterval b ⊆ seamSideInterval b := by
  cases b
  · exact Ioo_subset_Ico_self
  · exact Ioo_subset_Ioc_self

theorem seamOpenSideInterval_subset_Ioo (b : Bool) :
    seamOpenSideInterval b ⊆ Ioo (-1 : ℝ) 1 := by
  cases b
  · exact Ioo_subset_Ioo (by norm_num) le_rfl
  · exact Ioo_subset_Ioo le_rfl (by norm_num)

theorem mem_seamOpenSideInterval_of_ne {b : Bool} {s : ℝ} (hs : s ∈ seamSideInterval b)
    (h0 : s ≠ 0) : s ∈ seamOpenSideInterval b := by
  cases b
  · obtain ⟨h1, h2⟩ := hs
    exact ⟨lt_of_le_of_ne h1 (Ne.symm h0), h2⟩
  · obtain ⟨h1, h2⟩ := hs
    exact ⟨h1, lt_of_le_of_ne h2 h0⟩

/-- A point of a sphere-seam collar target is the collar image of a point with `s ∈ (-1, 1)`. -/
theorem sphereSeam_exists_of_mem_target_FIX2 (σ : SphereSeam W) {x : W.Carrier}
    (hx : x ∈ σ.collar.target) : ∃ z s, -1 < s ∧ s < 1 ∧ σ.collar (z, s) = x := by
  have hp := σ.collar.map_target hx
  rw [σ.source_eq, sphereSignedCollarSource] at hp
  exact ⟨_, _, hp.2.1, hp.2.2, σ.collar.right_inv hx⟩

/-- A point of a torus-seam collar target is the collar image of a point with `s ∈ (-1, 1)`. -/
theorem torusSeam_exists_of_mem_target_FIX2 (σ : TorusSeam W) {x : W.Carrier}
    (hx : x ∈ σ.collar.target) : ∃ t s, -1 < s ∧ s < 1 ∧ σ.collar (t, s) = x := by
  have hp := σ.collar.map_target hx
  rw [σ.source_eq, signedCollarSource] at hp
  exact ⟨_, _, hp.1, hp.2, σ.collar.right_inv hx⟩

/-- The open half of a sphere-seam collar is open. -/
theorem sphereSeam_isOpen_side_FIX2 (σ : SphereSeam W) (b : Bool) :
    IsOpen (σ.collar '' (univ ×ˢ seamOpenSideInterval b)) := by
  refine σ.collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod (isOpen_seamOpenSideInterval b)) ?_
  intro p hp
  change p ∈ σ.collar.source
  rw [σ.source_eq, sphereSignedCollarSource]
  exact ⟨mem_univ _, seamOpenSideInterval_subset_Ioo b hp.2⟩

/-- The open half of a torus-seam collar is open. -/
theorem torusSeam_isOpen_side_FIX2 (σ : TorusSeam W) (b : Bool) :
    IsOpen (σ.collar '' (univ ×ˢ seamOpenSideInterval b)) := by
  refine σ.collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod (isOpen_seamOpenSideInterval b)) ?_
  intro p hp
  change p ∈ σ.collar.source
  rw [σ.source_eq, signedCollarSource]
  exact seamOpenSideInterval_subset_Ioo b hp.2

/-- The closed half `b` of a sphere-seam collar lies in the side vertex `b`. -/
theorem SeamLayer.sphereSeam_mem_side {V : VertexLayer W} {circ : CircleRegion W}
    (S : SeamLayer W V circ) (c : Fin S.sphereSeamCount) (b : Bool) (z : ClosureSphere.{u})
    {s : ℝ} (hs : s ∈ seamSideInterval b) :
    (S.sphereSeam c).collar (z, s) ∈ (V.vertex (S.sphereSide c b)).image := by
  cases b
  · obtain ⟨h1, h2⟩ := hs
    exact S.sphereSide_pos c z s h1 h2
  · obtain ⟨h1, h2⟩ := hs
    exact S.sphereSide_neg c z s h2 h1

/-- The open half `b` of a sphere-seam collar lies in the INTERIOR of the side vertex `b`. -/
theorem SeamLayer.sphereSeam_mem_interior_side {V : VertexLayer W} {circ : CircleRegion W}
    (S : SeamLayer W V circ) (c : Fin S.sphereSeamCount) (b : Bool) (z : ClosureSphere.{u})
    {s : ℝ} (hs : s ∈ seamOpenSideInterval b) :
    (S.sphereSeam c).collar (z, s) ∈ interior (V.vertex (S.sphereSide c b)).image := by
  refine interior_maximal ?_ (sphereSeam_isOpen_side_FIX2 (S.sphereSeam c) b)
    ⟨(z, s), ⟨mem_univ _, hs⟩, rfl⟩
  rintro _ ⟨⟨z', s'⟩, ⟨-, hs'⟩, rfl⟩
  exact S.sphereSeam_mem_side c b z' (seamOpenSideInterval_subset b hs')

/-- The image of a vertex is the set of its row. -/
theorem VertexModelLink.image_eq_rowSet {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    (VL : VertexModelLink Rw V) (k : Fin V.vertexCount) :
    (V.vertex k).image = Rw.slim.rowSet (VL.index k) := by
  rw [VL.vertex_eq k, Rw.rowVertex_image]

/-- The row of a neighbour face is a zero domain or a cusp core. -/
theorem FC39RowsV2.rowSet_neighbourIndex_subset (Rw : FC39RowsV2 W E)
    (G : NeighbourFace Rw.zero Rw.cusp) :
    Rw.slim.rowSet (Rw.neighbourIndex G) ⊆
      (⋃ i, range (Rw.zero.piece i).map) ∪ ⋃ b, range (Rw.cusp.piece b).map := by
  rcases G with G | G
  · exact (subset_iUnion (fun i => range (Rw.zero.piece i).map) G.1).trans subset_union_left
  · exact (subset_iUnion (fun b => range (Rw.cusp.piece b).map) G.1).trans subset_union_right

/-! ## Sphere seams -/

section Seams

variable {Rw : FC39RowsV2 W E} {V : VertexLayer W} {VL : VertexModelLink Rw V}
  {O : PortLayer W E V} {circ : CircleRegion W} {S : SeamLayer W V circ}
  {F : FaceLayer W E V S O} {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- The zero slice of a sphere seam (the shared face) lies in `int_{M₁} S`. -/
theorem SeamFacesLink.sphereSlice_mem_relInt (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.sphereSeamCount) (z : ClosureSphere.{u}) :
    (S.sphereSeam c).collar (z, 0) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  have h : (S.sphereSeam c).collar (z, 0) ∈ Rw.sharedSet (L.sphereEquiv c).1 := by
    rw [← L.sphere_slim c]
    exact ⟨z, rfl⟩
  exact Rw.junctions.shared_removed _ h

/-- **The whole collar of every sphere seam misses `M₂`** (general form of
`sphereSharedSeam_target_disjoint_M2`). -/
theorem SeamFacesLink.sphereSeam_target_disjoint_M2 (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.sphereSeamCount) :
    Disjoint (S.sphereSeam c).collar.target (regionM2 Rw.slim) := by
  rw [Set.disjoint_left]
  intro x hx hxM
  obtain ⟨z, s, hs1, hs2, rfl⟩ := sphereSeam_exists_of_mem_target_FIX2 (S.sphereSeam c) hx
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hI := S.sphereSeam_mem_interior_side c true z
      (show s ∈ seamOpenSideInterval true from ⟨hs1, hs⟩)
    rw [VL.image_eq_rowSet] at hI
    exact Set.disjoint_left.1 (interior_rowSet_disjoint_regionM2 Rw.slim _) hI hxM
  · exact hxM.2 (L.sphereSlice_mem_relInt c z)
  · have hI := S.sphereSeam_mem_interior_side c false z
      (show s ∈ seamOpenSideInterval false from ⟨hs, hs2⟩)
    rw [VL.image_eq_rowSet] at hI
    exact Set.disjoint_left.1 (interior_rowSet_disjoint_regionM2 Rw.slim _) hI hxM

/-- **The slim half of a sphere seam collar lies in `int_{M₁} S`** (general form of
`sphereSharedSeam_slimSide_removed`): on the side `b` whose vertex is the slim owner of the shared
face, the closed half collar is removed with the face. -/
theorem SeamFacesLink.sphere_slimSide_removed (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.sphereSeamCount) {b : Bool}
    (hb : VL.index (S.sphereSide c b) = Rw.slimIndex (L.sphereEquiv c).1)
    (z : ClosureSphere.{u}) {s : ℝ} (hs : s ∈ seamSideInterval b) :
    (S.sphereSeam c).collar (z, s) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  by_cases h0 : s = 0
  · subst h0
    exact L.sphereSlice_mem_relInt c z
  · have hI := S.sphereSeam_mem_interior_side c b z (mem_seamOpenSideInterval_of_ne hs h0)
    rw [VL.image_eq_rowSet, hb] at hI
    exact Rw.junctions.slim_interior_subset_relInt (L.sphereEquiv c).1.1.1.1 hI

/-- The slim side exists (`sphere_owner`) and its closed half collar is removed. -/
theorem SeamFacesLink.exists_sphere_slimSide_removed (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.sphereSeamCount) :
    ∃ b, VL.index (S.sphereSide c b) = Rw.slimIndex (L.sphereEquiv c).1 ∧
      ∀ (z : ClosureSphere.{u}) (s : ℝ), s ∈ seamSideInterval b →
        (S.sphereSeam c).collar (z, s) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  obtain ⟨b, hb, -⟩ := L.sphere_owner c
  exact ⟨b, hb, fun z s hs => L.sphere_slimSide_removed c hb z hs⟩

/-- The open neighbour half of a sphere seam collar lies in `int_W (Z ∪ C)`, so not in `M₁`. -/
theorem SeamFacesLink.sphere_neighbourSide_not_mem_M1 (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.sphereSeamCount) {b : Bool}
    (hb : VL.index (S.sphereSide c b) =
      Rw.neighbourIndex (Rw.sharedNeighbour (L.sphereEquiv c).1))
    (z : ClosureSphere.{u}) {s : ℝ} (hs : s ∈ seamOpenSideInterval b) :
    (S.sphereSeam c).collar (z, s) ∉ regionM1 Rw.zero Rw.cusp := by
  have hI := S.sphereSeam_mem_interior_side c b z hs
  rw [VL.image_eq_rowSet, hb] at hI
  exact fun hM => hM (interior_mono (Rw.rowSet_neighbourIndex_subset _) hI)

end Seams

/-! ## Torus seams -/

section TorusSeams

variable {Rw : FC39RowsV2 W E} {V : VertexLayer W} {VL : VertexModelLink Rw V}
  {O : PortLayer W E V} {circ : CircleRegion W} {S : SeamLayer W V circ}
  {F : FaceLayer W E V S O} {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- The closed half `b` of a torus-seam collar lies in the side vertex `torusOwner c b`. -/
theorem SeamFacesLink.torusSeam_mem_side (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) (b : Bool) (t : Torus) {s : ℝ} (hs : s ∈ seamSideInterval b) :
    (S.torusSeam c).collar (t, s) ∈ (V.vertex (L.torusOwner c b)).image := by
  cases b
  · obtain ⟨h1, h2⟩ := hs
    have h := S.torusSide_pos c t s h1 h2
    rw [L.torusSide_eq] at h
    exact h
  · obtain ⟨h1, h2⟩ := hs
    have h := S.torusSide_neg c t s h1 h2
    rw [L.torusSide_eq] at h
    exact h

/-- The open half `b` of a torus-seam collar lies in the interior of the side vertex. -/
theorem SeamFacesLink.torusSeam_mem_interior_side (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) (b : Bool) (t : Torus) {s : ℝ}
    (hs : s ∈ seamOpenSideInterval b) :
    (S.torusSeam c).collar (t, s) ∈ interior (V.vertex (L.torusOwner c b)).image := by
  refine interior_maximal ?_ (torusSeam_isOpen_side_FIX2 (S.torusSeam c) b)
    ⟨(t, s), ⟨mem_univ _, hs⟩, rfl⟩
  rintro _ ⟨⟨t', s'⟩, ⟨-, hs'⟩, rfl⟩
  exact L.torusSeam_mem_side c b t' (seamOpenSideInterval_subset b hs')

/-- The zero slice of a torus seam (the shared face) lies in `int_{M₁} S`. -/
theorem SeamFacesLink.torusSlice_mem_relInt (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) (t : Torus) :
    (S.torusSeam c).collar (t, 0) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  have h : (S.torusSeam c).collar (t, 0) ∈ Rw.sharedSet (L.torusEquiv c).1 := by
    rw [← L.torus_slim c]
    exact ⟨t, rfl⟩
  exact Rw.junctions.shared_removed _ h

/-- **The whole collar of every torus seam misses `M₂`.** -/
theorem SeamFacesLink.torusSeam_target_disjoint_M2 (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) :
    Disjoint (S.torusSeam c).collar.target (regionM2 Rw.slim) := by
  rw [Set.disjoint_left]
  intro x hx hxM
  obtain ⟨t, s, hs1, hs2, rfl⟩ := torusSeam_exists_of_mem_target_FIX2 (S.torusSeam c) hx
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hI := L.torusSeam_mem_interior_side c true t
      (show s ∈ seamOpenSideInterval true from ⟨hs1, hs⟩)
    rw [VL.image_eq_rowSet] at hI
    exact Set.disjoint_left.1 (interior_rowSet_disjoint_regionM2 Rw.slim _) hI hxM
  · exact hxM.2 (L.torusSlice_mem_relInt c t)
  · have hI := L.torusSeam_mem_interior_side c false t
      (show s ∈ seamOpenSideInterval false from ⟨hs, hs2⟩)
    rw [VL.image_eq_rowSet] at hI
    exact Set.disjoint_left.1 (interior_rowSet_disjoint_regionM2 Rw.slim _) hI hxM

/-- **The slim half of a torus seam collar lies in `int_{M₁} S`.** -/
theorem SeamFacesLink.torus_slimSide_removed (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) {b : Bool}
    (hb : VL.index (L.torusOwner c b) = Rw.slimIndex (L.torusEquiv c).1)
    (t : Torus) {s : ℝ} (hs : s ∈ seamSideInterval b) :
    (S.torusSeam c).collar (t, s) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  by_cases h0 : s = 0
  · subst h0
    exact L.torusSlice_mem_relInt c t
  · have hI := L.torusSeam_mem_interior_side c b t (mem_seamOpenSideInterval_of_ne hs h0)
    rw [VL.image_eq_rowSet, hb] at hI
    exact Rw.junctions.slim_interior_subset_relInt (L.torusEquiv c).1.1.1.1 hI

/-- The slim side exists (`torus_owner`) and its closed half collar is removed. -/
theorem SeamFacesLink.exists_torus_slimSide_removed (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) :
    ∃ b, VL.index (L.torusOwner c b) = Rw.slimIndex (L.torusEquiv c).1 ∧
      ∀ (t : Torus) (s : ℝ), s ∈ seamSideInterval b →
        (S.torusSeam c).collar (t, s) ∈ relInt (regionM1 Rw.zero Rw.cusp) Rw.slim.union := by
  obtain ⟨b, hb, -⟩ := L.torus_owner c
  exact ⟨b, hb, fun t s hs => L.torus_slimSide_removed c hb t hs⟩

/-- The open neighbour half of a torus seam collar lies in `int_W (Z ∪ C)`, so not in `M₁`. -/
theorem SeamFacesLink.torus_neighbourSide_not_mem_M1 (L : SeamFacesLink Rw V VL O S F N)
    (c : Fin S.torusSeamCount) {b : Bool}
    (hb : VL.index (L.torusOwner c b) =
      Rw.neighbourIndex (Rw.sharedNeighbour (L.torusEquiv c).1))
    (t : Torus) {s : ℝ} (hs : s ∈ seamOpenSideInterval b) :
    (S.torusSeam c).collar (t, s) ∉ regionM1 Rw.zero Rw.cusp := by
  have hI := L.torusSeam_mem_interior_side c b t hs
  rw [VL.image_eq_rowSet, hb] at hI
  exact fun hM => hM (interior_mono (Rw.rowSet_neighbourIndex_subset _) hI)

end TorusSeams

end GC.GraphManifold.Assembly.FC39P0
