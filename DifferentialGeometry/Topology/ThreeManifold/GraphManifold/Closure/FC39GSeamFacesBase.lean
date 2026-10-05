import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidual

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): shared faces, sides, catalogue

Step G1 and the index bookkeeping of the joint seam–face construction (lane sheet
`build-logs/resume/sheet-FC39-G-SF.md`; dispositions D56-1, D58-6). Everything is read from the
fields of `FC39RowsV2`, a vertex link and a port link (no new hypothesis):

* G1 — a shared face is nonempty, lies in `W.interior` (through its neighbour face: the zero
  level of `ratio`, resp. the cusp internal level, both inside `near ⊆ W.interior`), distinct shared
  faces are disjoint (lane SAFE), hence the shared set determines the shared face; an external
  torus lies in `∂W` (`CuspCores.ports`);
* the two SIDES of a shared face `σ`: side `false` the slim owner (`slimIndex σ`), side `true` the
  neighbour (`neighbourIndex`); each side carries an actual model boundary face of its vertex whose
  image is the shared set (`exists_sideFace_GSF`: the slim end face `endFace σ.1`, the zero face, or
  the cusp internal face, transported along `vertex_piece`); the external face of the port `i`
  (`exists_externalFace_GSF`: the external model face of the cusp core `i`);
* the ONE face catalogue `Catalogue_GSF V = Σ k, ModelBoundaryFace (V.vertex k).piece`, the seam
  enumerations `sphereEquiv_GSF` / `torusEquiv_GSF` (finite enumerations of the sphere / torus
  shaped shared faces), the side entries `sEntry_GSF` / `tEntry_GSF`, the external entries
  `xEntry_GSF`, their injectivity and pairwise distinctness (from the images), the kind of a
  catalogue entry `kindOf_GSF` with the three iff rules, and the exhaustion of every vertex
  boundary by its catalogue entries.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## G1: shared faces -/

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- The end slices of an interval slim model are nonempty. -/
theorem slimModelEnd_nonempty_GSF {P : PieceEmbedding W} (m : SlimModel P)
    (hm : slimModelIsInterval m) (b : Bool) : (slimModelEnd m b).Nonempty := by
  cases m with
  | sphereInterval e => exact ⟨_, ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, rfl⟩⟩
  | torusInterval e => exact ⟨_, ⟨1, rfl⟩⟩
  | overCircle p hp hsub fib hcl => exact hm.elim

/-- A shared face is nonempty (its slim model is an interval model). -/
theorem sharedSet_nonempty_GSF (σ : Rw.SharedFace) : (Rw.sharedSet σ).Nonempty :=
  (slimModelEnd_nonempty_GSF (Rw.slim.model σ.1.1.1) σ.1.2 σ.1.1.2).image _

/-- A neighbour face lies in `W.interior`: a zero face in the zero level of `ratio`, a cusp
internal face in the internal level, both inside their `near ⊆ W.interior`. -/
theorem neighbourSet_subset_interior_GSF :
    ∀ F : NeighbourFace Rw.zero Rw.cusp, neighbourSet F ⊆ W.interior
  | .inl ⟨i, A⟩ => by
    intro x hx
    have hb : x ∈ pieceBoundary (Rw.zero.piece i) := image_mono A.subset hx
    rw [Rw.zero.boundary_eq i] at hb
    exact Rw.zero.near_interior i (Rw.zero.zero_subset_near i hb)
  | .inr ⟨b, A, hA⟩ => by
    intro x hx
    change x ∈ (Rw.cusp.piece b).map '' A.1 at hx
    rw [hA, Rw.cusp.internalModelFace_eq b] at hx
    obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hx
    have hx' : (Rw.cusp.piece b).map (Rw.cusp.product b (t, iccEnd true)) ∈
        {x | x ∈ Rw.cusp.near b ∧ Rw.cusp.cuspFn b x = 0} := by
      rw [← Rw.cusp.internal_eq b]
      exact ⟨t, rfl⟩
    exact Rw.cusp.near_interior b hx'.1

/-- **G1** A shared face lies in `W.interior`. -/
theorem sharedSet_subset_interior_GSF (σ : Rw.SharedFace) : Rw.sharedSet σ ⊆ W.interior := by
  rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
  exact Rw.neighbourSet_subset_interior_GSF _

/-- The shared set determines the shared face. -/
theorem sharedSet_injective_GSF {σ τ : Rw.SharedFace} (h : Rw.sharedSet σ = Rw.sharedSet τ) :
    σ = τ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Rw.sharedSet_nonempty_GSF σ
  exact Set.disjoint_left.1 (Rw.sharedSet_pairwise_disjoint_GSAFE hne) hx (h ▸ hx)

include Rw in
/-- An external boundary torus lies in `∂W` (`CuspCores.ports`). -/
theorem range_torusMap_subset_boundary_GSF (i : Fin n) :
    range (E.torusMap i) ⊆ W.model.boundary W.Carrier := by
  rw [Rw.cusp.ports]
  exact subset_iUnion (fun j => range (E.torusMap j)) i

/-- A shared face meets no external boundary torus. -/
theorem sharedSet_disjoint_torusMap_GSF (σ : Rw.SharedFace) (i : Fin n) :
    Disjoint (Rw.sharedSet σ) (range (E.torusMap i)) :=
  (W.model.disjoint_interior_boundary (M := W.Carrier)).mono
    (Rw.sharedSet_subset_interior_GSF σ) (Rw.range_torusMap_subset_boundary_GSF i)

/-! ## The two sides of a shared face -/

/-- The row index of the side `b` of a shared face: `false` the slim owner, `true` the
neighbour. -/
def sideIndex_GSF (σ : Rw.SharedFace) (b : Bool) : Rw.slim.RowIndex :=
  cond b (Rw.neighbourIndex (Rw.sharedNeighbour σ)) (Rw.slimIndex σ)

theorem sideIndex_true_ne_false_GSF (σ : Rw.SharedFace) :
    Rw.sideIndex_GSF σ true ≠ Rw.sideIndex_GSF σ false := by
  simp only [sideIndex_GSF, Bool.cond_true, Bool.cond_false, slimIndex]
  rcases Rw.sharedNeighbour σ with F | F <;> simp [neighbourIndex]

theorem sideIndex_injective_GSF (σ : Rw.SharedFace) : Injective (Rw.sideIndex_GSF σ) := by
  intro b b' h
  cases b <;> cases b'
  · rfl
  · exact ((Rw.sideIndex_true_ne_false_GSF σ) h.symm).elim
  · exact ((Rw.sideIndex_true_ne_false_GSF σ) h).elim
  · rfl

/-- The row piece of the side `b` carries an actual model boundary face whose image is the shared
set: the slim end face, the zero face, or the cusp internal face. -/
theorem exists_rowFace_GSF (σ : Rw.SharedFace) (b : Bool) :
    ∃ m : ModelBoundaryFace (Rw.rowPiece (Rw.sideIndex_GSF σ b)),
      (Rw.rowPiece (Rw.sideIndex_GSF σ b)).map '' m.1 = Rw.sharedSet σ := by
  cases b
  · refine ⟨Rw.slim.endFace σ.1, ?_⟩
    change (Rw.slim.piece σ.1.1.1).map '' (Rw.slim.endFace σ.1).1 = Rw.slim.endSet σ.1
    rw [Rw.slim.endFace_eq σ.1]
    rfl
  · rw [Rw.sharedSet_eq_neighbourSet_GSAFE σ]
    change ∃ m : ModelBoundaryFace (Rw.rowPiece (Rw.neighbourIndex (Rw.sharedNeighbour σ))),
      (Rw.rowPiece (Rw.neighbourIndex (Rw.sharedNeighbour σ))).map '' m.1 =
        neighbourSet (Rw.sharedNeighbour σ)
    rcases Rw.sharedNeighbour σ with ⟨i, A⟩ | ⟨b, A, hA⟩
    · exact ⟨A, rfl⟩
    · exact ⟨A, rfl⟩

end FC39RowsV2

/-- Transport of a model face along an equality of pieces. -/
theorem exists_face_of_eq_GSF {P Q : PieceEmbedding W} (h : P = Q) (m' : ModelBoundaryFace Q) :
    ∃ m : ModelBoundaryFace P, P.map '' m.1 = Q.map '' m'.1 := by
  subst h
  exact ⟨m', rfl⟩

/-- The side `b` of a shared face: an actual model boundary face of the side vertex whose image is
the shared set. -/
theorem exists_sideFace_GSF (Rw : FC39RowsV2 W E) {V : VertexLayer W}
    (vlink : VertexModelLink Rw V) (σ : Rw.SharedFace) (b : Bool) :
    ∃ m : ModelBoundaryFace (V.vertex (vlink.index.symm (Rw.sideIndex_GSF σ b))).piece,
      (V.vertex (vlink.index.symm (Rw.sideIndex_GSF σ b))).piece.map '' m.1 = Rw.sharedSet σ := by
  have hP : (V.vertex (vlink.index.symm (Rw.sideIndex_GSF σ b))).piece =
      Rw.rowPiece (Rw.sideIndex_GSF σ b) := by
    rw [vlink.vertex_piece, Equiv.apply_symm_apply]
  obtain ⟨m', hm'⟩ := Rw.exists_rowFace_GSF σ b
  obtain ⟨m, hm⟩ := exists_face_of_eq_GSF hP m'
  exact ⟨m, hm.trans hm'⟩

/-- The external face of the port `i`: the external model face of the cusp core `i`. -/
theorem exists_externalFace_GSF (Rw : FC39RowsV2 W E) {V : VertexLayer W}
    {vlink : VertexModelLink Rw V} {O : PortLayer W E V} (olink : PortModelLink Rw vlink O)
    (i : Fin n) :
    ∃ m : ModelBoundaryFace (V.vertex (O.externalOwner i)).piece,
      (V.vertex (O.externalOwner i)).piece.map '' m.1 = range (E.torusMap i) := by
  have hP : (V.vertex (O.externalOwner i)).piece = Rw.cusp.piece i := by
    rw [olink.owner_vertex_G1 i]
    rfl
  obtain ⟨m, hm⟩ := exists_face_of_eq_GSF hP (Rw.cusp.externalModelFace i)
  refine ⟨m, hm.trans ?_⟩
  rw [Rw.cusp.externalModelFace_eq i]
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, (Rw.cusp.external_end i t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨t, rfl⟩, Rw.cusp.external_end i t⟩

/-! ## The face catalogue -/

/-- The face catalogue of a vertex layer: every actual model boundary face of every vertex. -/
abbrev Catalogue_GSF (V : VertexLayer W) : Type u :=
  Σ k : Fin V.vertexCount, ModelBoundaryFace (V.vertex k).piece

/-- The ambient image of a catalogue entry. -/
def catImage_GSF {V : VertexLayer W} (p : Catalogue_GSF V) : Set W.Carrier :=
  (V.vertex p.1).piece.map '' p.2.1

theorem catImage_nonempty_GSF {V : VertexLayer W} (p : Catalogue_GSF V) :
    (catImage_GSF p).Nonempty := by
  obtain ⟨x, hx, hc⟩ := p.2.2
  refine ⟨_, x, ?_, rfl⟩
  rw [hc]
  exact mem_connectedComponentIn hx

theorem catImage_subset_boundaryImage_GSF {V : VertexLayer W} (p : Catalogue_GSF V) :
    catImage_GSF p ⊆ (V.vertex p.1).boundaryImage :=
  image_mono p.2.subset

/-- Two catalogue entries of the same vertex whose images meet are equal. -/
theorem catalogue_eq_of_meet_GSF {V : VertexLayer W} {p p' : Catalogue_GSF V} (h1 : p.1 = p'.1)
    (h : (catImage_GSF p ∩ catImage_GSF p').Nonempty) : p = p' := by
  obtain ⟨k, m⟩ := p
  obtain ⟨k', m'⟩ := p'
  dsimp only at h1
  subst h1
  obtain rfl := ModelBoundaryFace.eq_of_image_meet (m := m) (m' := m') h
  rfl

/-- The faces of a catalogue owned by a vertex exhaust its model boundary image. -/
theorem catalogue_exhausted_GSF {V : VertexLayer W} {m : ℕ} (e : Fin m ≃ Catalogue_GSF V)
    (k : Fin V.vertexCount) :
    (⋃ (f : Fin m) (_ : (e f).1 = k), catImage_GSF (e f)) = (V.vertex k).boundaryImage := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun f hf => ?_
    rw [← hf]
    exact catImage_subset_boundaryImage_GSF (e f)
  · rintro _ ⟨q, hq, rfl⟩
    refine mem_iUnion₂.2 ⟨e.symm ⟨k, ActualComponent.of hq⟩, by rw [Equiv.apply_symm_apply], ?_⟩
    rw [Equiv.apply_symm_apply]
    exact ⟨q, mem_connectedComponentIn hq, rfl⟩

/-! ## Seam indices and side entries -/

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- Sphere-shaped shared faces. -/
abbrev SphereShared_GSF : Type := {σ : Rw.SharedFace // Rw.sharedShape σ = .sphere}

/-- Torus-shaped shared faces. -/
abbrev TorusShared_GSF : Type := {σ : Rw.SharedFace // Rw.sharedShape σ = .torus}

instance finite_sharedFace_GSF : Finite Rw.SharedFace :=
  Rw.finite_sharedFace_GSAFE

/-- The number of sphere seams. -/
def sphereCount_GSF : ℕ := Nat.card Rw.SphereShared_GSF

/-- The number of torus seams. -/
def torusCount_GSF : ℕ := Nat.card Rw.TorusShared_GSF

/-- The sphere seam indices: an enumeration of the sphere-shaped shared faces. -/
def sphereEquiv_GSF : Fin Rw.sphereCount_GSF ≃ Rw.SphereShared_GSF :=
  (Finite.equivFin _).symm

/-- The torus seam indices: an enumeration of the torus-shaped shared faces. -/
def torusEquiv_GSF : Fin Rw.torusCount_GSF ≃ Rw.TorusShared_GSF :=
  (Finite.equivFin _).symm

theorem sphereShared_ne_torusShared_GSF (σ : Rw.SphereShared_GSF) (τ : Rw.TorusShared_GSF) :
    σ.1 ≠ τ.1 := by
  intro h
  have h1 := σ.2
  rw [h, τ.2] at h1
  cases h1

end FC39RowsV2

section Entries

variable (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
  (O : PortLayer W E V) (olink : PortModelLink Rw vlink O)

/-- The vertex of the side `b` of a shared face. -/
def sideVertex_GSF (σ : Rw.SharedFace) (b : Bool) : Fin V.vertexCount :=
  vlink.index.symm (Rw.sideIndex_GSF σ b)

/-- The face of the side `b` of a shared face. -/
def sideFace_GSF (σ : Rw.SharedFace) (b : Bool) :
    ModelBoundaryFace (V.vertex (sideVertex_GSF Rw V vlink σ b)).piece :=
  Classical.choose (exists_sideFace_GSF Rw vlink σ b)

theorem sideFace_image_GSF (σ : Rw.SharedFace) (b : Bool) :
    (V.vertex (sideVertex_GSF Rw V vlink σ b)).piece.map '' (sideFace_GSF Rw V vlink σ b).1 =
      Rw.sharedSet σ :=
  Classical.choose_spec (exists_sideFace_GSF Rw vlink σ b)

theorem image_sideVertex_GSF (σ : Rw.SharedFace) (b : Bool) :
    (V.vertex (sideVertex_GSF Rw V vlink σ b)).image = Rw.slim.rowSet (Rw.sideIndex_GSF σ b) := by
  rw [VertexModelLink.image_eq_G1, sideVertex_GSF, Equiv.apply_symm_apply]

theorem index_sideVertex_GSF (σ : Rw.SharedFace) (b : Bool) :
    vlink.index (sideVertex_GSF Rw V vlink σ b) = Rw.sideIndex_GSF σ b :=
  Equiv.apply_symm_apply _ _

/-- The external face of the port `i`. -/
def externalFace_GSF (i : Fin n) : ModelBoundaryFace (V.vertex (O.externalOwner i)).piece :=
  Classical.choose (exists_externalFace_GSF Rw olink i)

theorem externalFace_image_GSF (i : Fin n) :
    (V.vertex (O.externalOwner i)).piece.map '' (externalFace_GSF Rw V vlink O olink i).1 =
      range (E.torusMap i) :=
  Classical.choose_spec (exists_externalFace_GSF Rw olink i)

/-- The catalogue entry of the side `b` of the sphere seam `c`. -/
def sEntry_GSF (c : Fin Rw.sphereCount_GSF) (b : Bool) : Catalogue_GSF V :=
  ⟨sideVertex_GSF Rw V vlink (Rw.sphereEquiv_GSF c).1 b, sideFace_GSF Rw V vlink _ b⟩

/-- The catalogue entry of the side `b` of the torus seam `c`. -/
def tEntry_GSF (c : Fin Rw.torusCount_GSF) (b : Bool) : Catalogue_GSF V :=
  ⟨sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 b, sideFace_GSF Rw V vlink _ b⟩

/-- The catalogue entry of the external face of the port `i`. -/
def xEntry_GSF (i : Fin n) : Catalogue_GSF V :=
  ⟨O.externalOwner i, externalFace_GSF Rw V vlink O olink i⟩

theorem catImage_sEntry_GSF (c : Fin Rw.sphereCount_GSF) (b : Bool) :
    catImage_GSF (sEntry_GSF Rw V vlink c b) = Rw.sharedSet (Rw.sphereEquiv_GSF c).1 :=
  sideFace_image_GSF Rw V vlink _ b

theorem catImage_tEntry_GSF (c : Fin Rw.torusCount_GSF) (b : Bool) :
    catImage_GSF (tEntry_GSF Rw V vlink c b) = Rw.sharedSet (Rw.torusEquiv_GSF c).1 :=
  sideFace_image_GSF Rw V vlink _ b

theorem catImage_xEntry_GSF (i : Fin n) :
    catImage_GSF (xEntry_GSF Rw V vlink O olink i) = range (E.torusMap i) :=
  externalFace_image_GSF Rw V vlink O olink i

theorem sEntry_injective_GSF {c c' : Fin Rw.sphereCount_GSF} {b b' : Bool}
    (h : sEntry_GSF Rw V vlink c b = sEntry_GSF Rw V vlink c' b') : c = c' ∧ b = b' := by
  have himg := congrArg catImage_GSF h
  rw [catImage_sEntry_GSF, catImage_sEntry_GSF] at himg
  have hcc : c = c' :=
    (Rw.sphereEquiv_GSF).injective (Subtype.ext (Rw.sharedSet_injective_GSF himg))
  subst hcc
  refine ⟨rfl, Rw.sideIndex_injective_GSF (Rw.sphereEquiv_GSF c).1 ?_⟩
  have h1 := congrArg Sigma.fst h
  exact vlink.index.symm.injective h1

theorem tEntry_injective_GSF {c c' : Fin Rw.torusCount_GSF} {b b' : Bool}
    (h : tEntry_GSF Rw V vlink c b = tEntry_GSF Rw V vlink c' b') : c = c' ∧ b = b' := by
  have himg := congrArg catImage_GSF h
  rw [catImage_tEntry_GSF, catImage_tEntry_GSF] at himg
  have hcc : c = c' :=
    (Rw.torusEquiv_GSF).injective (Subtype.ext (Rw.sharedSet_injective_GSF himg))
  subst hcc
  refine ⟨rfl, Rw.sideIndex_injective_GSF (Rw.torusEquiv_GSF c).1 ?_⟩
  have h1 := congrArg Sigma.fst h
  exact vlink.index.symm.injective h1

theorem xEntry_injective_GSF {i i' : Fin n}
    (h : xEntry_GSF Rw V vlink O olink i = xEntry_GSF Rw V vlink O olink i') : i = i' := by
  have h1 := congrArg (fun p => vlink.index p.1) h
  simp only [xEntry_GSF, olink.owner_index] at h1
  simpa using h1

theorem sEntry_ne_tEntry_GSF (c : Fin Rw.sphereCount_GSF) (b : Bool)
    (c' : Fin Rw.torusCount_GSF) (b' : Bool) :
    sEntry_GSF Rw V vlink c b ≠ tEntry_GSF Rw V vlink c' b' := by
  intro h
  have himg := congrArg catImage_GSF h
  rw [catImage_sEntry_GSF, catImage_tEntry_GSF] at himg
  exact Rw.sphereShared_ne_torusShared_GSF _ _ (Rw.sharedSet_injective_GSF himg)

theorem sEntry_ne_xEntry_GSF (c : Fin Rw.sphereCount_GSF) (b : Bool) (i : Fin n) :
    sEntry_GSF Rw V vlink c b ≠ xEntry_GSF Rw V vlink O olink i := by
  intro h
  have himg := congrArg catImage_GSF h
  rw [catImage_sEntry_GSF, catImage_xEntry_GSF] at himg
  obtain ⟨x, hx⟩ := Rw.sharedSet_nonempty_GSF (Rw.sphereEquiv_GSF c).1
  exact Set.disjoint_left.1 (Rw.sharedSet_disjoint_torusMap_GSF _ i) hx (himg ▸ hx)

theorem tEntry_ne_xEntry_GSF (c : Fin Rw.torusCount_GSF) (b : Bool) (i : Fin n) :
    tEntry_GSF Rw V vlink c b ≠ xEntry_GSF Rw V vlink O olink i := by
  intro h
  have himg := congrArg catImage_GSF h
  rw [catImage_tEntry_GSF, catImage_xEntry_GSF] at himg
  obtain ⟨x, hx⟩ := Rw.sharedSet_nonempty_GSF (Rw.torusEquiv_GSF c).1
  exact Set.disjoint_left.1 (Rw.sharedSet_disjoint_torusMap_GSF _ i) hx (himg ▸ hx)

open Classical in
/-- **The kind of a catalogue entry**: a sphere / torus seam side, an external face, or
partitioned (every other face, a whole vertex–circle torus included). -/
def kindOf_GSF (p : Catalogue_GSF V) : FaceKind n Rw.torusCount_GSF Rw.sphereCount_GSF :=
  if h : ∃ cb : Fin Rw.sphereCount_GSF × Bool, sEntry_GSF Rw V vlink cb.1 cb.2 = p then
    .sphereSeam h.choose.1 h.choose.2
  else if h' : ∃ cb : Fin Rw.torusCount_GSF × Bool, tEntry_GSF Rw V vlink cb.1 cb.2 = p then
    .torusSeam h'.choose.1 h'.choose.2
  else if h'' : ∃ i, xEntry_GSF Rw V vlink O olink i = p then .external h''.choose
  else .partitioned

variable {Rw V vlink O olink} in
theorem kindOf_sphereSeam_iff_GSF {p : Catalogue_GSF V} {c : Fin Rw.sphereCount_GSF} {b : Bool} :
    kindOf_GSF Rw V vlink O olink p = .sphereSeam c b ↔ p = sEntry_GSF Rw V vlink c b := by
  constructor
  · intro h
    unfold kindOf_GSF at h
    split_ifs at h with h1 h2 h3
    · injection h with hc hb
      rw [← h1.choose_spec, hc, hb]
  · rintro rfl
    unfold kindOf_GSF
    rw [dite_eq_left ⟨(c, b), rfl⟩]
    have h1 : ∃ cb : Fin Rw.sphereCount_GSF × Bool,
        sEntry_GSF Rw V vlink cb.1 cb.2 = sEntry_GSF Rw V vlink c b := ⟨(c, b), rfl⟩
    obtain ⟨hc, hb⟩ := sEntry_injective_GSF Rw V vlink h1.choose_spec
    rw [hc, hb]

variable {Rw V vlink O olink} in
theorem kindOf_torusSeam_iff_GSF {p : Catalogue_GSF V} {c : Fin Rw.torusCount_GSF} {b : Bool} :
    kindOf_GSF Rw V vlink O olink p = .torusSeam c b ↔ p = tEntry_GSF Rw V vlink c b := by
  constructor
  · intro h
    unfold kindOf_GSF at h
    split_ifs at h with h1 h2 h3
    · injection h with hc hb
      rw [← h2.choose_spec, hc, hb]
  · rintro rfl
    unfold kindOf_GSF
    rw [dite_eq_right (by
      rintro ⟨cb, hcb⟩
      exact sEntry_ne_tEntry_GSF Rw V vlink cb.1 cb.2 c b hcb), dite_eq_left ⟨(c, b), rfl⟩]
    have h1 : ∃ cb : Fin Rw.torusCount_GSF × Bool,
        tEntry_GSF Rw V vlink cb.1 cb.2 = tEntry_GSF Rw V vlink c b := ⟨(c, b), rfl⟩
    obtain ⟨hc, hb⟩ := tEntry_injective_GSF Rw V vlink h1.choose_spec
    rw [hc, hb]

variable {Rw V vlink O olink} in
theorem kindOf_external_iff_GSF {p : Catalogue_GSF V} {i : Fin n} :
    kindOf_GSF Rw V vlink O olink p = .external i ↔ p = xEntry_GSF Rw V vlink O olink i := by
  constructor
  · intro h
    unfold kindOf_GSF at h
    split_ifs at h with h1 h2 h3
    · injection h with hi
      rw [← h3.choose_spec, hi]
  · rintro rfl
    unfold kindOf_GSF
    rw [dite_eq_right (by
      rintro ⟨cb, hcb⟩
      exact sEntry_ne_xEntry_GSF Rw V vlink O olink cb.1 cb.2 i hcb), dite_eq_right (by
      rintro ⟨cb, hcb⟩
      exact tEntry_ne_xEntry_GSF Rw V vlink O olink cb.1 cb.2 i hcb), dite_eq_left ⟨i, rfl⟩]
    have h1 : ∃ i', xEntry_GSF Rw V vlink O olink i' = xEntry_GSF Rw V vlink O olink i := ⟨i, rfl⟩
    rw [xEntry_injective_GSF Rw V vlink O olink h1.choose_spec]

end Entries

end GC.GraphManifold.Assembly.FC39P0
