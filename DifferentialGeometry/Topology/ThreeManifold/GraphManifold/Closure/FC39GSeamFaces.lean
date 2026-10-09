import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesDisjoint

/-!
# FC39 GROUP G, target `stub_exists_seams_faces` (lane FC39-G-SF): the joint seam–face layers

The frozen target `T:289–299` (`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`),
proved as a general theorem on the contract (external review 56, D56-1; dispositions D58-6: the
safe neighbourhoods `N = safe.shared` are GIVEN first, seams and faces are built JOINTLY from them).
Step G9 of the lane sheet (`build-logs/resume/sheet-FC39-G-SF.md`):

* ONE index set drives both layers: the face catalogue `Catalogue_GSF V` (every actual model
  boundary face of every vertex, `FC39GSeamFacesBase.lean`), finite with sphere / torus face models
  (`FC39GSeamFacesBoundary.lean`); the sphere (torus) seams are indexed by the sphere- (torus-)
  shaped shared faces, and the two sides of the seam `c` ARE the catalogue entries
  `sEntry_GSF c b` / `tEntry_GSF c b`; the kind of an entry is read off this identification
  (`kindOf_GSF`);
* `seamLayer_GSF` — the seams of `FC39GSeamFacesSeams.lean` inside the given `N σ`, sides the slim
  owner (`false`, positive collar side) and the neighbour (`true`, negative side), every torus side a
  vertex;
* `faceLayer_GSF` — the catalogue, exhausting every vertex boundary, faces disjoint except the two
  sides of one seam (`catImage_disjoint_GSF`, `FC39GSeamFacesDisjoint.lean`), external faces the
  boundary tori, seam faces the zero slices of the collars;
* `seamFacesLink_GSF` — the joint link with the side parametrizations of
  `FC39GSeamFacesParams.lean` (each side map is the zero slice of the collar);
* `exists_seams_faces_GSF` — **the frozen statement**, strengthened: the circle restriction link
  `clink` is not read (the circle region only enters the type of `SeamLayer`; every torus side is a
  vertex), so it is dropped; the verbatim form is the `example` at the end.
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

section Assembly

variable (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
  (O : PortLayer W E V) (olink : PortModelLink Rw vlink O)
  (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier) (hN : SharedSafe Rw N)

/-! ## Seams -/

/-- The seam of a sphere-shaped shared face. -/
def sSeam_GSF (τ : Rw.SphereShared_GSF) : SphereSeam W :=
  Classical.choose (Rw.exists_sphereSeam_GSF N hN τ.1 τ.2)

/-- Its zero section. -/
def sParam_GSF (τ : Rw.SphereShared_GSF) : ClosureSphere.{u} → W.Carrier :=
  Classical.choose (Classical.choose_spec (Rw.exists_sphereSeam_GSF N hN τ.1 τ.2))

theorem sSeam_spec_GSF (τ : Rw.SphereShared_GSF) :
    IsSmoothEmbedding (𝓡 2) W.model ∞ (sParam_GSF Rw N hN τ) ∧
      (∀ z, (sSeam_GSF Rw N hN τ).collar (z, 0) = sParam_GSF Rw N hN τ z) ∧
      range (sParam_GSF Rw N hN τ) = Rw.sharedSet τ.1 ∧
      (∀ z s, s ≤ 0 → -1 < s → (sSeam_GSF Rw N hN τ).collar (z, s) ∈
        Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour τ.1))) ∧
      (∀ z s, 0 ≤ s → s < 1 →
        (sSeam_GSF Rw N hN τ).collar (z, s) ∈ Rw.slim.rowSet (Rw.slimIndex τ.1)) ∧
      closure (sSeam_GSF Rw N hN τ).collar.target ⊆ (N τ.1 : Set W.Carrier) :=
  Classical.choose_spec (Classical.choose_spec (Rw.exists_sphereSeam_GSF N hN τ.1 τ.2))

/-- The seam of a torus-shaped shared face. -/
def tSeam_GSF (τ : Rw.TorusShared_GSF) : TorusSeam W :=
  Classical.choose (Rw.exists_torusSeam_GSF N hN τ.1 τ.2)

/-- Its zero section. -/
def tParam_GSF (τ : Rw.TorusShared_GSF) : Torus → W.Carrier :=
  Classical.choose (Classical.choose_spec (Rw.exists_torusSeam_GSF N hN τ.1 τ.2))

theorem tSeam_spec_GSF (τ : Rw.TorusShared_GSF) :
    IsSmoothEmbedding torusModel W.model ∞ (tParam_GSF Rw N hN τ) ∧
      (∀ t, (tSeam_GSF Rw N hN τ).collar (t, 0) = tParam_GSF Rw N hN τ t) ∧
      range (tParam_GSF Rw N hN τ) = Rw.sharedSet τ.1 ∧
      (∀ t s, -1 < s → s ≤ 0 → (tSeam_GSF Rw N hN τ).collar (t, s) ∈
        Rw.slim.rowSet (Rw.neighbourIndex (Rw.sharedNeighbour τ.1))) ∧
      (∀ t s, 0 ≤ s → s < 1 →
        (tSeam_GSF Rw N hN τ).collar (t, s) ∈ Rw.slim.rowSet (Rw.slimIndex τ.1)) ∧
      closure (tSeam_GSF Rw N hN τ).collar.target ⊆ (N τ.1 : Set W.Carrier) :=
  Classical.choose_spec (Classical.choose_spec (Rw.exists_torusSeam_GSF N hN τ.1 τ.2))

theorem sphereSide_ne_GSF (c d : Fin Rw.sphereCount_GSF) (hcd : c ≠ d) :
    (Rw.sphereEquiv_GSF c).1 ≠ (Rw.sphereEquiv_GSF d).1 := fun h =>
  hcd ((Rw.sphereEquiv_GSF).injective (Subtype.ext h))

theorem torusSide_ne_GSF (c d : Fin Rw.torusCount_GSF) (hcd : c ≠ d) :
    (Rw.torusEquiv_GSF c).1 ≠ (Rw.torusEquiv_GSF d).1 := fun h =>
  hcd ((Rw.torusEquiv_GSF).injective (Subtype.ext h))

/-- **The seam layer.** -/
def seamLayer_GSF (circ : CircleRegion W) : SeamLayer W V circ where
  torusSeamCount := Rw.torusCount_GSF
  torusSeam c := tSeam_GSF Rw N hN (Rw.torusEquiv_GSF c)
  torusSide c b := some (sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 b)
  torusSide_neg c t s hs hs' := by
    change _ ∈ (V.vertex (sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 true)).image
    rw [image_sideVertex_GSF]
    exact (tSeam_spec_GSF Rw N hN _).2.2.2.1 t s hs hs'
  torusSide_pos c t s hs hs' := by
    change _ ∈ (V.vertex (sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 false)).image
    rw [image_sideVertex_GSF]
    exact (tSeam_spec_GSF Rw N hN _).2.2.2.2.1 t s hs hs'
  torusSeam_disjoint c d hcd :=
    (hN.closure_disjoint (torusSide_ne_GSF Rw c d hcd)).mono
      ((subset_closure.trans (tSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)
      ((subset_closure.trans (tSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)
  sphereSeamCount := Rw.sphereCount_GSF
  sphereSeam c := sSeam_GSF Rw N hN (Rw.sphereEquiv_GSF c)
  sphereSide c b := sideVertex_GSF Rw V vlink (Rw.sphereEquiv_GSF c).1 b
  sphereSide_neg c z s hs hs' := by
    rw [image_sideVertex_GSF]
    exact (sSeam_spec_GSF Rw N hN _).2.2.2.1 z s hs hs'
  sphereSide_pos c z s hs hs' := by
    rw [image_sideVertex_GSF]
    exact (sSeam_spec_GSF Rw N hN _).2.2.2.2.1 z s hs hs'
  sphereSeam_disjoint c d hcd :=
    (hN.closure_disjoint (sphereSide_ne_GSF Rw c d hcd)).mono
      ((subset_closure.trans (sSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)
      ((subset_closure.trans (sSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)
  sphere_torus_seam_disjoint c d :=
    (hN.closure_disjoint (Rw.sphereShared_ne_torusShared_GSF _ _)).mono
      ((subset_closure.trans (sSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)
      ((subset_closure.trans (tSeam_spec_GSF Rw N hN _).2.2.2.2.2).trans subset_closure)

/-! ## Faces -/

/-- **The face layer.** -/
def faceLayer_GSF (circ : CircleRegion W) :
    FaceLayer W E V (seamLayer_GSF Rw V vlink N hN circ) O where
  faceCount := Nat.card (Catalogue_GSF V)
  face f := catImage_GSF (catEquiv_GSF V f)
  faceOwner f := (catEquiv_GSF V f).1
  faceModel f := catModel_GSF (catEquiv_GSF V f)
  face_exhausted k := catalogue_exhausted_GSF (catEquiv_GSF V) k
  faceKind f := kindOf_GSF Rw V vlink O olink (catEquiv_GSF V f)
  face_disjoint f f' hne hs ht := by
    refine catImage_disjoint_GSF Rw V vlink (fun h => hne ((catEquiv_GSF V).injective h))
      (fun c b hcb => hs c b ⟨?_, ?_⟩) (fun c b hcb => ht c b ⟨?_, ?_⟩)
    · exact (kindOf_sphereSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 hcb.1
    · exact (kindOf_sphereSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 hcb.2
    · exact (kindOf_torusSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 hcb.1
    · exact (kindOf_torusSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 hcb.2
  face_external f i h := by
    have hf := (kindOf_external_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).1 h
    refine ⟨?_, ?_⟩
    · rw [hf]
      exact catImage_xEntry_GSF Rw V vlink O olink i
    · rw [hf]
      rfl
  external_face i := ⟨(catEquiv_GSF V).symm (xEntry_GSF Rw V vlink O olink i),
    (kindOf_external_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 (Equiv.apply_symm_apply _ _)⟩
  face_torusSeam f c b h := by
    have hf := (kindOf_torusSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).1 h
    refine ⟨?_, ?_⟩
    · rw [hf]
      refine (catImage_tEntry_GSF Rw V vlink c b).trans ?_
      have h1 := (tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)).2.1
      have h2 := (tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)).2.2.1
      change _ = range fun t => (tSeam_GSF Rw N hN (Rw.torusEquiv_GSF c)).collar (t, 0)
      simp only [h1]
      exact h2.symm
    · change some (sideVertex_GSF Rw V vlink _ b) = some (catEquiv_GSF V f).1
      rw [hf]
      rfl
  torusSeam_face c b k hk := by
    refine ⟨(catEquiv_GSF V).symm (tEntry_GSF Rw V vlink c b), ?_,
      (kindOf_torusSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 (Equiv.apply_symm_apply _ _)⟩
    rw [Equiv.apply_symm_apply]
    exact Option.some_injective _ hk
  face_sphereSeam f c b h := by
    have hf := (kindOf_sphereSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).1 h
    refine ⟨?_, ?_⟩
    · rw [hf]
      refine (catImage_sEntry_GSF Rw V vlink c b).trans ?_
      have h1 := (sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)).2.1
      have h2 := (sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)).2.2.1
      change _ = range fun z => (sSeam_GSF Rw N hN (Rw.sphereEquiv_GSF c)).collar (z, 0)
      simp only [h1]
      exact h2.symm
    · change sideVertex_GSF Rw V vlink _ b = (catEquiv_GSF V f).1
      rw [hf]
      rfl
  sphereSeam_face c b := ⟨(catEquiv_GSF V).symm (sEntry_GSF Rw V vlink c b),
    by
      rw [Equiv.apply_symm_apply]
      rfl,
    (kindOf_sphereSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)).2 (Equiv.apply_symm_apply _ _)⟩

/-! ## Side parametrizations and the joint link -/

theorem exists_sSideParam_GSF (c : Fin Rw.sphereCount_GSF) (b : Bool) :
    ∃ ψ : ClosureSphere.{u} →
        (V.vertex (sideVertex_GSF Rw V vlink (Rw.sphereEquiv_GSF c).1 b)).piece.Piece,
      IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ ψ ∧ range ψ = (sideFace_GSF Rw V vlink _ b).1 ∧
        ∀ z, (V.vertex (sideVertex_GSF Rw V vlink (Rw.sphereEquiv_GSF c).1 b)).piece.map (ψ z) =
          (sSeam_GSF Rw N hN (Rw.sphereEquiv_GSF c)).collar (z, 0) := by
  have hs := sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)
  obtain ⟨ψ, h1, h2, h3⟩ := exists_sideParam_GSF _ (sideFace_GSF Rw V vlink _ b) hs.1
    (hs.2.2.1.trans (sideFace_image_GSF Rw V vlink _ b).symm)
    (hs.2.2.1 ▸ Rw.sharedSet_subset_interior_GSF _)
  exact ⟨ψ, h1, h2, fun z => (h3 z).trans (hs.2.1 z).symm⟩

theorem exists_tSideParam_GSF (c : Fin Rw.torusCount_GSF) (b : Bool) :
    ∃ ψ : Torus → (V.vertex (sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 b)).piece.Piece,
      IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ ψ ∧ range ψ = (sideFace_GSF Rw V vlink _ b).1 ∧
        ∀ t, (V.vertex (sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 b)).piece.map (ψ t) =
          (tSeam_GSF Rw N hN (Rw.torusEquiv_GSF c)).collar (t, 0) := by
  have hs := tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)
  obtain ⟨ψ, h1, h2, h3⟩ := exists_sideParam_torus_GSF _ (sideFace_GSF Rw V vlink _ b) hs.1
    (hs.2.2.1.trans (sideFace_image_GSF Rw V vlink _ b).symm)
    (hs.2.2.1 ▸ Rw.sharedSet_subset_interior_GSF _)
  exact ⟨ψ, h1, h2, fun t => (h3 t).trans (hs.2.1 t).symm⟩

/-- **The joint seam–face link.** -/
def seamFacesLink_GSF (circ : CircleRegion W) :
    SeamFacesLink Rw V vlink O (seamLayer_GSF Rw V vlink N hN circ)
      (faceLayer_GSF Rw V vlink O olink N hN circ) N where
  sphereEquiv := Rw.sphereEquiv_GSF
  torusEquiv := Rw.torusEquiv_GSF
  sphere_slim c := by
    have hs := sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)
    change (range fun z => (sSeam_GSF Rw N hN (Rw.sphereEquiv_GSF c)).collar (z, 0)) = _
    simp only [hs.2.1]
    exact hs.2.2.1
  sphere_neighbour c := by
    have hs := sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)
    change (range fun z => (sSeam_GSF Rw N hN (Rw.sphereEquiv_GSF c)).collar (z, 0)) = _
    simp only [hs.2.1]
    exact hs.2.2.1.trans (Rw.sharedSet_eq_neighbourSet_GSAFE _)
  sphere_owner c := ⟨false, Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _⟩
  sphereSideFace c b := sideFace_GSF Rw V vlink _ b
  sphereSideParam c b := Classical.choose (exists_sSideParam_GSF Rw V vlink N hN c b)
  sphereSideParam_embedding c b :=
    (Classical.choose_spec (exists_sSideParam_GSF Rw V vlink N hN c b)).1
  sphereSideParam_range c b :=
    (Classical.choose_spec (exists_sSideParam_GSF Rw V vlink N hN c b)).2.1
  sphereSide_map c b := (Classical.choose_spec (exists_sSideParam_GSF Rw V vlink N hN c b)).2.2
  sphere_closure c := (sSeam_spec_GSF Rw N hN (Rw.sphereEquiv_GSF c)).2.2.2.2.2
  torusOwner c b := sideVertex_GSF Rw V vlink (Rw.torusEquiv_GSF c).1 b
  torusSide_eq c b := rfl
  torus_slim c := by
    have hs := tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)
    change (range fun t => (tSeam_GSF Rw N hN (Rw.torusEquiv_GSF c)).collar (t, 0)) = _
    simp only [hs.2.1]
    exact hs.2.2.1
  torus_neighbour c := by
    have hs := tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)
    change (range fun t => (tSeam_GSF Rw N hN (Rw.torusEquiv_GSF c)).collar (t, 0)) = _
    simp only [hs.2.1]
    exact hs.2.2.1.trans (Rw.sharedSet_eq_neighbourSet_GSAFE _)
  torus_owner c := ⟨false, Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _⟩
  torusSideFace c b := sideFace_GSF Rw V vlink _ b
  torusSideParam c b := Classical.choose (exists_tSideParam_GSF Rw V vlink N hN c b)
  torusSideParam_embedding c b :=
    (Classical.choose_spec (exists_tSideParam_GSF Rw V vlink N hN c b)).1
  torusSideParam_range c b :=
    (Classical.choose_spec (exists_tSideParam_GSF Rw V vlink N hN c b)).2.1
  torusSide_map c b := (Classical.choose_spec (exists_tSideParam_GSF Rw V vlink N hN c b)).2.2
  torus_closure c := (tSeam_spec_GSF Rw N hN (Rw.torusEquiv_GSF c)).2.2.2.2.2
  externalSideFace i := externalFace_GSF Rw V vlink O olink i
  externalSideFace_image i := externalFace_image_GSF Rw V vlink O olink i
  faceEquiv := catEquiv_GSF V
  faceEquiv_owner _ := rfl
  face_image _ := rfl
  kind_sphere := kindOf_sphereSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)
  kind_torus := kindOf_torusSeam_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)
  kind_external := kindOf_external_iff_GSF (Rw := Rw) (V := V) (vlink := vlink) (O := O) (olink := olink)

end Assembly

/-- **GROUP G, `stub_exists_seams_faces` (frozen statement `T:289–299`), strengthened**: the
circle restriction link is not read (dropped). Seams and faces are built jointly from the given
safe neighbourhoods `N`. -/
theorem exists_seams_faces_GSF (Rw : FC39RowsV2 W E)
    (V : VertexLayer W) (vlink : VertexModelLink Rw V)
    (circ : CircleRegion W)
    (O : PortLayer W E V) (olink : PortModelLink Rw vlink O)
    (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier)
    (hN : SharedSafe Rw N) :
    ∃ S : SeamLayer W V circ,
    ∃ F : FaceLayer W E V S O,
      Nonempty (SeamFacesLink Rw V vlink O S F N) :=
  ⟨seamLayer_GSF Rw V vlink N hN circ, faceLayer_GSF Rw V vlink O olink N hN circ,
    ⟨seamFacesLink_GSF Rw V vlink O olink N hN circ⟩⟩

/-- The frozen statement `stub_exists_seams_faces` verbatim (with the unused `clink`). -/
example (Rw : FC39RowsV2 W E)
    (V : VertexLayer W) (vlink : VertexModelLink Rw V)
    (circ : CircleRegion W) (_clink : CircleRestrictionLink Rw.circle circ)
    (O : PortLayer W E V) (olink : PortModelLink Rw vlink O)
    (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier)
    (hN : SharedSafe Rw N) :
    ∃ S : SeamLayer W V circ,
    ∃ F : FaceLayer W E V S O,
      Nonempty (SeamFacesLink Rw V vlink O S F N) :=
  exists_seams_faces_GSF Rw V vlink circ O olink N hN

end GC.GraphManifold.Assembly.FC39P0
