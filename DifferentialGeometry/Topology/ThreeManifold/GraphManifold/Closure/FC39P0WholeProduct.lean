import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport

/-!
# FC39 producer, GROUP G-product (review 56, D56-5): the whole-product strong certificate

External review 56 (§4.2, disposition D56-5): `exists_certificate_of_product_strong` (frozen targets
T:160–168) is product geometry without any analytic premise; the whole-product shape (T:214–226)
proceeds after its three contract fixes of review 49 (F.8, §6.2): (1) the genuine EMPTY circle
region as output, (2) the correspondence of the two product ends with the numbering of `B`, (3) shape
and `RimProduct` on the SAME certificate. FC39-FIX2 revised the target accordingly
(`build-logs/scratch/FC39-FIX2/TargetsV2.lean`, `exists_certificate_of_product_shape_v2`) and proved
the end equivalence (`exists_productEndEquiv`) and `strongOfHandleCount`
(`FC39P0FixProduct.lean`); no whole-product certificate existed in the tree. It is constructed here,
for ANY nearly cuspidal boundary `B` of `W` and ANY diffeomorphism
`e : annulus × S¹ ≃ₘ W`:

* `wholeProductPiece e` — the piece `annulus × S¹` mapped by `e` (an embedding, image all of `W`);
  the vertex `wholeProductVertex e = .cuspCore (wholeProductPiece e) ι` with the product parameter
  `ι = annulusCircleCarrierDiffeomorphTorusInterval.symm` (FC42 B13); its model boundary image is
  `∂W` (`wholeProductVertex_boundaryImage`); the end `b` of its product is the end torus
  `e '' doubleCuspBoundary (if b then 1 else 0)` (`wholeProductVertex_end`);
* `wholeProductPorts B e` — the ports: the product boundary tori `productBoundaryTori 2` transported
  by `e` and renumbered by the partition equivalence with `B.component`, so that the port `i` IS the
  component `B.component i` (`wholeProductPorts_range`);
* `wholeProductCertificate B e` — one cusp-core vertex covering `W`, the canonical empty circle region
  `CircleRegion.empty W`, the faces `Fin B.count` with face `i` the port torus `i` of kind
  `.external i`, owned by the vertex; no handles, edge circles, seams, arcs or loops;
  `wholeProductStrongCertificate B e` — the same certificate with its (vacuous) rim-product clause.

Main theorems: **`exists_certificate_of_product_shape_v2`** (the revised shape of FC39-FIX2,
proved), **`exists_certificate_of_product_strong`** (T:160–168, verbatim) and
`exists_certificate_of_product_shape` (T:214–226, verbatim), both from the revised shape.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## Boundary tori: torus images, renumbering -/

/-- The boundary torus `i` lies in the collar target `i`. -/
theorem boundaryTori_torusMap_mem_target_GI {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)
    (i : Fin n) (t : Torus) : T.torusMap i t ∈ (T.collar i).target :=
  (T.collar i).map_source (by
    rw [T.source_eq]
    change (0 : ℝ) < 1
    norm_num)

/-- Distinct boundary tori are disjoint. -/
theorem boundaryTori_range_disjoint_GI {C : CompactCarrier.{u}} {n : ℕ} (T : BoundaryTori C n)
    {i j : Fin n} (hij : i ≠ j) : Disjoint (range (T.torusMap i)) (range (T.torusMap j)) :=
  (T.disjoint hij).mono (range_subset_iff.2 (boundaryTori_torusMap_mem_target_GI T i))
    (range_subset_iff.2 (boundaryTori_torusMap_mem_target_GI T j))

/-- A family of boundary tori renumbered by an equivalence of the indices. -/
def boundaryToriReindex {C : CompactCarrier.{u}} {m n : ℕ} (T : BoundaryTori C n)
    (τ : Fin m ≃ Fin n) : BoundaryTori C m where
  collar i := T.collar (τ i)
  source_eq i := T.source_eq (τ i)
  boundary_zero i := T.boundary_zero (τ i)
  disjoint _ _ hij := T.disjoint (τ.injective.ne hij)

theorem boundaryToriReindex_torusMap {C : CompactCarrier.{u}} {m n : ℕ} (T : BoundaryTori C n)
    (τ : Fin m ≃ Fin n) (i : Fin m) : (boundaryToriReindex T τ).torusMap i = T.torusMap (τ i) :=
  rfl

/-! ## The product ports -/

variable {W : CompactCarrier.{u}}

/-- The product boundary tori of `annulus × S¹`, transported to `W` by `e`. -/
def productPortsTransport
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    BoundaryTori W 2 :=
  (productBoundaryTori.{u} 2 (Or.inl rfl)).transport e

/-- The transported product tori exhaust `∂W`. -/
theorem productPortsTransport_image
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    (productPortsTransport e).image = W.model.boundary W.Carrier := by
  rw [← Diffeomorph.image_boundary (by simp) e]
  have h : annulusCircleCarrier.{u}.model.boundary annulusCircleCarrier.{u}.Carrier =
      (productBoundaryTori.{u} 2 (Or.inl rfl)).image :=
    productBoundary_eq.{u} 2 (Or.inl rfl)
  rw [h]
  simp only [BoundaryTori.image]
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, rfl⟩ := mem_iUnion.1 hx
    exact ⟨_, mem_iUnion.2 ⟨i, y, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, y, rfl⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨i, y, rfl⟩

/-- The components of `B` are the transported product tori, under an equivalence of numberings. -/
theorem exists_productPortsEquiv {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ τ : Fin B.count ≃ Fin 2,
      ∀ i, B.component i = range ((productPortsTransport e).torusMap (τ i)) :=
  finite_connected_partitions_equiv B.component
    (fun j => range ((productPortsTransport e).torusMap j)) B.connected
    (fun j => isConnected_range ((productPortsTransport e).torusMap_smooth j).continuous)
    B.closed
    (fun j => (isCompact_range ((productPortsTransport e).torusMap_smooth j).continuous).isClosed)
    B.disjoint (fun _ _ hij => boundaryTori_range_disjoint_GI _ hij)
    (B.covers.trans (productPortsTransport_image e).symm)

/-- The renumbering of the product ports by `B` (a choice of the equivalence above). -/
def productPortsEquiv {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    Fin B.count ≃ Fin 2 :=
  Classical.choose (exists_productPortsEquiv B e)

/-- **The ports of the whole product, numbered by `B`.** -/
def wholeProductPorts {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    BoundaryTori W B.count :=
  boundaryToriReindex (productPortsTransport e) (productPortsEquiv B e)

/-- **The port `i` is the component `i` of `B`.** -/
theorem wholeProductPorts_range {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier)
    (i : Fin B.count) : range ((wholeProductPorts B e).torusMap i) = B.component i :=
  (Classical.choose_spec (exists_productPortsEquiv B e) i).symm

/-- The ports exhaust `∂W`. -/
theorem wholeProductPorts_image {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    (wholeProductPorts B e).image = W.model.boundary W.Carrier := by
  change (⋃ i, range ((wholeProductPorts B e).torusMap i)) = _
  simp only [wholeProductPorts_range]
  exact B.covers

/-! ## The whole-product vertex -/

/-- **The whole product as an embedded piece**: `annulus × S¹` mapped by `e`. -/
def wholeProductPiece
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    PieceEmbedding W where
  Piece := annulusCircleCarrier.{u}.Carrier
  topology := annulusCircleCarrier.{u}.topology
  charts := annulusCircleCarrier.{u}.charts
  manifold := annulusCircleCarrier.{u}.smooth
  compact := annulusCircleCarrier.{u}.compact
  hausdorff := annulusCircleCarrier.{u}.hausdorff
  secondCountable := annulusCircleCarrier.{u}.secondCountable
  connected := connectedSpace_productSet (Or.inl rfl)
  map := e
  smooth := e.contMDiff
  mfderiv_bijective q := (e.mfderivToContinuousLinearEquiv (by simp) q).bijective
  injective := e.injective

theorem wholeProductPiece_range
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    range (wholeProductPiece e).map = univ :=
  e.surjective.range_eq

/-- **The whole-product vertex**: one cusp core, product parameter FC42 B13. -/
def wholeProductVertex
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    Vertex W :=
  .cuspCore (wholeProductPiece e) annulusCircleCarrierDiffeomorphTorusInterval.symm

theorem wholeProductVertex_image
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    (wholeProductVertex e).image = univ :=
  wholeProductPiece_range e

/-- The model boundary image of the whole-product vertex is `∂W`. -/
theorem wholeProductVertex_boundaryImage
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    (wholeProductVertex e).boundaryImage = W.model.boundary W.Carrier :=
  Diffeomorph.image_boundary (by simp) e

/-- **The ends of the vertex product are the end tori of `e`**: the end `j = 1` (resp. `0`) of
the product parameter of the whole-product vertex is `e '' doubleCuspBoundary j`. -/
theorem wholeProductVertex_end
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier)
    (j : Fin 2) :
    range (fun t : Torus => (wholeProductPiece e).map
        (annulusCircleCarrierDiffeomorphTorusInterval.{u}.symm (t, iccEnd (decide (j = 1))))) =
      e '' doubleCuspBoundary.{u} j := by
  have hb : (if j = 0 then (0 : unitInterval) else 1) = iccEnd (decide (j = 1)) := by
    fin_cases j <;> rfl
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨_, ?_, rfl⟩
    change (torusMonodromyPolarDiffeomorph.{u}
      (torusMonodromyPolarDiffeomorph.{u}.symm (t, iccEnd (decide (j = 1))))).2 =
        if j = 0 then 0 else 1
    rw [Diffeomorph.apply_symm_apply, hb]
  · rintro ⟨y, hy, rfl⟩
    change (torusMonodromyPolarDiffeomorph.{u} y).2 = if j = 0 then 0 else 1 at hy
    rw [hb] at hy
    refine ⟨(torusMonodromyPolarDiffeomorph.{u} y).1, ?_⟩
    change e (torusMonodromyPolarDiffeomorph.{u}.symm
      ((torusMonodromyPolarDiffeomorph.{u} y).1, iccEnd (decide (j = 1)))) = e y
    rw [← hy, Prod.mk.eta]
    exact congrArg e (torusMonodromyPolarDiffeomorph.{u}.symm_apply_apply y)

/-! ## The whole-product certificate -/

/-- **The whole-product certificate**: one cusp-core vertex covering `W`, the empty circle region,
the two ports numbered by `B` as the two external faces, all families empty. -/
def wholeProductCertificate {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    DecompositionCertificate W (wholeProductPorts B e) where
  external_exhausted := (wholeProductPorts_image B e).symm
  vertexCount := 1
  vertex _ := wholeProductVertex e
  handleCount := 0
  handle h := h.elim0
  edgeCircleCount := 0
  edgeCircle c := c.elim0
  circ := CircleRegion.empty W
  cover := by
    refine eq_univ_of_forall fun x => Or.inl (Or.inl (Or.inl (mem_iUnion.2 ⟨0, ?_⟩)))
    rw [wholeProductVertex_image]
    exact mem_univ x
  vertex_disjoint k k' hkk' := (hkk' (Subsingleton.elim k k')).elim
  handle_disjoint h := h.elim0
  edgeCircle_disjoint c := c.elim0
  vertex_handle_disjoint _ h := h.elim0
  edgeCircle_vertex_disjoint c := c.elim0
  edgeCircle_handle_disjoint c := c.elim0
  circ_vertex_disjoint _ := by
    rw [CircleRegion.empty_region, interior_empty]
    exact empty_disjoint _
  circ_handle_disjoint h := h.elim0
  circ_edgeCircle_disjoint c := c.elim0
  vertical_fibre h := h.elim0
  edgeCircle_vertical c := c.elim0
  torusSeamCount := 0
  torusSeam c := c.elim0
  torusSide c := c.elim0
  torusSide_neg c := c.elim0
  torusSide_pos c := c.elim0
  torusSeam_disjoint c := c.elim0
  sphereSeamCount := 0
  sphereSeam c := c.elim0
  sphereSide c := c.elim0
  sphereSide_neg c := c.elim0
  sphereSide_pos c := c.elim0
  sphereSeam_disjoint c := c.elim0
  sphere_torus_seam_disjoint c := c.elim0
  externalOwner _ := 0
  external_owned _ := by
    rw [wholeProductVertex_image]
    exact subset_univ _
  faceCount := B.count
  face i := range ((wholeProductPorts B e).torusMap i)
  faceOwner _ := 0
  faceModel i := Sum.inr ((wholeProductPorts B e).torusMap_isEmbedding i).toHomeomorph.symm
  face_exhausted k := by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change (⋃ (i : Fin B.count) (_ : (0 : Fin 1) = 0), range ((wholeProductPorts B e).torusMap i)) =
      (wholeProductVertex e).boundaryImage
    rw [wholeProductVertex_boundaryImage, ← wholeProductPorts_image B e]
    simp only [iUnion_true]
    rfl
  faceKind i := .external i
  face_disjoint _ _ hne _ _ := boundaryTori_range_disjoint_GI _ hne
  face_external f i h := by
    cases h
    exact ⟨rfl, rfl⟩
  external_face i := ⟨i, rfl⟩
  face_torusSeam _ c := c.elim0
  torusSeam_face c := c.elim0
  face_sphereSeam _ c := c.elim0
  sphereSeam_face c := c.elim0
  handleEnd h := h.elim0
  handleFace h := h.elim0
  handleFace_owner h := h.elim0
  handleFace_kind h := h.elim0
  handleEnd_face h := h.elim0
  endDisk_disjoint h := h.elim0
  arcFaceCount := 0
  arcFace a := a.elim0
  arcOwner a := a.elim0
  arcOwner_kind a := a.elim0
  arcBase a := a.elim0
  arcBase_embedding a := a.elim0
  arcFace_eq a := a.elim0
  arcDefining a := a.elim0
  arcBase_defining a := a.elim0
  arcAnnulus a := a.elim0
  arcAnnulus_continuous a := a.elim0
  arcAnnulus_injective a := a.elim0
  arcAnnulus_range a := a.elim0
  arcAnnulus_proj a := a.elim0
  loopFaceCount := 0
  loopFace l := l.elim0
  loopOwner l := l.elim0
  loopOwner_kind l := l.elim0
  loopBase l := l.elim0
  loopBase_embedding l := l.elim0
  loopFace_eq l := l.elim0
  loopDefining l := l.elim0
  loopBase_defining l := l.elim0
  loopFace_closed l := l.elim0
  loopFace_nonempty l := l.elim0
  arcFace_disjoint a := a.elim0
  loopFace_disjoint l := l.elim0
  arc_loop_disjoint a := a.elim0
  face_partition _ hf := by cases hf
  face_region_inter _ hf := by cases hf
  handleArc h := h.elim0
  handleArc_owner h := h.elim0
  handleArc_meets h := h.elim0
  endDisk_loop_disjoint h := h.elim0
  endDisk_rim h := h.elim0
  arcEnd a := a.elim0
  arcEnd_arc a := a.elim0
  arcEnd_injective a := a.elim0
  arcEnd_surjective h := h.elim0
  arcAnnulus_end a := a.elim0
  handleCorner h := h.elim0
  handleCorner_bijective := ⟨fun a _ _ => a.1.elim0, fun c => c.elim0⟩
  arcBase_end a := a.elim0
  rimChart h := h.elim0
  rim_source h := h.elim0
  rim_proj h := h.elim0
  rim_vertex h := h.elim0
  rim_handle h := h.elim0
  rim_region h := h.elim0
  rim_label h := h.elim0
  rim_disjoint h := h.elim0
  external_region_disjoint _ := by
    rw [CircleRegion.empty_region]
    exact disjoint_empty _
  external_handle_disjoint _ h := h.elim0
  external_edgeCircle_disjoint _ c := c.elim0
  external_torusSeam_disjoint _ c := c.elim0
  external_sphereSeam_disjoint _ c := c.elim0
  rim_external_disjoint h := h.elim0
  rim_torusSeam_disjoint h := h.elim0
  rim_sphereSeam_disjoint h := h.elim0
  sphereSeam_region_disjoint c := c.elim0
  sphereSeam_handle_disjoint c := c.elim0

/-- **The whole-product strong certificate**: the same certificate with its (vacuous) rim-product
clause. -/
def wholeProductStrongCertificate {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    StrongCertificate W (wholeProductPorts B e) :=
  strongOfHandleCount (wholeProductCertificate B e) rfl

theorem wholeProductStrongCertificate_val {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    (wholeProductStrongCertificate B e).1 = wholeProductCertificate B e :=
  rfl

/-- The external face `i` of the whole-product certificate is the component `i` of `B`. -/
theorem wholeProductCertificate_face {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier)
    (i : Fin B.count) : (wholeProductCertificate B e).face i = B.component i :=
  wholeProductPorts_range B e i

/-- **The numbering of the two ends by `B` on the certificate itself**: under `σ`, the component
`i` of `B` is the end torus `e '' doubleCuspBoundary (σ i)` of the given product, it is the
external face `i` (= the port `i`) of the whole-product certificate, and it is the end
`σ i = 1` of the product parameter of its one cusp-core vertex. -/
theorem wholeProductCertificate_ends {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ σ : Fin B.count ≃ Fin 2, ∀ i,
      B.component i = e '' doubleCuspBoundary.{u} (σ i) ∧
      (wholeProductCertificate B e).face i = B.component i ∧
      B.component i = range (fun t : Torus => (wholeProductPiece e).map
        (annulusCircleCarrierDiffeomorphTorusInterval.{u}.symm (t, iccEnd (decide (σ i = 1))))) := by
  obtain ⟨σ, hσ⟩ := exists_productEndEquiv B e
  exact ⟨σ, fun i => ⟨hσ i, wholeProductCertificate_face B e i,
    (hσ i).trans (wholeProductVertex_end e (σ i)).symm⟩⟩

/-! ## The revised shape and the frozen targets -/

/-- **The revised whole-product shape (review 49 F.8 / review 56 D56-5, three points)** — the
target `exists_certificate_of_product_shape_v2` of FC39-FIX2, PROVED: `B` has two components,
numbered against the two ends of the GIVEN product `e` by `σ`; the ports numbered by `B`; ONE strong
certificate whose underlying certificate has the canonical empty circle region, one cusp-core vertex
covering `W`, two external faces and empty families. -/
theorem exists_certificate_of_product_shape_v2 {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    B.count = 2 ∧
    ∃ σ : Fin B.count ≃ Fin 2, (∀ i, B.component i = e '' doubleCuspBoundary.{u} (σ i)) ∧
    ∃ E : BoundaryTori W B.count, (∀ i, range (E.torusMap i) = B.component i) ∧
    ∃ D : StrongCertificate W E,
      D.1.circ = CircleRegion.empty W ∧ D.1.vertexCount = 1 ∧
      (∀ k, ∃ P eP, D.1.vertex k = .cuspCore P eP ∧ range P.map = univ) ∧
      D.1.faceCount = 2 ∧ (∀ f, ∃ i, D.1.faceKind f = .external i) ∧
      D.1.handleCount = 0 ∧ D.1.edgeCircleCount = 0 ∧ D.1.torusSeamCount = 0 ∧
      D.1.sphereSeamCount = 0 ∧ D.1.arcFaceCount = 0 ∧ D.1.loopFaceCount = 0 := by
  obtain ⟨σ, hσ⟩ := exists_productEndEquiv B e
  exact ⟨count_eq_two_of_productDiffeomorph B e, σ, hσ, wholeProductPorts B e,
    wholeProductPorts_range B e, wholeProductStrongCertificate B e, rfl, rfl,
    fun _ => ⟨_, _, rfl, wholeProductPiece_range e⟩, count_eq_two_of_productDiffeomorph B e,
    fun f => ⟨f, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **(5) `exists_certificate_of_product_strong` (frozen T:160–168, verbatim)**, from the revised
shape (the same certificate). -/
theorem exists_certificate_of_product_strong
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier
      ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    ∃ E : BoundaryTori W B.count,
      Nonempty {D : DecompositionCertificate W E // D.RimProduct} ∧
      (∀ i, Set.range (E.torusMap i) = B.component i) := by
  obtain ⟨-, -, -, E, hE, D, -⟩ := exists_certificate_of_product_shape_v2 B e
  exact ⟨E, ⟨D⟩, hE⟩

/-- **The old whole-product shape (frozen T:214–226, verbatim)**, from the revised one. -/
theorem exists_certificate_of_product_shape
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ)
    (e : annulusCircleCarrier.{u}.Carrier
      ≃ₘ⟮annulusCircleCarrier.{u}.model, W.model⟯ W.Carrier) :
    B.count = 2 ∧ ∃ E : BoundaryTori W B.count, ∃ D : DecompositionCertificate W E,
      D.vertexCount = 1 ∧ (∀ k, ∃ P eP, D.vertex k = .cuspCore P eP ∧ range P.map = univ) ∧
      D.faceCount = 2 ∧ (∀ f, ∃ i, D.faceKind f = .external i) ∧
      D.handleCount = 0 ∧ D.edgeCircleCount = 0 ∧ D.torusSeamCount = 0 ∧
      D.sphereSeamCount = 0 ∧ D.arcFaceCount = 0 ∧ D.loopFaceCount = 0 ∧
      D.circ.cornerCount = 0 ∧ (∀ i, Set.range (E.torusMap i) = B.component i) := by
  obtain ⟨h2, -, -, E, hE, D, hcirc, hV, hk, hF, hf, hH, hEC, hT, hS, hA, hL⟩ :=
    exists_certificate_of_product_shape_v2 B e
  refine ⟨h2, E, D.1, hV, hk, hF, hf, hH, hEC, hT, hS, hA, hL, ?_, hE⟩
  rw [hcirc]
  rfl

end GC.GraphManifold.Assembly.FC39P0
