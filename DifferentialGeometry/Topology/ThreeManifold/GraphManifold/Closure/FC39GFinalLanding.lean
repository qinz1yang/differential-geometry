import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesExist
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcLayer

/-!
# FC39 GROUP G: the final landing modulo the adapted edge–rim data (lane FC39-G-FINAL, G2)

The final assembly of `FC39GFinalAssembly.lean` with three of its four remaining arguments now
DELIVERED:

* seams / faces — `exists_seams_faces_GSF` (lane FC39-G-SF; the unused `clink` of the frozen
  `T:289–299` is dropped there, so it enters through the one-line adapter
  `fun Rw V vlink circ _ O olink N hN => exists_seams_faces_GSF Rw V vlink circ O olink N hN`);
* global face functions V2 — `exists_globalFaceFunctions_GGFF` (lane FC39-G-GFF);
* arcs V2 — `stub_exists_arcLayer_GARC` (lane FC39-G-ARC).

The only explicit argument left is the frozen V2 adapted statement `stubV2_exists_adaptedEdgeRimData`
(lane FC39-G-RIMBOX, `exists_adaptedEdgeRimDataV2_GRIM`):

* `strongCertificate_of_adapted_GFIN` — from the rows;
* `strongCertificate_of_prepared_adapted_GFIN` — the frozen V2 final target
  `stubV2_exists_strongCertificate (Pr)`;
* `strongCertificate_of_adapted_V1_GFIN` — the frozen V1 final target `T:369–371` (via
  `FC39Prepared.toV2`).

The pointwise form takes the adapted DATA of one prepared row package and its safe neighbourhoods:

* `strongCertificateOfAdapted_GFIN Pr safe A` — the certificate whose vertex / port layers, seams,
  faces and arcs are produced by the delivered theorems, the handle-end layer computed from the labels,
  the rim region and cover / vertical / protection computed inside the assembler; its circle region,
  handles and rim charts ARE those of `A` (definitional: `_circ`, `_handle`, `_rimChart`,
  `_handleCount`);
* `strongCertificate_of_adapted_at_GFIN` — its existence form.
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

/-! ## The landing modulo the adapted statement -/

/-- **GROUP G final landing from the rows, modulo the adapted edge–rim data V2** (the only
remaining argument, `stubV2_exists_adaptedEdgeRimData`): seams / faces, global face functions V2 and
arcs V2 are the delivered theorems. -/
theorem strongCertificate_of_adapted_GFIN (Rw : FC39RowsV2 W E)
    (hA : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe)) :
    Nonempty (StrongCertificate W E) :=
  strongCertificate_of_remaining_layers_GFIN Rw
    (fun Rw V vlink circ _ O olink N hN => exists_seams_faces_GSF Rw V vlink circ O olink N hN)
    exists_globalFaceFunctions_GGFF hA stub_exists_arcLayer_GARC

/-- **The frozen V2 final target `stubV2_exists_strongCertificate (Pr)`** modulo the adapted
edge–rim data V2. -/
theorem strongCertificate_of_prepared_adapted_GFIN (Pr : FC39PreparedV2 W E)
    (hA : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe)) :
    Nonempty (StrongCertificate W E) :=
  strongCertificate_of_prepared_remaining_layers_GFIN Pr
    (fun Rw V vlink circ _ O olink N hN => exists_seams_faces_GSF Rw V vlink circ O olink N hN)
    hA stub_exists_arcLayer_GARC

/-- **The frozen V1 final target `stub_exists_strongCertificate (Pr : FC39Prepared W E)`
(`T:369–371`)** modulo the adapted edge–rim data V2 (through `FC39Prepared.toV2`). -/
theorem strongCertificate_of_adapted_V1_GFIN (Pr : FC39Prepared W E)
    (hA : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe)) :
    Nonempty (StrongCertificate W E) :=
  strongCertificate_of_remaining_layers_V1_GFIN Pr
    (fun Rw V vlink circ _ O olink N hN => exists_seams_faces_GSF Rw V vlink circ O olink N hN)
    hA stub_exists_arcLayer_GARC

/-! ## The pointwise form: the certificate of given adapted data -/

/-- **The certificate of given adapted data.** For a prepared row package `Pr`, safe neighbourhoods
`safe` and adapted data `A` over them: the vertex and port layers (`exists_vertexLayer_portLayer_G1`),
the seams and faces on `(V, O, A.circ, safe.shared)` (`exists_seams_faces_GSF`), the handle-end
layer of the labels and the arc layer of THAT layer (`stub_exists_arcLayer_GARC`), assembled by
`strongCertificateOfRemainingLabelled_GFIN`. -/
def strongCertificateOfAdapted_GFIN (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe) :
    StrongCertificate W E :=
  let hVO := exists_vertexLayer_portLayer_G1 Pr.rows
  let V := hVO.choose
  let vlink := hVO.choose_spec.choose
  let O := hVO.choose_spec.choose_spec.choose
  let hSF := exists_seams_faces_GSF Pr.rows V vlink A.circ O
    hVO.choose_spec.choose_spec.choose_spec safe.shared safe.shared_safe
  let S := hSF.choose
  let F := hSF.choose_spec.choose
  let sf := hSF.choose_spec.choose_spec.some
  strongCertificateOfRemainingLabelled_GFIN Pr.rows Pr.globalFaces safe V vlink O A S F sf
    (stub_exists_arcLayer_GARC Pr safe A V vlink O S F sf (A.handleEndLayer_GHR vlink sf)).some

/-- The circle region of the certificate of `A` is the circle region of `A`. -/
theorem strongCertificateOfAdapted_GFIN_circ (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe) :
    (strongCertificateOfAdapted_GFIN Pr safe A).1.circ = A.circ :=
  rfl

/-- The certificate of `A` has the handles of `A`. -/
theorem strongCertificateOfAdapted_GFIN_handleCount (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe) :
    (strongCertificateOfAdapted_GFIN Pr safe A).1.handleCount = A.edges.handleCount :=
  rfl

/-- Every handle of the certificate of `A` is the handle of `A`. -/
theorem strongCertificateOfAdapted_GFIN_handle (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) :
    (strongCertificateOfAdapted_GFIN Pr safe A).1.handle h = A.edges.handle h :=
  rfl

/-- Every rim chart of the certificate of `A` is the rim chart of `A`. -/
theorem strongCertificateOfAdapted_GFIN_rimChart (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (strongCertificateOfAdapted_GFIN Pr safe A).1.rimChart h b = A.rims.rimChart h b :=
  rfl

/-- **Whole preimages.** Every handle of the certificate of `A` is the WHOLE inverse image of the
base component of its labelled registration. -/
theorem strongCertificateOfAdapted_GFIN_handle_whole (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) :
    range ((strongCertificateOfAdapted_GFIN Pr safe A).1.handle h).map =
      Pr.rows.edge.wholeComponent
        (Pr.rows.edgeModels.componentEquiv (.inl (A.labelled.edgeLink.handleEquiv h))) := by
  rw [strongCertificateOfAdapted_GFIN_handle, A.components_eq]
  exact A.components.handle_whole h

/-- **The existence form of the pointwise landing**: given adapted data over some safe
neighbourhoods of a prepared row package, the strong certificate exists. -/
theorem strongCertificate_of_adapted_at_GFIN (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe) :
    Nonempty (StrongCertificate W E) :=
  ⟨strongCertificateOfAdapted_GFIN Pr safe A⟩

end GC.GraphManifold.Assembly.FC39P0
