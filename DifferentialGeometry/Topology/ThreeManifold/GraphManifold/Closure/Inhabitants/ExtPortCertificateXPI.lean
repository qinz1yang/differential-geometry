import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortAdaptedXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalLanding

/-!
# FC39 external-port regression instance: the strong certificate through the GENERAL chain

External review 63 (D63-7), 67 (D67-6 (b)/(c)): one end-to-end run of the GROUP G route on the
external-port rows `extportRowsW_XPI` — GENERAL GFF (`exists_globalFaceFunctions_GGFF`) → prepared
rows → GENERAL SAFE (`exists_safeNeighbourhoods_GSAFE`) → adapted data V2 over THAT `GF` and THAT
`safe` (`extportAdapted_XPI`, empty edge / rim families) → the pointwise landing
`strongCertificateOfAdapted_GFIN` (general vertex / port layers, seams / faces, handle ends, arcs on
the same `GF` / `safe` / `A`) → the strong certificate.

* `extportCertificate_XPI : StrongCertificate carrierW_XPI portsE_XPI`, existence
  `extport_exists_strongCertificate_XPI`; the same for EVERY `GF` and `safe`
  (`exists_strongCertificate_of_globalFaces_XPI`);
* regression: the certificate's circle region IS the region of the adapted data built over the
  general `GF` (definitional), its defining functions ARE `GF.fn` through `ι = val`, its region is
  `3/2 ≤ rad ≤ 2`; three vertices, one torus seam, no sphere seam, six faces, no handle, no arc,
  both ports owned by different vertices.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-! ## The general chain on the instance -/

/-- The global face functions of the instance: the GENERAL GFF output. -/
def extportGF_XPI : GlobalFaceFunctionsV2 extportRowsW_XPI :=
  exists_globalFaces_XPI.some

/-- The prepared rows of the instance over the general GFF output. -/
def extportPrepared_XPI : FC39PreparedV2 carrierW_XPI portsE_XPI :=
  preparedOf_XPI extportGF_XPI

/-- The safe neighbourhoods of the instance: the GENERAL SAFE output. -/
def extportSafe_XPI : ProducerSafeNeighbourhoods extportRowsW_XPI :=
  exists_safe_XPI.some

/-- The adapted data V2 over the general `GF` and the general `safe`. -/
def extportAdaptedG_XPI : AdaptedEdgeRimDataV2 extportPrepared_XPI extportSafe_XPI :=
  extportAdapted_XPI extportGF_XPI extportSafe_XPI

/-- **The strong certificate of the external-port instance** (pointwise landing
`strongCertificateOfAdapted_GFIN`). -/
def extportCertificate_XPI : StrongCertificate carrierW_XPI portsE_XPI :=
  strongCertificateOfAdapted_GFIN extportPrepared_XPI extportSafe_XPI extportAdaptedG_XPI

/-- **`T² × I` with two ports has a strong certificate**, through the general GROUP G chain. -/
theorem extport_exists_strongCertificate_XPI : Nonempty (StrongCertificate carrierW_XPI portsE_XPI) :=
  ⟨extportCertificate_XPI⟩

/-- The landing works over EVERY global face family and EVERY safe family of the instance. -/
theorem exists_strongCertificate_of_globalFaces_XPI (GF : GlobalFaceFunctionsV2 extportRowsW_XPI)
    (safe : ProducerSafeNeighbourhoods extportRowsW_XPI) :
    Nonempty (StrongCertificate carrierW_XPI portsE_XPI) :=
  strongCertificate_of_adapted_at_GFIN (preparedOf_XPI GF) safe (extportAdapted_XPI GF safe)

/-! ## Regression -/

/-- The certificate's circle region IS the region of the adapted data over the general `GF`. -/
theorem extportCertificate_circ_XPI :
    extportCertificate_XPI.1.circ = extportCirc_XPI extportGF_XPI :=
  strongCertificateOfAdapted_GFIN_circ _ _ _

/-- The base of the certificate's circle region is the base of the general `GF`. -/
theorem extportCertificate_base_XPI : extportCertificate_XPI.1.circ.Base = extportGF_XPI.base :=
  rfl

/-- The certificate's defining functions ARE the general global face functions through `ι = val`
(one label system passed through). -/
theorem extportCertificate_defining_XPI (l : Fin 2) (c : extportGF_XPI.base) :
    extportCertificate_XPI.1.circ.defining l c = extportGF_XPI.fn (faceIdx_XPI extportGF_XPI l) c.val :=
  rfl

/-- The face of the defining function `l` is the labelled circle face `l` (`0` the new slim end,
`1` the outer cusp face). -/
theorem extportCertificate_faceOfDefining_XPI (l : Fin 2) :
    (extportFaceLink_XPI extportGF_XPI).faceOfDefining l = circleFaceEquiv_XPI l :=
  actualFace_faceIdx_XPI extportGF_XPI l

/-- Two defining functions, no corner. -/
theorem extportCertificate_counts_XPI :
    extportCertificate_XPI.1.circ.definingCount = 2 ∧ extportCertificate_XPI.1.circ.cornerCount = 0 :=
  ⟨rfl, rfl⟩

/-- The certificate's circle region is `3/2 ≤ rad ≤ 2`. -/
theorem extportCertificate_region_XPI :
    extportCertificate_XPI.1.circ.region = {x | 3 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 2} :=
  (extportCircLink_XPI extportGF_XPI).region_eq.trans extportCircle_region_XPI

/-- No handle, no edge circle. -/
theorem extportCertificate_handles_XPI :
    extportCertificate_XPI.1.handleCount = 0 ∧ extportCertificate_XPI.1.edgeCircleCount = 0 :=
  ⟨rfl, rfl⟩

/-- Three vertices. -/
theorem extportCertificate_vertexCount_XPI : extportCertificate_XPI.1.vertexCount = 3 :=
  vertexCount_XPI (exists_vertexLayer_portLayer_G1 extportRowsW_XPI).choose_spec.choose

/-- The seams and faces of the certificate: one torus seam, no sphere seam, six faces. -/
theorem extportCertificate_seams_faces_XPI :
    extportCertificate_XPI.1.torusSeamCount = 1 ∧ extportCertificate_XPI.1.sphereSeamCount = 0 ∧
      extportCertificate_XPI.1.faceCount = 6 := by
  let hVO := exists_vertexLayer_portLayer_G1 extportRowsW_XPI
  let hSF := exists_seams_faces_GSF extportRowsW_XPI hVO.choose hVO.choose_spec.choose
    extportAdaptedG_XPI.circ hVO.choose_spec.choose_spec.choose
    hVO.choose_spec.choose_spec.choose_spec extportSafe_XPI.shared extportSafe_XPI.shared_safe
  exact ⟨torusSeamCount_XPI hSF.choose_spec.choose_spec.some,
    sphereSeamCount_XPI hSF.choose_spec.choose_spec.some,
    faceCount_XPI hSF.choose_spec.choose_spec.some⟩

/-- The two ports are owned by different vertices of the certificate. -/
theorem extportCertificate_ports_XPI :
    extportCertificate_XPI.1.externalOwner 0 ≠ extportCertificate_XPI.1.externalOwner 1 := by
  let hVO := exists_vertexLayer_portLayer_G1 extportRowsW_XPI
  intro h
  have h2 := congrArg hVO.choose_spec.choose.index h
  change hVO.choose_spec.choose.index (hVO.choose_spec.choose_spec.choose.externalOwner 0) =
    hVO.choose_spec.choose.index (hVO.choose_spec.choose_spec.choose.externalOwner 1) at h2
  rw [hVO.choose_spec.choose_spec.choose_spec.owner_index,
    hVO.choose_spec.choose_spec.choose_spec.owner_index] at h2
  simp at h2

/-- A certificate without handles has no arc face (every arc has two ends at handle ends). -/
theorem arcFaceCount_eq_zero_of_handleCount_XPI {W : CompactCarrier} {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hH : D.handleCount = 0) : D.arcFaceCount = 0 := by
  by_contra hne
  exact (Fin.cast hH (D.arcEnd ⟨0, Nat.pos_of_ne_zero hne⟩ false).1).elim0

/-- No arc face. -/
theorem extportCertificate_arcFaceCount_XPI : extportCertificate_XPI.1.arcFaceCount = 0 :=
  arcFaceCount_eq_zero_of_handleCount_XPI _ extportCertificate_handles_XPI.1

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
