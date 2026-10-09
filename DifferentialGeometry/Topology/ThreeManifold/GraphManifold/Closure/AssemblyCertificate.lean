import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# Chapter-14 assembly: the FC39 decomposition certificate (VERSION 2)

`DecompositionCertificate W E` and its closed abbreviation `ClosedDecompositionCertificate W`,
moved VERBATIM from the frozen interface file V2 (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean`,
§1 lines 320–525; change log `docs/geometrization/chapter14/design-fc39-fc42-assembly-v2-changes-20261004.md`,
rows 15–20; review `docs/geometrization/chapter14/out/review-fc39-fc42-assembly.md` §3, dispositions D4,
D5, D14). The parts (vertices, edges, circle region, face kinds) live in
`AssemblyCertificateParts.lean`. One deviation from the V2 text, forced by the `explicitVarsOfIff`
linter: in the fields `rim_source`, `rim_vertex`, `rim_handle`, `rim_region` the point `p` is an
implicit binder (`∀ h b {p}, …`); the statements are otherwise identical.

VERSION 4 (defect D-CERT-1, review 39 §9.2): the V2 field `face_disjoint` (pairwise disjoint
ambient face images) contradicted `face_sphereSeam` + `sphereSeam_face` (the two sides of a sphere
seam are two distinct faces with the same nonempty image), so it forced `sphereSeamCount = 0`, and
likewise every torus seam to have the circle region on one side. Faces are now pairwise disjoint
EXCEPT the two opposite sides `(c, b)`, `(c, !b)` of one seam, whose images coincide.

Besides the two definitions:
* the closed wrapper: the projections `ClosedDecompositionCertificate.tori` / `.cert`, the
  constructor `DecompositionCertificate.toClosed`, and `ClosedDecompositionCertificate.boundary_eq_empty`
  (a closed certificate lives on a carrier with empty boundary);
* the empty circle region `CircleRegion.empty` (base `PEmpty`, domain `⊥`), whose cornered and rounded
  regions are empty — the circle region of a certificate without circle-region strata;
* `CircleRegion.region_subset_domain`, `CircleRegion.region_subset_interior` and the same for the
  rounded region.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **FC39 (mixed encoding), one certificate with external ports. VERSION 2.**
Changes against V1 (review item 3 table, items 7 and 10; D4, D5, D14):
* every disjointness clause has its own quantifier (V1 `circ_disjoint : ∀ k h e, A k ∧ B h ∧ C e`
  and the second half of `edgeCircle_disjoint` asserted nothing when one family was empty);
* the torus sides constrain the `none` side: that half collar lies in the circle region;
* seams are pairwise disjoint, torus and sphere seams are disjoint, and every seam side that is a
  vertex is a WHOLE face of that vertex (seam completeness);
* per-vertex model-boundary partition: faces (`face`, `faceOwner`, `faceModel`, `faceKind`) that
  partition `(vertex k).boundaryImage`; partitioned faces are cut into end disks, arcs and loops,
  with the circle-region intersection equality; arcs carry an embedded interval base, an annulus
  parametrization and the endpoint bijection with the two end disks they meet; loops carry an
  embedded circle base and meet no disk. These are the inputs of FC40
  (`Connected/DiskFaceDegree.lean:38–66`: closed faces, cover, disjointness, endpoint bijection,
  `hdisk` rim–region equality, `hann` annulus parametrization, `hbase`);
* genuine rim charts in `W` at every handle end, over the corner charts of the base (`rim_proj`),
  with the rim model membership and the rim label (the end disk whose rim is the centre circle);
* protection of ALL operation supports: the rounding supports (rim chart targets) and the sphere
  surgery supports (sphere seam collars) avoid every external collar, every whole torus seam
  collar and each other; external collars avoid all torus seam collars (`external_seam_disjoint`
  style, as B3 needs).
Families may be empty. -/
structure DecompositionCertificate (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  -- ports (BCP/BCG, BCF01–BCF03, B:9834–9884)
  external_exhausted : W.model.boundary W.Carrier = E.image
  -- vertices (ZSP02–ZSP05, LFR54, BCG06–BCG07)
  vertexCount : ℕ
  vertex : Fin vertexCount → Vertex W
  -- handles and circle-base edge pieces (EDP04–EDP06, FDC01–FDC02)
  handleCount : ℕ
  handle : Fin handleCount → EdgeHandle W
  edgeCircleCount : ℕ
  edgeCircle : Fin edgeCircleCount → EdgeCirclePiece W
  -- the circle region with the common rounding (FDC03, FDC04 ¶3)
  circ : CircleRegion W
  -- actual cover
  cover : (⋃ k, (vertex k).image) ∪ (⋃ h, range (handle h).map) ∪
      (⋃ e, range (edgeCircle e).piece.map) ∪ circ.region = univ
  -- disjoint ambient interiors, ONE quantifier per clause (V2, review item 3, D4)
  vertex_disjoint : Pairwise fun k k' =>
    Disjoint (interior (vertex k).image) (interior (vertex k').image)
  handle_disjoint : Pairwise fun h h' =>
    Disjoint (interior (range (handle h).map)) (interior (range (handle h').map))
  edgeCircle_disjoint : Pairwise fun e e' =>
    Disjoint (range (edgeCircle e).piece.map) (range (edgeCircle e').piece.map)
  vertex_handle_disjoint : ∀ k h,
    Disjoint (interior (vertex k).image) (interior (range (handle h).map))
  edgeCircle_vertex_disjoint : ∀ e k,
    Disjoint (interior (range (edgeCircle e).piece.map)) (interior (vertex k).image)
  edgeCircle_handle_disjoint : ∀ e h,
    Disjoint (interior (range (edgeCircle e).piece.map)) (interior (range (handle h).map))
  circ_vertex_disjoint : ∀ k, Disjoint (interior circ.region) (interior (vertex k).image)
  circ_handle_disjoint : ∀ h, Disjoint (interior circ.region) (interior (range (handle h).map))
  circ_edgeCircle_disjoint : ∀ e,
    Disjoint (interior circ.region) (interior (range (edgeCircle e).piece.map))
  -- vertical faces (EDP06): every rim circle of a handle slice is a WHOLE circle-region fibre
  vertical_fibre : ∀ h (t : Icc (0 : ℝ) 1), ∃ b : circ.Base,
    (fun x : ClosedCell 2 => (handle h).map (x, t)) '' diskRim =
      Subtype.val '' (circ.proj ⁻¹' {b})
  edgeCircle_vertical : ∀ e, (edgeCircle e).piece.map ''
      {q | (𝓡∂ 3).IsBoundaryPoint q} ⊆ circ.region
  -- whole torus seams; `none` = the circle region (V2: the `none` side is constrained)
  torusSeamCount : ℕ
  torusSeam : Fin torusSeamCount → TorusSeam W
  torusSide : Fin torusSeamCount → Bool → Option (Fin vertexCount)
  torusSide_neg : ∀ c t s, -1 < s → s ≤ 0 →
    (torusSeam c).collar (t, s) ∈ (torusSide c true).elim circ.region fun k => (vertex k).image
  torusSide_pos : ∀ c t s, 0 ≤ s → s < 1 →
    (torusSeam c).collar (t, s) ∈ (torusSide c false).elim circ.region fun k => (vertex k).image
  torusSeam_disjoint : Pairwise fun c d =>
    Disjoint (torusSeam c).collar.target (torusSeam d).collar.target
  -- whole sphere seams between two vertices
  sphereSeamCount : ℕ
  sphereSeam : Fin sphereSeamCount → SphereSeam W
  sphereSide : Fin sphereSeamCount → Bool → Fin vertexCount
  sphereSide_neg : ∀ c z s, s ≤ 0 → -1 < s →
    (sphereSeam c).collar (z, s) ∈ (vertex (sphereSide c true)).image
  sphereSide_pos : ∀ c z s, 0 ≤ s → s < 1 →
    (sphereSeam c).collar (z, s) ∈ (vertex (sphereSide c false)).image
  sphereSeam_disjoint : Pairwise fun c d =>
    Disjoint (sphereSeam c).collar.target (sphereSeam d).collar.target
  sphere_torus_seam_disjoint : ∀ c d,
    Disjoint (sphereSeam c).collar.target (torusSeam d).collar.target
  -- external ports: owner (a cusp core or a torus piece)
  externalOwner : Fin n → Fin vertexCount
  external_owned : ∀ i, (E.collar i).target ⊆ (vertex (externalOwner i)).image
  -- V2 (review item 3, D4): the per-vertex model-boundary partition into whole faces
  faceCount : ℕ
  face : Fin faceCount → Set W.Carrier
  faceOwner : Fin faceCount → Fin vertexCount
  faceModel : (f : Fin faceCount) →
    (face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕ (face f ≃ₜ Circle × Circle)
  face_exhausted : ∀ k, (⋃ (f : Fin faceCount) (_ : faceOwner f = k), face f) =
    (vertex k).boundaryImage
  faceKind : Fin faceCount → FaceKind n torusSeamCount sphereSeamCount
  -- V4 (D-CERT-1): disjoint unless the two faces are the opposite sides of one seam
  face_disjoint : ∀ f f', f ≠ f' →
    (∀ c b, ¬ (faceKind f = .sphereSeam c b ∧ faceKind f' = .sphereSeam c (!b))) →
    (∀ c b, ¬ (faceKind f = .torusSeam c b ∧ faceKind f' = .torusSeam c (!b))) →
    Disjoint (face f) (face f')
  face_external : ∀ f i, faceKind f = .external i →
    face f = range (E.torusMap i) ∧ externalOwner i = faceOwner f
  external_face : ∀ i, ∃ f, faceKind f = .external i
  face_torusSeam : ∀ f c b, faceKind f = .torusSeam c b →
    face f = range (fun t => (torusSeam c).collar (t, 0)) ∧ torusSide c b = some (faceOwner f)
  torusSeam_face : ∀ c b k, torusSide c b = some k →
    ∃ f, faceOwner f = k ∧ faceKind f = .torusSeam c b
  face_sphereSeam : ∀ f c b, faceKind f = .sphereSeam c b →
    face f = range (fun z => (sphereSeam c).collar (z, 0)) ∧ sphereSide c b = faceOwner f
  sphereSeam_face : ∀ c b, ∃ f, faceOwner f = sphereSide c b ∧ faceKind f = .sphereSeam c b
  -- handle ends: each end disk is a whole disk in ONE partitioned face (EDP06, FC40 input)
  handleEnd : Fin handleCount → Bool → Fin vertexCount
  handleFace : Fin handleCount → Bool → Fin faceCount
  handleFace_owner : ∀ h b, faceOwner (handleFace h b) = handleEnd h b
  handleFace_kind : ∀ h b, faceKind (handleFace h b) = .partitioned
  handleEnd_face : ∀ h b, (handle h).endDisk b ⊆ face (handleFace h b)
  endDisk_disjoint : ∀ h b h' b', (h, b) ≠ (h', b') →
    Disjoint ((handle h).endDisk b) ((handle h').endDisk b')
  -- circle-region faces of partitioned faces: arcs (two end disks) and loops (no disk)
  arcFaceCount : ℕ
  arcFace : Fin arcFaceCount → Set W.Carrier
  arcOwner : Fin arcFaceCount → Fin faceCount
  arcOwner_kind : ∀ j, faceKind (arcOwner j) = .partitioned
  arcBase : Fin arcFaceCount → Icc (0 : ℝ) 1 → circ.Base
  arcBase_embedding : ∀ j, IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (arcBase j)
  arcFace_eq : ∀ j, arcFace j = Subtype.val '' (circ.proj ⁻¹' range (arcBase j))
  arcDefining : Fin arcFaceCount → Fin circ.definingCount
  arcBase_defining : ∀ j t, circ.defining (arcDefining j) (arcBase j t) = 0
  arcAnnulus : Fin arcFaceCount →
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → W.Carrier
  arcAnnulus_continuous : ∀ j, Continuous (arcAnnulus j)
  arcAnnulus_injective : ∀ j, Injective (arcAnnulus j)
  arcAnnulus_range : ∀ j, range (arcAnnulus j) = arcFace j
  arcAnnulus_proj : ∀ j q, ∃ hx : arcAnnulus j q ∈ circ.domain,
    circ.proj ⟨arcAnnulus j q, hx⟩ = arcBase j q.2
  loopFaceCount : ℕ
  loopFace : Fin loopFaceCount → Set W.Carrier
  loopOwner : Fin loopFaceCount → Fin faceCount
  loopOwner_kind : ∀ j, faceKind (loopOwner j) = .partitioned
  loopBase : Fin loopFaceCount → Circle → circ.Base
  loopBase_embedding : ∀ j, IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (loopBase j)
  loopFace_eq : ∀ j, loopFace j = Subtype.val '' (circ.proj ⁻¹' range (loopBase j))
  loopDefining : Fin loopFaceCount → Fin circ.definingCount
  loopBase_defining : ∀ j z, circ.defining (loopDefining j) (loopBase j z) = 0
  loopFace_closed : ∀ j, IsClosed (loopFace j)
  loopFace_nonempty : ∀ j, (loopFace j).Nonempty
  arcFace_disjoint : Pairwise fun j j' => Disjoint (arcFace j) (arcFace j')
  loopFace_disjoint : Pairwise fun j j' => Disjoint (loopFace j) (loopFace j')
  arc_loop_disjoint : ∀ j j', Disjoint (arcFace j) (loopFace j')
  -- FC40 cover and circle-region intersection equality on every partitioned face
  face_partition : ∀ f, faceKind f = .partitioned →
    (⋃ (h : Fin handleCount) (b : Bool) (_ : handleFace h b = f), (handle h).endDisk b) ∪
      (⋃ (j : Fin arcFaceCount) (_ : arcOwner j = f), arcFace j) ∪
      (⋃ (j : Fin loopFaceCount) (_ : loopOwner j = f), loopFace j) = face f
  face_region_inter : ∀ f, faceKind f = .partitioned →
    face f ∩ circ.region = (⋃ (j : Fin arcFaceCount) (_ : arcOwner j = f), arcFace j) ∪
      (⋃ (j : Fin loopFaceCount) (_ : loopOwner j = f), loopFace j)
  -- disk–arc incidence, `hdisk` rim–region equality, endpoint bijection, `hann` ends
  handleArc : Fin handleCount → Bool → Fin arcFaceCount
  handleArc_owner : ∀ h b, arcOwner (handleArc h b) = handleFace h b
  handleArc_meets : ∀ h b j, ((handle h).endDisk b ∩ arcFace j).Nonempty → handleArc h b = j
  endDisk_loop_disjoint : ∀ h b j, Disjoint ((handle h).endDisk b) (loopFace j)
  endDisk_rim : ∀ h b, (fun x : ClosedCell 2 => (handle h).map (x, iccEnd b)) '' diskRim =
    (handle h).endDisk b ∩ arcFace (handleArc h b)
  arcEnd : Fin arcFaceCount → Bool → Fin handleCount × Bool
  arcEnd_arc : ∀ j e, handleArc (arcEnd j e).1 (arcEnd j e).2 = j
  arcEnd_injective : ∀ j, Injective (arcEnd j)
  arcEnd_surjective : ∀ h b, ∃ e, arcEnd (handleArc h b) e = (h, b)
  arcAnnulus_end : ∀ j e, (handle (arcEnd j e).1).endDisk (arcEnd j e).2 ∩ arcFace j =
    arcAnnulus j '' {q | q.2 = iccEnd e}
  -- V2 (review item 3, D4): corners = handle rims; genuine rim charts in `W`; rim model
  handleCorner : Fin handleCount → Bool → Fin circ.cornerCount
  handleCorner_bijective : Bijective fun hb : Fin handleCount × Bool => handleCorner hb.1 hb.2
  arcBase_end : ∀ j e, arcBase j (iccEnd e) =
    circ.cornerChart (handleCorner (arcEnd j e).1 (arcEnd j e).2) (0, 0)
  rimChart : Fin handleCount → Bool →
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞
  rim_source : ∀ h b {p}, p ∈ (rimChart h b).source ↔ p.2 ∈ rimBox 2
  rim_proj : ∀ h b p, p ∈ (rimChart h b).source → ∃ hx : rimChart h b p ∈ circ.domain,
    circ.proj ⟨rimChart h b p, hx⟩ = circ.cornerChart (handleCorner h b) p.2
  rim_vertex : ∀ h b {p}, p ∈ (rimChart h b).source →
    (rimChart h b p ∈ (vertex (handleEnd h b)).image ↔ p.2.2 ≤ 0)
  rim_handle : ∀ h b {p}, p ∈ (rimChart h b).source →
    (rimChart h b p ∈ range (handle h).map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0))
  rim_region : ∀ h b {p}, p ∈ (rimChart h b).source →
    (rimChart h b p ∈ circ.region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2))
  rim_label : ∀ h b, rimChart h b '' {p | p.2 = (0, 0)} =
    (fun x : ClosedCell 2 => (handle h).map (x, iccEnd b)) '' diskRim
  rim_disjoint : ∀ h b h' b', (h, b) ≠ (h', b') →
    Disjoint (rimChart h b).target (rimChart h' b').target
  -- V2 (review item 3, D4/D6): protection of every port and every whole torus seam collar from
  -- every operation support (rounding = rim charts; sphere surgery = sphere seam collars)
  external_region_disjoint : ∀ i, Disjoint (E.collar i).target circ.region
  external_handle_disjoint : ∀ i h, Disjoint (E.collar i).target (range (handle h).map)
  external_edgeCircle_disjoint : ∀ i e,
    Disjoint (E.collar i).target (range (edgeCircle e).piece.map)
  external_torusSeam_disjoint : ∀ i c,
    Disjoint (E.collar i).target (torusSeam c).collar.target
  external_sphereSeam_disjoint : ∀ i c,
    Disjoint (E.collar i).target (sphereSeam c).collar.target
  rim_external_disjoint : ∀ h b i, Disjoint (rimChart h b).target (E.collar i).target
  rim_torusSeam_disjoint : ∀ h b c, Disjoint (rimChart h b).target (torusSeam c).collar.target
  rim_sphereSeam_disjoint : ∀ h b c,
    Disjoint (rimChart h b).target (sphereSeam c).collar.target
  sphereSeam_region_disjoint : ∀ c, Disjoint (sphereSeam c).collar.target circ.region
  sphereSeam_handle_disjoint : ∀ c h,
    Disjoint (sphereSeam c).collar.target (range (handle h).map)

/-- The closed certificate is an abbreviation, not a second assembly (draft (a)). -/
abbrev ClosedDecompositionCertificate (W : CompactCarrier.{u}) :=
  Σ E : BoundaryTori W 0, DecompositionCertificate W E

/-! ## The closed wrapper -/

/-- A certificate without external ports is a closed certificate. -/
def DecompositionCertificate.toClosed {W : CompactCarrier.{u}} {E : BoundaryTori W 0}
    (D : DecompositionCertificate W E) : ClosedDecompositionCertificate W :=
  ⟨E, D⟩

namespace ClosedDecompositionCertificate

variable {W : CompactCarrier.{u}}

/-- The (empty) family of external ports of a closed certificate. -/
abbrev tori (D : ClosedDecompositionCertificate W) : BoundaryTori W 0 :=
  D.1

/-- The underlying certificate of a closed certificate. -/
abbrev cert (D : ClosedDecompositionCertificate W) : DecompositionCertificate W D.tori :=
  D.2

@[simp]
theorem toClosed_cert {E : BoundaryTori W 0} (C : DecompositionCertificate W E) :
    C.toClosed.cert = C :=
  rfl

@[simp]
theorem toClosed_tori {E : BoundaryTori W 0} (C : DecompositionCertificate W E) :
    C.toClosed.tori = E :=
  rfl

/-- A closed certificate lives on a carrier with empty boundary. -/
theorem boundary_eq_empty (D : ClosedDecompositionCertificate W) :
    W.model.boundary W.Carrier = ∅ := by
  rw [D.cert.external_exhausted]
  simp [BoundaryTori.image]

end ClosedDecompositionCertificate

/-! ## The empty circle region and the region inclusions -/

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

theorem region_subset_domain : R.region ⊆ (R.domain : Set W.Carrier) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem region_subset_interior : R.region ⊆ (W.interior : Set W.Carrier) :=
  R.region_subset_domain.trans R.domain_interior

theorem rounded_subset_domain : R.rounded ⊆ (R.domain : Set W.Carrier) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem rounded_subset_interior : R.rounded ⊆ (W.interior : Set W.Carrier) :=
  R.rounded_subset_domain.trans R.domain_interior

/-- The pointwise form of the field `rounding_agree` (V2's text): off the unit-box images of the
corner charts, the rounded base is the cornered base. -/
theorem rounding_le_zero_iff {R : CircleRegion W} {b : R.Base}
    (hb : b ∉ ⋃ k, R.cornerChart k '' rimBox 1) :
    R.rounding b ≤ 0 ↔ b ∈ R.cornerBase := by
  have h := Set.ext_iff.1 R.rounding_agree b
  exact ⟨fun hr => (h.1 ⟨hr, hb⟩).1, fun hc => (h.2 ⟨hc, hb⟩).1⟩

/-- The bottom open set of `W` has no points. -/
theorem false_of_bot (W : CompactCarrier.{u}) (x : (⊥ : TopologicalSpace.Opens W.Carrier)) :
    False := by
  have h := x.2
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_bot] at h
  exact h

/-- The projection of the empty circle region. -/
def emptyProj (W : CompactCarrier.{u}) : C((⊥ : TopologicalSpace.Opens W.Carrier), PEmpty.{u + 1}) where
  toFun x := (false_of_bot W x).elim
  continuous_toFun := continuous_def.2 fun s _ => by
    convert isOpen_empty
    ext x
    exact (false_of_bot W x).elim

/-- The empty circle region: base `PEmpty`, domain `⊥`, no defining functions, no corners. -/
def empty (W : CompactCarrier.{u}) : CircleRegion W where
  Base := PEmpty.{u + 1}
  baseCharts := ChartedSpace.empty _ _
  baseSmooth := by
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) PEmpty.{u + 1} := ChartedSpace.empty _ _
    exact IsManifold.empty ∞
  domain := ⊥
  domain_interior := by simp
  proj := emptyProj W
  proj_smooth x := (false_of_bot W x).elim
  proj_submersion x := (false_of_bot W x).elim
  neighborhood b := b.elim
  mem_neighborhood b := b.elim
  trivialization b := b.elim
  projection_trivialization b := b.elim
  definingCount := 0
  defining l := l.elim0
  defining_smooth l := l.elim0
  defining_regular l := l.elim0
  depth_le_two b := b.elim
  defining_independent b := b.elim
  cornerBase := ∅
  cornerBase_eq := (eq_empty_of_isEmpty _).symm
  cornerBase_compact := isCompact_empty
  cornerCount := 0
  cornerChart k := k.elim0
  cornerChart_source k := k.elim0
  cornerChart_disjoint k := k.elim0
  cornerFirst k := k.elim0
  cornerSecond k := k.elim0
  corner_ne k := k.elim0
  cornerScale k := k.elim0
  cornerScale_pos k := k.elim0
  chart_first k := k.elim0
  chart_second k := k.elim0
  chart_other k := k.elim0
  corner_center b := b.elim
  rounding b := b.elim
  rounding_smooth b := b.elim
  rounding_regular b := b.elim
  rounding_chart k := k.elim0
  rounding_agree := (eq_empty_of_isEmpty _).trans (eq_empty_of_isEmpty _).symm
  rounded_compact := (Set.toFinite _).isCompact

@[simp]
theorem empty_region (W : CompactCarrier.{u}) : (empty W).region = ∅ :=
  eq_empty_of_subset_empty fun _ hx => by
    simpa [empty] using (empty W).region_subset_domain hx

@[simp]
theorem empty_rounded (W : CompactCarrier.{u}) : (empty W).rounded = ∅ :=
  eq_empty_of_subset_empty fun _ hx => by
    simpa [empty] using (empty W).rounded_subset_domain hx

@[simp]
theorem empty_cornerCount (W : CompactCarrier.{u}) : (empty W).cornerCount = 0 :=
  rfl

@[simp]
theorem empty_definingCount (W : CompactCarrier.{u}) : (empty W).definingCount = 0 :=
  rfl

end CircleRegion

end GC.GraphManifold.Assembly
