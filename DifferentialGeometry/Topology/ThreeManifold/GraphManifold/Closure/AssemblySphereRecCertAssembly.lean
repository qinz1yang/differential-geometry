import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertFields3
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormMeasure

/-!
# FC42 sphere recursion, packet S4 (group G6): the inherited certificate

Lane ASM-SPH2b (frozen statement `build-logs/scratch/ASM-SPH/Targets.lean` v2, S4). On a capped
component all of whose caps belong to `S² × I` sides, the inherited data of
`AssemblySphereRecCertIndex`/`…Fields1`/`…Fields2`/`…Fields3` assemble to a certificate `ccCert`
of the component carrier with the ports `X.componentTori DQ i`:

* one sphere seam fewer (`ccCert_sphereSeamCount_lt`: the cut seam is not a seam of the component);
* its bad vertices inject into the bad vertices of `D` that are not sides of the cut seam
  (`ccCert_badVertexCount_le`: a bad vertex of the component is not a ball, so it is a lifted
  vertex that is not a side, with the same model and the same partitioned sphere face);
* no closed zero vertex; the rim-product clause is inherited.

**S4** `exists_cappedComponentCertificate`. Deviation from the frozen text (a strengthening): the
instance argument `[ConnectedSpace W.Carrier]` of the frozen statement is not used by the proof and
is dropped (the declaration linter `unusedArguments` rejects it); the verbatim frozen form is the
`example` after the theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)
  (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i → D.SideSphereInterval c b)

/-- **The inherited certificate of a capped component** (all caps of the component belong to
`S² × I` sides). -/
def ccCert : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i) where
  external_exhausted := X.componentTori_boundary DQ i
  vertexCount := Nat.card {k // D.ccV c X DQ i k}
  vertex := D.ccVertex c X DQ i hcap
  handleCount := Nat.card {h // D.ccH c X DQ i h}
  handle := D.ccHandle c X DQ i
  edgeCircleCount := Nat.card {e // D.ccE c X DQ i e}
  edgeCircle := D.ccEdgeCircle c X DQ i
  circ := D.ccCirc c X DQ i
  cover := D.cc_cover c X DQ i hcap
  vertex_disjoint := D.cc_vertex_disjoint c X DQ i hcap
  handle_disjoint := D.cc_handle_disjoint c X DQ i
  edgeCircle_disjoint := D.cc_edgeCircle_disjoint c X DQ i
  vertex_handle_disjoint := D.cc_vertex_handle_disjoint c X DQ i hcap
  edgeCircle_vertex_disjoint := D.cc_edgeCircle_vertex_disjoint c X DQ i hcap
  edgeCircle_handle_disjoint := D.cc_edgeCircle_handle_disjoint c X DQ i
  circ_vertex_disjoint := D.cc_circ_vertex_disjoint c X DQ i hcap
  circ_handle_disjoint := D.cc_circ_handle_disjoint c X DQ i
  circ_edgeCircle_disjoint := D.cc_circ_edgeCircle_disjoint c X DQ i
  vertical_fibre := D.cc_vertical_fibre c X DQ i
  edgeCircle_vertical := D.cc_edgeCircle_vertical c X DQ i
  torusSeamCount := Nat.card {d // D.ccT c X DQ i d}
  torusSeam := D.ccTorusSeam c X DQ i
  torusSide := D.ccTorusSide c X DQ i
  torusSide_neg := D.cc_torusSide_neg c X DQ i hcap
  torusSide_pos := D.cc_torusSide_pos c X DQ i hcap
  torusSeam_disjoint := D.cc_torusSeam_disjoint c X DQ i
  sphereSeamCount := Nat.card {c' // D.ccS c X DQ i c'}
  sphereSeam := D.ccSphereSeam c X DQ i
  sphereSide := D.ccSphereSide c X DQ i
  sphereSide_neg := D.cc_sphereSide_neg c X DQ i hcap
  sphereSide_pos := D.cc_sphereSide_pos c X DQ i hcap
  sphereSeam_disjoint := D.cc_sphereSeam_disjoint c X DQ i
  sphere_torus_seam_disjoint := D.cc_sphere_torus_seam_disjoint c X DQ i
  externalOwner := D.ccExternalOwner c X DQ i
  external_owned := D.cc_external_owned c X DQ i hcap
  faceCount := Nat.card {f // D.ccF c X DQ i f}
  face := D.ccFace c X DQ i
  faceOwner := D.ccFaceOwner c X DQ i
  faceModel := D.ccFaceModel c X DQ i
  face_exhausted := D.cc_face_exhausted c X DQ i hcap
  faceKind := D.ccFaceKind c X DQ i
  face_disjoint := D.cc_face_disjoint c X DQ i
  face_external := D.cc_face_external c X DQ i
  external_face := D.cc_external_face c X DQ i
  face_torusSeam := D.cc_face_torusSeam c X DQ i
  torusSeam_face := D.cc_torusSeam_face c X DQ i
  face_sphereSeam := D.cc_face_sphereSeam c X DQ i
  sphereSeam_face := D.cc_sphereSeam_face c X DQ i
  handleEnd := D.ccHandleEnd c X DQ i
  handleFace := D.ccHandleFace c X DQ i
  handleFace_owner := D.cc_handleFace_owner c X DQ i
  handleFace_kind := D.cc_handleFace_kind c X DQ i
  handleEnd_face := D.cc_handleEnd_face c X DQ i
  endDisk_disjoint := D.cc_endDisk_disjoint c X DQ i
  arcFaceCount := Nat.card {j // D.ccA c X DQ i j}
  arcFace := D.ccArcFace c X DQ i
  arcOwner := D.ccArcOwner c X DQ i
  arcOwner_kind := D.cc_arcOwner_kind c X DQ i
  arcBase := D.ccArcBase c X DQ i
  arcBase_embedding := D.cc_arcBase_embedding c X DQ i
  arcFace_eq := D.cc_arcFace_eq c X DQ i
  arcDefining := D.ccArcDefining c X DQ i
  arcBase_defining := D.cc_arcBase_defining c X DQ i
  arcAnnulus := D.ccArcAnnulus c X DQ i
  arcAnnulus_continuous := D.cc_arcAnnulus_continuous c X DQ i
  arcAnnulus_injective := D.cc_arcAnnulus_injective c X DQ i
  arcAnnulus_range := D.cc_arcAnnulus_range c X DQ i
  arcAnnulus_proj := D.cc_arcAnnulus_proj c X DQ i
  loopFaceCount := Nat.card {j // D.ccL c X DQ i j}
  loopFace := D.ccLoopFace c X DQ i
  loopOwner := D.ccLoopOwner c X DQ i
  loopOwner_kind := D.cc_loopOwner_kind c X DQ i
  loopBase := D.ccLoopBase c X DQ i
  loopBase_embedding := D.cc_loopBase_embedding c X DQ i
  loopFace_eq := D.cc_loopFace_eq c X DQ i
  loopDefining := D.ccLoopDefining c X DQ i
  loopBase_defining := D.cc_loopBase_defining c X DQ i
  loopFace_closed := D.cc_loopFace_closed c X DQ i
  loopFace_nonempty := D.cc_loopFace_nonempty c X DQ i
  arcFace_disjoint := D.cc_arcFace_disjoint c X DQ i
  loopFace_disjoint := D.cc_loopFace_disjoint c X DQ i
  arc_loop_disjoint := D.cc_arc_loop_disjoint c X DQ i
  face_partition := D.cc_face_partition c X DQ i
  face_region_inter := D.cc_face_region_inter c X DQ i
  handleArc := D.ccHandleArc c X DQ i
  handleArc_owner := D.cc_handleArc_owner c X DQ i
  handleArc_meets := D.cc_handleArc_meets c X DQ i
  endDisk_loop_disjoint := D.cc_endDisk_loop_disjoint c X DQ i
  endDisk_rim := D.cc_endDisk_rim c X DQ i
  arcEnd := D.ccArcEnd c X DQ i
  arcEnd_arc := D.cc_arcEnd_arc c X DQ i
  arcEnd_injective := D.cc_arcEnd_injective c X DQ i
  arcEnd_surjective := D.cc_arcEnd_surjective c X DQ i
  arcAnnulus_end := D.cc_arcAnnulus_end c X DQ i
  handleCorner := D.ccHandleCorner c X DQ i
  handleCorner_bijective := D.cc_handleCorner_bijective c X DQ i
  arcBase_end := D.cc_arcBase_end c X DQ i
  rimChart := D.ccRimChart c X DQ i
  rim_source := D.cc_rim_source c X DQ i
  rim_proj := D.cc_rim_proj c X DQ i
  rim_vertex := D.cc_rim_vertex c X DQ i hcap
  rim_handle := D.cc_rim_handle c X DQ i
  rim_region := D.cc_rim_region c X DQ i
  rim_label := D.cc_rim_label c X DQ i
  rim_disjoint := D.cc_rim_disjoint c X DQ i
  external_region_disjoint := D.cc_external_region_disjoint c X DQ i
  external_handle_disjoint := D.cc_external_handle_disjoint c X DQ i
  external_edgeCircle_disjoint := D.cc_external_edgeCircle_disjoint c X DQ i
  external_torusSeam_disjoint := D.cc_external_torusSeam_disjoint c X DQ i
  external_sphereSeam_disjoint := D.cc_external_sphereSeam_disjoint c X DQ i
  rim_external_disjoint := D.cc_rim_external_disjoint c X DQ i
  rim_torusSeam_disjoint := D.cc_rim_torusSeam_disjoint c X DQ i
  rim_sphereSeam_disjoint := D.cc_rim_sphereSeam_disjoint c X DQ i
  sphereSeam_region_disjoint := D.cc_sphereSeam_region_disjoint c X DQ i
  sphereSeam_handle_disjoint := D.cc_sphereSeam_handle_disjoint c X DQ i

/-- One sphere seam fewer. -/
theorem ccCert_sphereSeamCount_lt :
    (D.ccCert c X DQ i hcap).sphereSeamCount < D.sphereSeamCount := by
  have h := Finite.card_subtype_lt (p := D.ccS c X DQ i) (x := c) fun h => h.1 rfl
  have h2 : Nat.card (Fin D.sphereSeamCount) = D.sphereSeamCount := by simp
  exact h2 ▸ h

/-- No closed zero vertex. -/
theorem ccCert_ne_closedZero (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (k : Fin (D.ccCert c X DQ i hcap).vertexCount)
    (C : ClosedZeroPiece (GC.Topology.componentCarrier X.Q DQ i)) :
    (D.ccCert c X DQ i hcap).vertex k ≠ .closedZero C :=
  D.ccVertexOf_ne_closedZero c X DQ i hcap hnz (ccEquiv _ k).1 (ccEquiv _ k).2 C

/-- The rim-product clause is inherited. -/
theorem ccCert_rimProduct (hR : D.RimProduct) : (D.ccCert c X DQ i hcap).RimProduct :=
  fun h b => D.cc_rimProduct c X DQ i hR h b

/-- A ball stays a ball. -/
theorem isBall_ccVertexOf_of_isBall (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k)
    (hb : (D.vertex k).IsBall) : (D.ccVertexOf c X DQ i hcap k hk).IsBall := by
  unfold ccVertexOf
  split_ifs with hs
  · exact Vertex.isBall_zero_ball _ _
  · exact Vertex.IsBall.toComponent (hb.ofMap _ _ _ _) _

/-- **The bad vertices of the component inject into the non-side bad vertices of `D`.** -/
theorem ccCert_badVertexCount_le :
    (D.ccCert c X DQ i hcap).badVertexCount ≤
      (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card := by
  classical
  rw [← (D.ccCert c X DQ i hcap).card_badVertexSet]
  refine Finset.card_le_card_of_injOn (fun k' => (ccEquiv _ k').1) ?_ ?_
  · intro k' hk'
    have hk'' := mem_badVertexSet_iff.mp (Finset.mem_coe.mp hk')
    obtain ⟨hnb, f', hfo, hfk, e', hfm⟩ := hk''
    have hns : ∀ b, (ccEquiv _ k').1 ≠ D.sphereSide c b := fun b hb =>
      hnb (D.isBall_ccVertexOf_of_side c X DQ i hcap (ccEquiv _ k').1 (ccEquiv _ k').2
        (isSide_iff.mpr ⟨b, hb⟩))
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_badVertexSet_iff.mpr ⟨?_, ?_⟩, hns⟩)
    · exact fun hb => hnb (D.isBall_ccVertexOf_of_isBall c X DQ i hcap (ccEquiv _ k').1
        (ccEquiv _ k').2 hb)
    · refine ⟨(ccEquiv _ f').1, ccFaceOwner_eq_iff.mp hfo,
        eq_partitioned_of_ccKind (ccEquiv _ f').2 hfk, faceModel_inl_of_ccFaceModel hfm⟩
  · intro k₁ _ k₂ _ h
    exact (ccEquiv _).injective (Subtype.ext h)

end DecompositionCertificate

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **S4** (frozen text without the unused `[ConnectedSpace W.Carrier]`, see the module
docstring). A component of the capped carrier all of whose caps belong to `S² × I` sides carries
the inherited certificate with the restricted ports: one sphere seam fewer, bad vertices injecting
into the non-side bad vertices of `D`, no closed zero vertex, the rim-product clause inherited. -/
theorem exists_cappedComponentCertificate
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components) (i : Fin DQ.count)
    (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
      ∃ (P : PieceEmbedding W)
        (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
        D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :
    ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
      D'.sphereSeamCount < D.sphereSeamCount ∧
      D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
      (∀ k C, D'.vertex k ≠ .closedZero C) ∧
      (D.RimProduct → D'.RimProduct) :=
  ⟨D.ccCert c X DQ i hcap, D.ccCert_sphereSeamCount_lt c X DQ i hcap,
    D.ccCert_badVertexCount_le c X DQ i hcap, D.ccCert_ne_closedZero c X DQ i hcap hnz,
    D.ccCert_rimProduct c X DQ i hcap⟩

/-- **S4, the frozen text verbatim** (`build-logs/scratch/ASM-SPH/Targets.lean` v2). -/
example [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components) (i : Fin DQ.count)
    (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
      ∃ (P : PieceEmbedding W)
        (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
        D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) :
    ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
      D'.sphereSeamCount < D.sphereSeamCount ∧
      D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
      (∀ k C, D'.vertex k ≠ .closedZero C) ∧
      (D.RimProduct → D'.RimProduct) :=
  D.exists_cappedComponentCertificate hnz c X DQ i hcap

/-- **Consumer (G6).** A component of the capped carrier containing no cap carries the inherited
certificate (the `S² × I` hypothesis is vacuous). -/
theorem exists_componentCertificate_of_capFree (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
    (i : Fin DQ.count) (hfree : ∀ j, X.spherePiece DQ j ≠ i) :
    ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
      D'.sphereSeamCount < D.sphereSeamCount ∧
      D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
      (∀ k C, D'.vertex k ≠ .closedZero C) ∧
      (D.RimProduct → D'.RimProduct) :=
  D.exists_cappedComponentCertificate hnz c X DQ i fun _ h => (hfree _ h).elim

end DecompositionCertificate

end GC.GraphManifold.Assembly
