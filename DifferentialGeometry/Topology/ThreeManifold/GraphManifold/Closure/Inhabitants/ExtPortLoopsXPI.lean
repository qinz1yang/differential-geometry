import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortCertificateXPI

/-!
# FC39 external-port regression instance: a NON-EMPTY loop case of the arc layer

External review 67, D67-6 (c): "a non-empty loop case" is an acceptance to-do of the general arc
theorem. On the external-port certificate `extportCertificate_XPI` (built through the GENERAL chain,
arc layer `stub_exists_arcLayer_GARC`, chosen by `Nonempty.some`), the loop branch is reached twice:

* `faceKind_partitioned_XPI` — under ANY seam–face link of the instance, a face through a point off
  the ports (`rad ≠ 1/2, 3`) and off the shared face (`rad ≠ 1`) is partitioned;
* `exists_face_of_vertex_XPI` — the end circle-torus of a band vertex lies in a face of that vertex
  (through `faceEquiv` / `face_image` of the link);
* `extportCertificate_loops_XPI` — two DIFFERENT loop faces of the certificate, one through the
  internal face of the outer cusp (`rad = 2`), one through the new slim end (`rad = 3/2`);
  `two_le_extportCertificate_loopFaceCount_XPI`.

Distinctness: the base circle of a loop is a zero set of ONE defining function, i.e. of one global
face function `GF.fn` on `C₁`, whose zero set there is ONE circle (`GF.face_eq`,
`globalFaces_zero_XPI`); a loop face therefore lies on one radius level (`loopFace_rad_eq_XPI`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-! ## Faces of the layers -/

section Layers

variable {V : VertexLayer carrierW_XPI} {vlink : VertexModelLink extportRowsW_XPI V}
  {O : PortLayer carrierW_XPI portsE_XPI V} {circ : CircleRegion carrierW_XPI}
  {S : SeamLayer carrierW_XPI V circ} {F : FaceLayer carrierW_XPI portsE_XPI V S O}
  {N : extportRowsW_XPI.SharedFace → TopologicalSpace.Opens carrierW_XPI.Carrier}

/-- A face through a point off the two ports and off the shared face is partitioned. -/
theorem faceKind_partitioned_XPI (sf : SeamFacesLink extportRowsW_XPI V vlink O S F N)
    {f : Fin F.faceCount} {x : carrierW_XPI.Carrier} (hx : x ∈ F.face f)
    (hhalf : rad_XPI x ≠ 1 / 2) (hthree : rad_XPI x ≠ 3) (hone : rad_XPI x ≠ 1) :
    F.faceKind f = .partitioned := by
  rcases hk : F.faceKind f with i | ⟨c, b⟩ | ⟨c, b⟩ | -
  · exfalso
    rw [(F.face_external f i hk).1] at hx
    obtain ⟨t, rfl⟩ := hx
    rcases carrier_isBoundaryPoint_iff_XPI.mp (portsE_XPI.boundary_zero i t) with h | h
    · exact hhalf h
    · exact hthree h
  · exfalso
    rw [(F.face_torusSeam f c b hk).1, sf.torus_slim c, sharedFace_eq_XPI (sf.torusEquiv c).1,
      sharedSet_XPI] at hx
    exact hone hx
  · exact (Fin.cast (sphereSeamCount_XPI sf) c).elim0
  · rfl

/-- A boundary preimage of an end point, in any piece equal to the band piece. -/
theorem exists_boundaryPreimage_XPI (B : BandRadii_XPI) (b : Bool) (t : Torus) :
    ∀ P : PieceEmbedding carrierW_XPI, P = bandPiece_XPI B →
      ∃ q : P.Piece, q ∈ (𝓡∂ 3).boundary P.Piece ∧
        P.map q = (bandPiece_XPI B).map (bandEnd_XPI B b t) := by
  rintro P rfl
  exact ⟨bandEnd_XPI B b t, bandEnd_in_boundary_XPI B b (mem_range_self t), rfl⟩

/-- The end circle-torus `b` of a band vertex lies in a face of that vertex. -/
theorem exists_face_of_vertex_XPI (sf : SeamFacesLink extportRowsW_XPI V vlink O S F N)
    (k : Fin V.vertexCount) (B : BandRadii_XPI) (hk : (V.vertex k).piece = bandPiece_XPI B)
    (b : Bool) (t : Torus) : ∃ f, (bandPiece_XPI B).map (bandEnd_XPI B b t) ∈ F.face f := by
  obtain ⟨q, hq, hqx⟩ := exists_boundaryPreimage_XPI B b t _ hk
  refine ⟨sf.faceEquiv.symm ⟨k, ActualComponent.of hq⟩, ?_⟩
  rw [sf.face_image, Equiv.apply_symm_apply]
  exact ⟨q, mem_connectedComponentIn hq, hqx⟩

/-- The vertex of the outer cusp is the band of `cuspRadii_XPI 0`. -/
theorem vertex_cusp0_piece_XPI (vlink : VertexModelLink extportRowsW_XPI V) :
    (V.vertex (vlink.index.symm (.inr (.inl 0)))).piece = bandPiece_XPI (cuspRadii_XPI 0) := by
  rw [vlink.vertex_piece, Equiv.apply_symm_apply]
  rfl

/-- The vertex of the slim piece is the band of `slimRadii_XPI`. -/
theorem vertex_slim_piece_XPI (vlink : VertexModelLink extportRowsW_XPI V) :
    (V.vertex (vlink.index.symm (.inr (.inr (0 : Fin 1))))).piece = bandPiece_XPI slimRadii_XPI := by
  rw [vlink.vertex_piece, Equiv.apply_symm_apply]
  rfl

end Layers

/-- The radius of an end point of a band. -/
theorem rad_bandEnd_XPI (B : BandRadii_XPI) (b : Bool) (t : Torus) :
    rad_XPI ((bandPiece_XPI B).map (bandEnd_XPI B b t)) = bandEndRadius_XPI B b :=
  norm_bandEnd_XPI B b t

/-! ## Loops of a certificate without arcs -/

/-- In a certificate without arc faces, a point of a partitioned face in the circle region lies in
a loop face owned by that face. -/
theorem exists_loop_of_mem_XPI {W : CompactCarrier} {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hA : D.arcFaceCount = 0) {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) {x : W.Carrier} (hx : x ∈ D.face f) (hR : x ∈ D.circ.region) :
    ∃ j, D.loopOwner j = f ∧ x ∈ D.loopFace j := by
  have h := D.face_region_inter f hf
  have hxx : x ∈ D.face f ∩ D.circ.region := ⟨hx, hR⟩
  rw [h] at hxx
  rcases hxx with hxa | hxl
  · obtain ⟨j, -⟩ := mem_iUnion.1 hxa
    exact (Fin.cast hA j).elim0
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hxl
    obtain ⟨hjf, hxj⟩ := mem_iUnion.1 hj
    exact ⟨j, hjf, hxj⟩

/-! ## The loops of the external-port certificate -/

/-- A loop face of the certificate lies in its circle region. -/
theorem extportCertificate_loop_region_XPI (j : Fin extportCertificate_XPI.1.loopFaceCount) :
    extportCertificate_XPI.1.loopFace j ⊆ extportCertificate_XPI.1.circ.region := by
  intro x hx
  have h := extportCertificate_XPI.1.face_region_inter _
    (extportCertificate_XPI.1.loopOwner_kind j)
  have hx' : x ∈ (⋃ (j' : Fin extportCertificate_XPI.1.arcFaceCount)
      (_ : extportCertificate_XPI.1.arcOwner j' = extportCertificate_XPI.1.loopOwner j),
        extportCertificate_XPI.1.arcFace j') ∪
      (⋃ (j' : Fin extportCertificate_XPI.1.loopFaceCount)
        (_ : extportCertificate_XPI.1.loopOwner j' = extportCertificate_XPI.1.loopOwner j),
          extportCertificate_XPI.1.loopFace j') :=
    Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨rfl, hx⟩⟩)
  rw [← h] at hx'
  exact hx'.2

/-- **A loop face of the certificate lies on ONE radius level.** -/
theorem loopFace_rad_eq_XPI {j : Fin extportCertificate_XPI.1.loopFaceCount}
    {x : carrierW_XPI.Carrier} (hx : x ∈ extportCertificate_XPI.1.loopFace j) :
    rad_XPI x = ![3 / 2, 2] (extportCertificate_XPI.1.loopDefining j) := by
  have hR := extportCertificate_loop_region_XPI j hx
  rw [extportCertificate_XPI.1.loopFace_eq j] at hx
  obtain ⟨u, ⟨z, hz⟩, rfl⟩ := hx
  have hd := extportCertificate_XPI.1.loopBase_defining j z
  rw [hz] at hd
  obtain ⟨u', hu', hu'x⟩ := hR
  have huu : u' = u := Subtype.ext hu'x
  subst huu
  -- the base point of `u` in `GF.base`, in `C₁`
  let p : extportGF_XPI.base := extportCertificate_XPI.1.circ.proj u'
  have hcb : p.val ∈ extportRowsW_XPI.circle.cbase := by
    have h2 : p ∈ cornerSet_XPI extportGF_XPI := hu'
    rw [cornerSet_eq_XPI] at h2
    exact h2
  let l : Fin 2 := extportCertificate_XPI.1.loopDefining j
  have hd' : extportGF_XPI.fn (extportGF_XPI.actualFace.symm (circleFaceEquiv_XPI l)) p.val = 0 :=
    hd
  have hz0 : p.val ∈ {c : extportRowsW_XPI.circle.Base | ‖c.val‖ = ![3 / 2, 2] l} := by
    rw [← globalFaces_zero_XPI extportGF_XPI l]
    exact ⟨hcb, hd'⟩
  have hn : ‖(show circleBaseOpens_XPI from p.val).val‖ = rad_XPI u'.val :=
    norm_toE2_XPI _
  rw [← hn]
  exact hz0

/-- **The non-empty loop case**: the certificate has two DIFFERENT loop faces, one through the
internal face of the outer cusp (`rad = 2`) and one through the new slim end (`rad = 3/2`). -/
theorem extportCertificate_loops_XPI :
    ∃ j₀ j₁ : Fin extportCertificate_XPI.1.loopFaceCount, j₀ ≠ j₁ ∧
      (∃ x ∈ extportCertificate_XPI.1.loopFace j₀, rad_XPI x = 2) ∧
      (∃ x ∈ extportCertificate_XPI.1.loopFace j₁, rad_XPI x = 3 / 2) := by
  let hVO := exists_vertexLayer_portLayer_G1 extportRowsW_XPI
  let hSF := exists_seams_faces_GSF extportRowsW_XPI hVO.choose hVO.choose_spec.choose
    extportAdaptedG_XPI.circ hVO.choose_spec.choose_spec.choose
    hVO.choose_spec.choose_spec.choose_spec extportSafe_XPI.shared extportSafe_XPI.shared_safe
  let sf := hSF.choose_spec.choose_spec.some
  have hA := extportCertificate_arcFaceCount_XPI
  -- the outer cusp face `rad = 2`
  obtain ⟨f₀, hf₀⟩ := exists_face_of_vertex_XPI sf _ (cuspRadii_XPI 0)
    (vertex_cusp0_piece_XPI hVO.choose_spec.choose) true (1, 1)
  have hr₀ := rad_bandEnd_XPI (cuspRadii_XPI 0) true (1, 1)
  change _ = 2 at hr₀
  have hk₀ := faceKind_partitioned_XPI sf hf₀ (by rw [hr₀]; norm_num) (by rw [hr₀]; norm_num)
    (by rw [hr₀]; norm_num)
  have hR₀ : (bandPiece_XPI (cuspRadii_XPI 0)).map (bandEnd_XPI (cuspRadii_XPI 0) true (1, 1)) ∈
      extportCertificate_XPI.1.circ.region := by
    rw [extportCertificate_region_XPI]
    change 3 / 2 ≤ rad_XPI _ ∧ rad_XPI _ ≤ 2
    rw [hr₀]
    norm_num
  obtain ⟨j₀, -, hj₀⟩ := exists_loop_of_mem_XPI extportCertificate_XPI.1 hA hk₀ hf₀ hR₀
  -- the new slim end `rad = 3/2`
  obtain ⟨f₁, hf₁⟩ := exists_face_of_vertex_XPI sf _ slimRadii_XPI
    (vertex_slim_piece_XPI hVO.choose_spec.choose) true (1, 1)
  have hr₁ := rad_bandEnd_XPI slimRadii_XPI true (1, 1)
  change _ = 3 / 2 at hr₁
  have hk₁ := faceKind_partitioned_XPI sf hf₁ (by rw [hr₁]; norm_num) (by rw [hr₁]; norm_num)
    (by rw [hr₁]; norm_num)
  have hR₁ : (bandPiece_XPI slimRadii_XPI).map (bandEnd_XPI slimRadii_XPI true (1, 1)) ∈
      extportCertificate_XPI.1.circ.region := by
    rw [extportCertificate_region_XPI]
    change 3 / 2 ≤ rad_XPI _ ∧ rad_XPI _ ≤ 2
    rw [hr₁]
    norm_num
  obtain ⟨j₁, -, hj₁⟩ := exists_loop_of_mem_XPI extportCertificate_XPI.1 hA hk₁ hf₁ hR₁
  refine ⟨j₀, j₁, fun h => ?_, ⟨_, hj₀, hr₀⟩, ⟨_, hj₁, hr₁⟩⟩
  subst h
  have e₀ := loopFace_rad_eq_XPI hj₀
  have e₁ := loopFace_rad_eq_XPI hj₁
  rw [hr₀] at e₀
  rw [hr₁, ← e₀] at e₁
  norm_num at e₁

/-- The certificate has at least two loop faces. -/
theorem two_le_extportCertificate_loopFaceCount_XPI :
    2 ≤ extportCertificate_XPI.1.loopFaceCount := by
  obtain ⟨j₀, j₁, hne, -⟩ := extportCertificate_loops_XPI
  by_contra h
  rw [not_le] at h
  have h1 : extportCertificate_XPI.1.loopFaceCount ≤ 1 := Nat.lt_succ_iff.mp h
  exact hne (Fin.ext (by omega))

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
