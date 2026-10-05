import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortJunctionsXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeNeighbourhoods
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesExist
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GComponentEquiv
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceAtlas

/-!
# FC39 external-port regression instance: the GROUP G layers on `extportRowsW_XPI`

External review 63 (D63-7) and 67 (D67-6 (c)): the delivered GENERAL GROUP G theorems applied to the
external-port rows `extportRowsW_XPI` (`T² × I`, two ports, two cusp cores, one slim torus
interval, no edge), each conclusion recorded on the instance:

* component equivalence (`totalComponentEquiv_G1`): no edge component;
* vertex / port layers (`exists_vertexLayer_portLayer_G1`): three vertices, the two ports owned by
  the two DIFFERENT cusp-core vertices;
* safe neighbourhoods (`exists_safeNeighbourhoods_GSAFE`): the unique shared face (slim end `rad = 1`
  glued to the internal face of the inner cusp `1`); the shared-face collar exclusion
  `sharedSet_disjoint_closure_collar_GSAFE` is exercised in BOTH cusp branches — port `1`
  (same cusp: `collar_closure_off`) and port `0` (different cusp: `CuspCores.disjoint`) — with
  non-empty sets on both sides; the corner (rim) fields are vacuous (no edge endpoint);
* seams / faces (`exists_seams_faces_GSF`): one torus seam, no sphere seam, six faces (two per
  vertex: `faceCount_XPI`), the two external faces are the two boundary tori;
* trace atlas (`frontier_cbase_eq_iUnion_baseTrace_GTR`, `labelled_baseTrace_atlas_GTR`): the two
  traces are the circles `‖w‖ = 3/2`, `‖w‖ = 2`, every frontier point carries exactly ONE label;
* global face functions V2 (`exists_globalFaceFunctions_GGFF`): every `GF` has two faces and no
  double zero.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

instance isEmpty_rowsEdgeEnd_XPI : IsEmpty extportRowsW_XPI.edge.EdgeEnd :=
  isEmpty_edgeEnd_XPI

instance isEmpty_rowsEdgeBaseComponent_XPI : IsEmpty extportRowsW_XPI.edge.EdgeBaseComponent :=
  isEmpty_edgeBaseComponent_XPI

/-! ## Component equivalence -/

/-- **`totalComponentEquiv_G1` on the instance.** -/
theorem componentEquiv_XPI :
    ∃ e : (Fin extportRowsW_XPI.edgeModels.intervalCount ⊕
        Fin extportRowsW_XPI.edgeModels.circleCount) ≃ extportRowsW_XPI.edge.EdgeActualComponent,
      ∀ s, (e s).1 = extportRowsW_XPI.edge.wholeComponent
        (extportRowsW_XPI.edgeModels.componentEquiv s) :=
  totalComponentEquiv_G1 _ _

/-- The edge piece of the instance has no actual component. -/
theorem isEmpty_edgeActualComponent_XPI : IsEmpty extportRowsW_XPI.edge.EdgeActualComponent := by
  obtain ⟨e, -⟩ := componentEquiv_XPI
  refine ⟨fun C => ?_⟩
  rcases e.symm C with i | j
  · exact i.elim0
  · exact j.elim0

/-! ## Vertex and port layers -/

/-- Every vertex layer linked to the instance rows has three vertices. -/
theorem vertexCount_XPI {V : VertexLayer carrierW_XPI} (vlink : VertexModelLink extportRowsW_XPI V) :
    V.vertexCount = 3 := by
  rw [vlink.vertexCount_eq_G1]
  rfl

/-- **`exists_vertexLayer_portLayer_G1` on the instance**: three vertices; the two ports are owned
by two different vertices, the cusp-core vertices of their own cusps. -/
theorem vertexLayer_portLayer_XPI :
    ∃ V : VertexLayer carrierW_XPI, ∃ vlink : VertexModelLink extportRowsW_XPI V,
      ∃ O : PortLayer carrierW_XPI portsE_XPI V, PortModelLink extportRowsW_XPI vlink O ∧
        V.vertexCount = 3 ∧ O.externalOwner 0 ≠ O.externalOwner 1 ∧
        ∀ i, V.vertex (O.externalOwner i) =
          .cuspCore (extportCuspCores_XPI.piece i) (extportCuspCores_XPI.product i) := by
  obtain ⟨V, vlink, O, olink⟩ := exists_vertexLayer_portLayer_G1 extportRowsW_XPI
  refine ⟨V, vlink, O, olink, vertexCount_XPI vlink, fun h => ?_, olink.owner_vertex_G1⟩
  have h2 := congrArg vlink.index h
  rw [olink.owner_index, olink.owner_index] at h2
  simp at h2

/-! ## The shared face and the safe neighbourhoods -/

/-- **The shared face of the instance**: the slim end `false` (`rad = 1`). -/
def sharedFace_XPI : extportRowsW_XPI.SharedFace :=
  ⟨⟨((0 : Fin 1), false), trivial⟩, rfl⟩

/-- The shared face is unique. -/
theorem sharedFace_eq_XPI (σ : extportRowsW_XPI.SharedFace) : σ = sharedFace_XPI := by
  obtain ⟨⟨⟨j, b⟩, hj⟩, hσ⟩ := σ
  obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  cases b
  · rfl
  · exfalso
    have hn := (slimEndKind_none_iff_XPI (e := ⟨((0 : Fin 1), true), hj⟩)).mpr rfl
    change (extportSlim_XPI.endKind ⟨((0 : Fin 1), true), hj⟩).isSome = true at hσ
    rw [hn] at hσ
    exact Bool.false_ne_true hσ

/-- The neighbour of the shared face is the internal model face of the inner cusp `1`. -/
theorem sharedNeighbour_XPI :
    extportRowsW_XPI.sharedNeighbour sharedFace_XPI =
      .inr ⟨1, ⟨extportCuspCores_XPI.internalModelFace 1, rfl⟩⟩ :=
  rfl

/-- The shared face is the torus `rad = 1`. -/
theorem sharedSet_XPI : extportRowsW_XPI.sharedSet sharedFace_XPI = {x | rad_XPI x = 1} :=
  (endSet_XPI sharedFace_XPI.1).trans rfl

/-- A carrier point of radius `r ∈ [1/2, 3]`. -/
theorem exists_rad_eq_XPI {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 3) :
    ∃ x : carrierW_XPI.Carrier, rad_XPI x = r :=
  ⟨scalePt_XPI (portsE_XPI.torusMap 0 (1, 1)) r, rad_scalePt_of_mem_XPI _ h1 h2⟩

theorem sharedSet_nonempty_XPI : (extportRowsW_XPI.sharedSet sharedFace_XPI).Nonempty := by
  rw [sharedSet_XPI]
  exact exists_rad_eq_XPI (by norm_num) (by norm_num)

/-- Both port collar targets are non-empty. -/
theorem collar_target_nonempty_XPI (i : Fin 2) : (portsE_XPI.collar i).target.Nonempty :=
  ⟨portsE_XPI.torusMap i (1, 1), (portsE_XPI.collar i).map_source (by
    rw [portsE_XPI.source_eq]; change (0 : ℝ) < 1; norm_num)⟩

/-- **Collar exclusion, same-cusp branch** (`b = i` in `sharedSet_disjoint_closure_collar_GSAFE`):
the shared face (neighbour: cusp `1`) avoids the closure of the collar of port `1`, both non-empty. -/
theorem shared_off_collar_sameCusp_XPI :
    (extportRowsW_XPI.sharedSet sharedFace_XPI).Nonempty ∧
      (closure (portsE_XPI.collar 1).target).Nonempty ∧
      Disjoint (extportRowsW_XPI.sharedSet sharedFace_XPI) (closure (portsE_XPI.collar 1).target) :=
  ⟨sharedSet_nonempty_XPI, (collar_target_nonempty_XPI 1).mono subset_closure,
    extportRowsW_XPI.sharedSet_disjoint_closure_collar_GSAFE sharedFace_XPI 1⟩

/-- **Collar exclusion, different-cusp branch** (`b ≠ i`): the shared face avoids the closure of
the collar of port `0`, both non-empty. -/
theorem shared_off_collar_otherCusp_XPI :
    (extportRowsW_XPI.sharedSet sharedFace_XPI).Nonempty ∧
      (closure (portsE_XPI.collar 0).target).Nonempty ∧
      Disjoint (extportRowsW_XPI.sharedSet sharedFace_XPI) (closure (portsE_XPI.collar 0).target) :=
  ⟨sharedSet_nonempty_XPI, (collar_target_nonempty_XPI 0).mono subset_closure,
    extportRowsW_XPI.sharedSet_disjoint_closure_collar_GSAFE sharedFace_XPI 0⟩

/-- The owner of port `1` is the cusp of the shared neighbour; the owner of port `0` is not. -/
theorem shared_cusp_cases_XPI :
    (∃ G, extportRowsW_XPI.sharedNeighbour sharedFace_XPI = .inr ⟨1, G⟩) ∧
      ∀ G, extportRowsW_XPI.sharedNeighbour sharedFace_XPI ≠ .inr ⟨0, G⟩ := by
  refine ⟨⟨_, sharedNeighbour_XPI⟩, fun G h => ?_⟩
  rw [sharedNeighbour_XPI] at h
  have h2 := congrArg (fun F : NeighbourFace extportZeroDomains_XPI extportCuspCores_XPI =>
    match F with
    | .inl _ => (2 : ℕ)
    | .inr G => G.1.val) h
  simp at h2

/-- **`exists_safeNeighbourhoods_GSAFE` on the instance.** -/
theorem exists_safe_XPI : Nonempty (ProducerSafeNeighbourhoods extportRowsW_XPI) :=
  exists_safeNeighbourhoods_GSAFE extportRowsW_XPI

/-- For EVERY safe family of the instance, the shared neighbourhood is non-empty and its closure
avoids both (non-empty) port collars. -/
theorem safe_shared_off_ports_XPI (safe : ProducerSafeNeighbourhoods extportRowsW_XPI) (i : Fin 2) :
    (safe.shared sharedFace_XPI : Set carrierW_XPI.Carrier).Nonempty ∧
      (portsE_XPI.collar i).target.Nonempty ∧
      Disjoint (closure (safe.shared sharedFace_XPI : Set carrierW_XPI.Carrier))
        (portsE_XPI.collar i).target :=
  ⟨sharedSet_nonempty_XPI.mono (safe.shared_safe.face_subset sharedFace_XPI),
    collar_target_nonempty_XPI i, safe.shared_safe.off_external sharedFace_XPI i⟩

/-- The corner (rim) branch is vacuous on the instance: there is no edge endpoint, so every safe
family has no corner tube. -/
theorem safe_corner_empty_XPI (safe : ProducerSafeNeighbourhoods extportRowsW_XPI) :
    ⋃ e, safe.corner e = ∅ :=
  iUnion_eq_empty.mpr fun e => isEmptyElim e

/-! ## Seams and faces -/

/-- The shared face is a torus. -/
theorem sharedShape_XPI : extportRowsW_XPI.sharedShape sharedFace_XPI = .torus :=
  rfl

section SeamFaceCounts

variable {V : VertexLayer carrierW_XPI} {vlink : VertexModelLink extportRowsW_XPI V}
  {O : PortLayer carrierW_XPI portsE_XPI V} {circ : CircleRegion carrierW_XPI}
  {S : SeamLayer carrierW_XPI V circ} {F : FaceLayer carrierW_XPI portsE_XPI V S O}
  {N : extportRowsW_XPI.SharedFace → TopologicalSpace.Opens carrierW_XPI.Carrier}

/-- Under any seam–face link of the instance there is exactly one torus seam. -/
theorem torusSeamCount_XPI (sf : SeamFacesLink extportRowsW_XPI V vlink O S F N) :
    S.torusSeamCount = 1 := by
  have h := Nat.card_congr sf.torusEquiv
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [h]
  have : Unique {σ : extportRowsW_XPI.SharedFace // extportRowsW_XPI.sharedShape σ = .torus} :=
    ⟨⟨⟨sharedFace_XPI, sharedShape_XPI⟩⟩, fun τ => Subtype.ext (sharedFace_eq_XPI τ.1)⟩
  exact Nat.card_unique

/-- Under any seam–face link of the instance there is no sphere seam. -/
theorem sphereSeamCount_XPI (sf : SeamFacesLink extportRowsW_XPI V vlink O S F N) :
    S.sphereSeamCount = 0 := by
  have h := Nat.card_congr sf.sphereEquiv
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [h]
  have : IsEmpty {σ : extportRowsW_XPI.SharedFace //
      extportRowsW_XPI.sharedShape σ = .sphere} := ⟨fun τ => by
    have h2 := τ.2
    rw [sharedFace_eq_XPI τ.1, sharedShape_XPI] at h2
    exact FaceShape.noConfusion h2⟩
  exact Nat.card_of_isEmpty

/-- The two model faces of a band are different. -/
theorem bandModelFace_injective_XPI (B : BandRadii_XPI) : Injective (bandModelFace_XPI B) := by
  intro b b' h
  have h1 : bandEnd_XPI B b (1, 1) ∈ range (bandEnd_XPI B b') := by
    change bandEnd_XPI B b (1, 1) ∈ (bandModelFace_XPI B b').1
    rw [← h]
    exact mem_range_self _
  obtain ⟨t, ht⟩ := h1
  have h2 := congrArg (bandCoord_XPI B) ht
  rw [bandCoord_bandEnd_XPI, bandCoord_bandEnd_XPI] at h2
  cases b <;> cases b' <;> simp_all

/-- The model faces of a band: exactly its two ends. -/
def bandFaceEquiv_XPI (B : BandRadii_XPI) : Bool ≃ ModelBoundaryFace (bandPiece_XPI B) :=
  Equiv.ofBijective (bandModelFace_XPI B) ⟨bandModelFace_injective_XPI B, fun G => by
    rcases bandModelFace_cases_XPI B G with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩⟩

theorem nat_card_bandFace_XPI (B : BandRadii_XPI) :
    Nat.card (ModelBoundaryFace (bandPiece_XPI B)) = 2 := by
  rw [← Nat.card_congr (bandFaceEquiv_XPI B), Nat.card_eq_fintype_card, Fintype.card_bool]

/-- Every row piece of the instance has two model faces. -/
theorem nat_card_rowFace_XPI (a : extportRowsW_XPI.slim.RowIndex) :
    Nat.card (ModelBoundaryFace (extportRowsW_XPI.rowPiece a)) = 2 := by
  rcases a with i | b | j
  · exact i.elim0
  · exact nat_card_bandFace_XPI (cuspRadii_XPI b)
  · exact nat_card_bandFace_XPI slimRadii_XPI

/-- Under any seam–face link of the instance there are exactly six faces (two per vertex). -/
theorem faceCount_XPI (sf : SeamFacesLink extportRowsW_XPI V vlink O S F N) : F.faceCount = 6 := by
  have hv : ∀ v : Fin V.vertexCount, Nat.card (ModelBoundaryFace (V.vertex v).piece) = 2 :=
    fun v => by
      rw [vlink.vertex_piece v]
      exact nat_card_rowFace_XPI _
  have : ∀ v : Fin V.vertexCount, Finite (ModelBoundaryFace (V.vertex v).piece) := fun v =>
    Nat.finite_of_card_ne_zero (by rw [hv v]; norm_num)
  have h := Nat.card_congr sf.faceEquiv
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_sigma] at h
  rw [h]
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [vertexCount_XPI vlink]

end SeamFaceCounts

/-- **`exists_seams_faces_GSF` on the instance**: for every vertex / port layer pair and every safe
shared family, the seam layer has one torus seam and no sphere seam, the face layer six faces; each
port is a face of kind `external`; the torus seam bounds a face on each side. -/
theorem seams_faces_XPI {V : VertexLayer carrierW_XPI} (vlink : VertexModelLink extportRowsW_XPI V)
    {O : PortLayer carrierW_XPI portsE_XPI V} (olink : PortModelLink extportRowsW_XPI vlink O)
    (circ : CircleRegion carrierW_XPI)
    (N : extportRowsW_XPI.SharedFace → TopologicalSpace.Opens carrierW_XPI.Carrier)
    (hN : SharedSafe extportRowsW_XPI N) :
    ∃ S : SeamLayer carrierW_XPI V circ, ∃ F : FaceLayer carrierW_XPI portsE_XPI V S O,
      Nonempty (SeamFacesLink extportRowsW_XPI V vlink O S F N) ∧
      S.torusSeamCount = 1 ∧ S.sphereSeamCount = 0 ∧ F.faceCount = 6 ∧
      (∀ i, ∃ f, F.faceKind f = .external i ∧ F.face f = range (portsE_XPI.torusMap i)) ∧
      ∀ (c : Fin S.torusSeamCount) (b : Bool), ∃ f, F.faceKind f = .torusSeam c b := by
  obtain ⟨S, F, ⟨sf⟩⟩ := exists_seams_faces_GSF extportRowsW_XPI V vlink circ O olink N hN
  refine ⟨S, F, ⟨sf⟩, torusSeamCount_XPI sf, sphereSeamCount_XPI sf, faceCount_XPI sf, ?_, ?_⟩
  · intro i
    obtain ⟨f, hf⟩ := F.external_face i
    exact ⟨f, hf, (F.face_external f i hf).1⟩
  · intro c b
    obtain ⟨f, -, hf⟩ := F.torusSeam_face c b (sf.torusOwner c b) (sf.torusSide_eq c b)
    exact ⟨f, hf⟩

/-! ## The labelled circle faces and the trace atlas -/

/-- The two labelled circle faces: `0` = the new slim end (`‖w‖ = 3/2`), `1` = the internal face of
the outer cusp (`‖w‖ = 2`). -/
def circleFaceFn_XPI : Fin 2 → extportRowsW_XPI.CircleFace :=
  ![.horizontal newEndFace_XPI, .horizontal cusp0Face_XPI]

/-- The index of a labelled circle face. -/
def circleFaceIdx_XPI : extportRowsW_XPI.CircleFace → Fin 2
  | .horizontal (.inl _) => 1
  | .horizontal (.inr _) => 0
  | .vertical c => isEmptyElim c

/-- **The labelled circle faces of the instance**: exactly two, both horizontal. -/
def circleFaceEquiv_XPI : Fin 2 ≃ extportRowsW_XPI.CircleFace where
  toFun := circleFaceFn_XPI
  invFun := circleFaceIdx_XPI
  left_inv i := by
    fin_cases i <;> rfl
  right_inv f := by
    rcases f with F | c
    · rcases residualFace_cases_XPI F with rfl | rfl <;> rfl
    · exact isEmptyElim c

theorem circleFaceEquiv_zero_XPI : circleFaceEquiv_XPI 0 = .horizontal newEndFace_XPI :=
  rfl

theorem circleFaceEquiv_one_XPI : circleFaceEquiv_XPI 1 = .horizontal cusp0Face_XPI :=
  rfl

/-- Every labelled circle face is one of the two horizontal faces. -/
theorem circleFace_cases_XPI (f : extportRowsW_XPI.CircleFace) :
    f = .horizontal newEndFace_XPI ∨ f = .horizontal cusp0Face_XPI := by
  rw [← circleFaceEquiv_XPI.apply_symm_apply f]
  generalize circleFaceEquiv_XPI.symm f = i
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem nat_card_circleFace_XPI : Nat.card extportRowsW_XPI.CircleFace = 2 := by
  rw [← Nat.card_congr circleFaceEquiv_XPI, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The trace of a horizontal face of radius `ρ ∈ [3/2, 2]`. -/
theorem baseTrace_horizontal_XPI {F : extportSlim_XPI.ResidualFace} {ρ : ℝ}
    (hF : extportSlim_XPI.residualSet F = {x | rad_XPI x = ρ}) (h1 : 3 / 2 ≤ ρ) (h2 : ρ ≤ 2) :
    extportRowsW_XPI.baseTrace (.horizontal F) = {c | ‖c.val‖ = ρ} := by
  ext c
  constructor
  · intro hc
    have hc' : extportCircle_XPI.fibre c ⊆ extportSlim_XPI.residualSet F := hc.2
    rw [hF] at hc'
    exact fibre_subset_iff_XPI.mp hc'
  · intro h
    have h' : ‖c.val‖ = ρ := h
    refine ⟨?_, ?_⟩
    · change 3 / 2 ≤ ‖c.val‖ ∧ ‖c.val‖ ≤ 2
      rw [h']
      exact ⟨h1, h2⟩
    · change extportCircle_XPI.fibre c ⊆ extportSlim_XPI.residualSet F
      rw [hF]
      exact fibre_subset_iff_XPI.mpr h'

/-- **The trace of the new slim end**: the circle `‖w‖ = 3/2`. -/
theorem baseTrace_newEnd_XPI :
    extportRowsW_XPI.baseTrace (.horizontal newEndFace_XPI) = {c | ‖c.val‖ = 3 / 2} :=
  baseTrace_horizontal_XPI residualSet_newEnd_XPI le_rfl (by norm_num)

/-- **The trace of the outer cusp's internal face**: the circle `‖w‖ = 2`. -/
theorem baseTrace_cusp0_XPI :
    extportRowsW_XPI.baseTrace (.horizontal cusp0Face_XPI) = {c | ‖c.val‖ = 2} :=
  baseTrace_horizontal_XPI residualSet_cusp0_XPI (by norm_num) le_rfl

/-- **F2 (`frontier_cbase_eq_iUnion_baseTrace_GTR`) on the instance**: `∂C₁` is the union of the
two circles. -/
theorem frontier_cbase_XPI :
    frontier extportRowsW_XPI.circle.cbase = {c | ‖c.val‖ = 3 / 2} ∪ {c | ‖c.val‖ = 2} := by
  rw [extportRowsW_XPI.frontier_cbase_eq_iUnion_baseTrace_GTR, ← baseTrace_newEnd_XPI,
    ← baseTrace_cusp0_XPI]
  ext c
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨f, hf⟩
    rcases circleFace_cases_XPI f with rfl | rfl
    · exact Or.inl hf
    · exact Or.inr hf
  · rintro (h | h)
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

/-- **The labelled base-trace atlas on the instance**: at every frontier point of `C₁` the atlas
of `labelled_baseTrace_atlas_GTR` carries exactly ONE label (no corner of the circle base). -/
theorem baseTrace_atlas_one_label_XPI {c : extportRowsW_XPI.circle.Base}
    (hc : c ∈ frontier extportRowsW_XPI.circle.cbase) :
    ∃ U : TopologicalSpace.Opens extportRowsW_XPI.circle.Base, c ∈ U ∧
      ∃ L : Finset extportRowsW_XPI.CircleFace, (∀ f, f ∈ L ↔ c ∈ extportRowsW_XPI.baseTrace f) ∧
        L.card = 1 := by
  obtain ⟨U, hcU, L, -, hL, -⟩ := extportRowsW_XPI.labelled_baseTrace_atlas_GTR hc
  refine ⟨U, hcU, L, hL, ?_⟩
  rw [frontier_cbase_XPI] at hc
  rw [Finset.card_eq_one]
  rcases hc with h | h
  · refine ⟨.horizontal newEndFace_XPI, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun f hf => ?_⟩⟩
    · rw [hL, baseTrace_newEnd_XPI]
      exact h
    · rw [hL] at hf
      rcases circleFace_cases_XPI f with rfl | rfl
      · rfl
      · rw [baseTrace_cusp0_XPI] at hf
        change ‖c.val‖ = 2 at hf
        change ‖c.val‖ = 3 / 2 at h
        rw [h] at hf
        norm_num at hf
  · refine ⟨.horizontal cusp0Face_XPI, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun f hf => ?_⟩⟩
    · rw [hL, baseTrace_cusp0_XPI]
      exact h
    · rw [hL] at hf
      rcases circleFace_cases_XPI f with rfl | rfl
      · rw [baseTrace_newEnd_XPI] at hf
        change ‖c.val‖ = 3 / 2 at hf
        change ‖c.val‖ = 2 at h
        rw [h] at hf
        norm_num at hf
      · rfl

/-! ## Global face functions V2 -/

/-- **`exists_globalFaceFunctions_GGFF` on the instance.** -/
theorem exists_globalFaces_XPI : Nonempty (GlobalFaceFunctionsV2 extportRowsW_XPI) :=
  exists_globalFaceFunctions_GGFF extportRowsW_XPI

/-- Every global face family of the instance has exactly two faces. -/
theorem globalFaces_card_XPI (GF : GlobalFaceFunctionsV2 extportRowsW_XPI) : Nat.card GF.Face = 2 :=
  (Nat.card_congr GF.actualFace).trans nat_card_circleFace_XPI

/-- No double zero: on the base of any global face family two different face functions never
vanish together (a double zero would be a registered edge endpoint, and there is none). -/
theorem globalFaces_no_double_zero_XPI (GF : GlobalFaceFunctionsV2 extportRowsW_XPI)
    {c : extportRowsW_XPI.circle.Base} (hc : c ∈ GF.base) {f f' : GF.Face} (hne : f ≠ f')
    (h0 : GF.fn f c = 0) (h0' : GF.fn f' c = 0) : False := by
  obtain ⟨e, -⟩ := GF.double_registered c hc f f' hne h0 h0'
  exact isEmptyElim e

/-- The zero set of a face function in `C₁` is the trace of its face (`face_eq`), here an explicit
circle. -/
theorem globalFaces_zero_XPI (GF : GlobalFaceFunctionsV2 extportRowsW_XPI) (i : Fin 2) :
    {c | c ∈ extportRowsW_XPI.circle.cbase ∧
        GF.fn (GF.actualFace.symm (circleFaceEquiv_XPI i)) c = 0} =
      {c | ‖c.val‖ = ![3 / 2, 2] i} := by
  rw [GF.face_eq, Equiv.apply_symm_apply]
  fin_cases i
  · exact baseTrace_newEnd_XPI
  · exact baseTrace_cusp0_XPI

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
