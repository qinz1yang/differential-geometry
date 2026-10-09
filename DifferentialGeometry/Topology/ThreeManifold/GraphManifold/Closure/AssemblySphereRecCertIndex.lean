import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertCircle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapInterval

/-!
# FC42 sphere recursion, packet S4 (group G3): transport images, index sets, the new vertices

Lane ASM-SPH2b (review 40 §2.4 "third layer"; plan in `build-logs/resume/state-ASM-SPH2.md`).
For a certificate `D`, a sphere seam `c`, cut-and-capped data `X` of `c`, a component
decomposition `DQ` of the capped carrier and a component `i`:

* transport images (`X.transport : W \ Σ ≅ Q \ caps`): intersections, disjointness, interiors,
  and the interior-disjointness of `T '' (A \ Σ) ∪ K` for cap parts `K` (`disjoint_interior_lift`);
* `compLift A = val ⁻¹' (T '' A)`, the trace in the component carrier;
* the index sets of the inherited certificate: vertices, handles, edge-circle pieces, torus seams,
  the other sphere seams, faces (those not of kind `sphereSeam c _`), arcs and loops, each
  renumbered by `Finite.equivFin`; the translated face kinds `kindMap`;
* the new vertex family `ccVertex`: the lifted vertices, a capped `S² × I` side replaced by the
  ball of S3a (`exists_capUnion_ball_of_sphereInterval`); its image and model-boundary image as
  traces of transport images (`image_ccVertex`, `boundaryImage_ccVertex`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASMSPH2b : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASMSPH2b : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASMSPH2b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMSPH2b : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## Transport images -/

theorem SphereSeam.sdiff_zeroSphere_subset {W : CompactCarrier.{u}} (S : SphereSeam W)
    (A : Set W.Carrier) : A \ S.zeroSphere ⊆ S.zeroSphereᶜ :=
  fun _ hx => hx.2

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

theorem injOn_transport : InjOn X.transport S.zeroSphereᶜ :=
  X.transport.toPartialEquiv.injOn

theorem transport_notMem_capSet {x : W.Carrier} (hx : x ∉ S.zeroSphere) :
    X.transport x ∉ X.capSet :=
  X.transport.map_source hx

theorem transport_image_subset_compl_capSet {A : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ) :
    X.transport '' A ⊆ X.capSetᶜ := by
  rintro _ ⟨x, hx, rfl⟩
  exact X.transport_notMem_capSet (hA hx)

theorem transport_symm_transport {x : W.Carrier} (hx : x ∉ S.zeroSphere) :
    X.transport.symm (X.transport x) = x :=
  X.transport.toPartialEquiv.left_inv hx

theorem transport_transport_symm {y : X.Q.Carrier} (hy : y ∉ X.capSet) :
    X.transport (X.transport.symm y) = y :=
  X.transport.toPartialEquiv.right_inv hy

theorem transport_symm_notMem {y : X.Q.Carrier} (hy : y ∉ X.capSet) :
    X.transport.symm y ∉ S.zeroSphere :=
  X.transport.map_target hy

theorem transport_image_inter {A B : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ)
    (hB : B ⊆ S.zeroSphereᶜ) : X.transport '' (A ∩ B) = X.transport '' A ∩ X.transport '' B :=
  X.injOn_transport.image_inter hA hB

theorem disjoint_transport_image {A B : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ)
    (hB : B ⊆ S.zeroSphereᶜ) (h : Disjoint A B) :
    Disjoint (X.transport '' A) (X.transport '' B) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← X.transport_image_inter hA hB,
    Set.disjoint_iff_inter_eq_empty.mp h, image_empty]

theorem transport_mem_image_iff {A : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ) {x : W.Carrier}
    (hx : x ∉ S.zeroSphere) : X.transport x ∈ X.transport '' A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← X.injOn_transport (hA hy) hx hyx]
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem interior_transport_image {A : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ) :
    interior (X.transport '' A) = X.transport '' interior A :=
  (OpenPartialHomeomorph.image_interior_of_subset_source X.transport.toOpenPartialHomeomorph
    hA).symm

/-- **Interiors of transported sets with cap parts.** If `A`, `B` have disjoint interiors and
`K`, `K'` are disjoint parts of the caps, then `T '' (A \ Σ) ∪ K` and `T '' (B \ Σ) ∪ K'` have
disjoint interiors. -/
theorem disjoint_interior_lift {A B : Set W.Carrier} {K K' : Set X.Q.Carrier}
    (hK : K ⊆ X.capSet) (hK' : K' ⊆ X.capSet) (hKK : Disjoint K K')
    (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (X.transport '' (A \ S.zeroSphere) ∪ K))
      (interior (X.transport '' (B \ S.zeroSphere) ∪ K')) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  set U := interior (X.transport '' (A \ S.zeroSphere) ∪ K) ∩
    interior (X.transport '' (B \ S.zeroSphere) ∪ K') with hUdef
  have hU : IsOpen U := isOpen_interior.inter isOpen_interior
  have hsub : U ⊆ X.transport '' ((A \ S.zeroSphere) ∩ (B \ S.zeroSphere)) := by
    rintro x ⟨hx, hx'⟩
    rcases interior_subset hx with ⟨a, ha, rfl⟩ | hxK
    · rcases interior_subset hx' with ⟨b, hb, hab⟩ | hxK'
      · rw [X.transport_image_inter (S.sdiff_zeroSphere_subset A) (S.sdiff_zeroSphere_subset B)]
        exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      · exact (X.transport_notMem_capSet ha.2 (hK' hxK')).elim
    · rcases interior_subset hx' with ⟨b, hb, rfl⟩ | hxK'
      · exact (X.transport_notMem_capSet hb.2 (hK hxK)).elim
      · exact (Set.disjoint_left.mp hKK hxK hxK').elim
  have hUT : U ⊆ X.capSetᶜ := hsub.trans (X.transport_image_subset_compl_capSet
    (inter_subset_left.trans (S.sdiff_zeroSphere_subset A)))
  have hopen : IsOpen (X.transport.symm '' U) :=
    X.transport.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target hU hUT
  have hAB : X.transport.symm '' U ⊆ A ∩ B := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ⟨ha, hb⟩, rfl⟩ := hsub hx
    rw [X.transport_symm_transport ha.2]
    exact ⟨ha.1, hb.1⟩
  have hyU : y ∈ U := ⟨hy, hy'⟩
  have hmem : X.transport.symm y ∈ X.transport.symm '' U := ⟨y, hyU, rfl⟩
  exact Set.disjoint_left.mp h
    (interior_maximal (hAB.trans inter_subset_left) hopen hmem)
    (interior_maximal (hAB.trans inter_subset_right) hopen hmem)

end SphereCutCapped

/-! ## Connected sets and the pieces of a component decomposition -/

section Pieces

variable {Q : CompactCarrier.{u}} {DQ : Q.Components} {i : Fin DQ.count}

/-- A preconnected set meeting the piece `i` lies in it. -/
theorem subset_piece_of_mem {A : Set Q.Carrier} (hA : IsPreconnected A) {x : Q.Carrier}
    (hx : x ∈ A) (hxi : x ∈ DQ.piece i) : A ⊆ DQ.piece i := by
  have h := subset_piece_pointComp (DQ := DQ) hA hx
  rwa [pointComp_eq_of_mem hxi] at h

/-- Two pieces sharing a point are the same. -/
theorem piece_eq_of_mem {x : Q.Carrier} {j : Fin DQ.count} (hi : x ∈ DQ.piece i)
    (hj : x ∈ DQ.piece j) : i = j :=
  (pointComp_eq_of_mem hi).symm.trans (pointComp_eq_of_mem hj)

end Pieces

/-- The closed disk times the unit interval is connected. -/
theorem connectedSpace_closedCell_two_prod_Icc :
    ConnectedSpace (ClosedCell 2 × Icc (0 : ℝ) 1) := by
  have hset : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp
  have hc : IsConnected {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} := by
    rw [hset]
    exact (convex_closedBall 0 1).isConnected (Metric.nonempty_closedBall.mpr zero_le_one)
  have h1 : ConnectedSpace (ClosedCell 2) := isConnected_iff_connectedSpace.mp hc
  have h2 : ConnectedSpace (Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc zero_le_one)
  infer_instance

theorem isPreconnected_signedCollarSource : IsPreconnected signedCollarSource := by
  have h : signedCollarSource = (univ : Set Torus) ×ˢ Ioo (-1 : ℝ) 1 := by
    ext p
    simp [signedCollarSource]
  rw [h]
  exact isPreconnected_univ.prod isPreconnected_Ioo

theorem isPreconnected_sphereSignedCollarSource :
    IsPreconnected (sphereSignedCollarSource.{u}) := by
  have := closureSphere_connectedSpace.{u}
  exact isPreconnected_univ.prod isPreconnected_Ioo

theorem TorusSeam.isPreconnected_target {W : CompactCarrier.{u}} (T : TorusSeam W) :
    IsPreconnected T.collar.target := by
  rw [← T.collar.toPartialEquiv.image_source_eq_target]
  exact (T.source_eq ▸ isPreconnected_signedCollarSource).image _ T.collar.contMDiffOn.continuousOn

theorem SphereSeam.isPreconnected_target {W : CompactCarrier.{u}} (S : SphereSeam W) :
    IsPreconnected S.collar.target := by
  rw [← S.collar.toPartialEquiv.image_source_eq_target]
  exact (S.source_eq ▸ isPreconnected_sphereSignedCollarSource).image _
    S.collar.contMDiffOn.continuousOn

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E) (DQ : X.Q.Components)

/-- A cap lies in the component of its cut sphere. -/
theorem range_cap_subset_spherePiece (j : Fin 2) :
    range (X.capping.cap (Fin.cast X.h2.symm j)) ⊆
      DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm j)) := by
  have := closedCell_three_connectedSpace
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  exact subset_piece_of_mem (isConnected_range (X.capping.cap _).continuous).isPreconnected
    (X.core_cutSphere_mem_range_cap j z₀) (X.sphere_mem_spherePiece DQ _ z₀)

/-- A transported image of a preconnected set off the seam sphere is preconnected. -/
theorem isPreconnected_transport_image {A : Set W.Carrier} (hA : IsPreconnected A)
    (hAS : A ⊆ S.zeroSphereᶜ) : IsPreconnected (X.transport '' A) :=
  hA.image _ (X.transport.contMDiffOn.continuousOn.mono hAS)

end SphereCutCapped

/-! ## The index sets of the inherited certificate -/

/-- The renumbering of the elements of a finite type satisfying a predicate. -/
def ccEquiv {α : Type*} [Finite α] (P : α → Prop) : Fin (Nat.card {a // P a}) ≃ {a // P a} :=
  (Finite.equivFin _).symm

theorem ccEquiv_symm_apply_val {α : Type*} [Finite α] {P : α → Prop} (a : α) (h : P a) :
    (ccEquiv P ((ccEquiv P).symm ⟨a, h⟩)).1 = a := by
  rw [Equiv.apply_symm_apply]

theorem ccEquiv_symm_injective {α : Type*} [Finite α] {P : α → Prop} {a b : α} {ha : P a}
    {hb : P b} (h : (ccEquiv P).symm ⟨a, ha⟩ = (ccEquiv P).symm ⟨b, hb⟩) : a = b :=
  congrArg Subtype.val ((ccEquiv P).symm.injective h)

theorem ccEquiv_symm_val {α : Type*} [Finite α] {P : α → Prop} (k : Fin (Nat.card {a // P a})) :
    (ccEquiv P).symm ⟨(ccEquiv P k).1, (ccEquiv P k).2⟩ = k := by
  rw [Subtype.coe_eta, Equiv.symm_apply_apply]

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- A vertex of the component `i`: its lift lies in the piece `i`. -/
def ccV (k : Fin D.vertexCount) : Prop :=
  range (D.liftVertex c X k).map ⊆ DQ.piece i

/-- A handle of the component `i`. -/
def ccH (h : Fin D.handleCount) : Prop :=
  range (D.liftHandle c X h).map ⊆ DQ.piece i

/-- An edge-circle piece of the component `i`. -/
def ccE (e : Fin D.edgeCircleCount) : Prop :=
  range (D.liftEdgeCircle c X e).piece.map ⊆ DQ.piece i

/-- A torus seam of the component `i`. -/
def ccT (d : Fin D.torusSeamCount) : Prop :=
  X.transport '' (D.torusSeam d).collar.target ⊆ DQ.piece i

/-- Another sphere seam of the component `i`. -/
def ccS (c' : Fin D.sphereSeamCount) : Prop :=
  c' ≠ c ∧ X.transport '' (D.sphereSeam c').collar.target ⊆ DQ.piece i

/-- A face of the component `i`: not a side of the cut seam, owner in the component. -/
def ccF (f : Fin D.faceCount) : Prop :=
  (∀ b, D.faceKind f ≠ .sphereSeam c b) ∧ D.ccV c X DQ i (D.faceOwner f)

/-- An arc of the component `i` (owner face in the component). -/
def ccA (j : Fin D.arcFaceCount) : Prop :=
  D.ccF c X DQ i (D.arcOwner j)

/-- A loop of the component `i` (owner face in the component). -/
def ccL (j : Fin D.loopFaceCount) : Prop :=
  D.ccF c X DQ i (D.loopOwner j)

end DecompositionCertificate

/-! ## The seam sphere and the side vertices -/

theorem Vertex.boundaryImage_subset_image' {W : CompactCarrier.{u}} (v : Vertex W) :
    v.boundaryImage ⊆ v.image := by
  rw [Vertex.image_eq_range_piece]
  exact image_subset_range _ _

theorem Vertex.boundaryImage_zero {W : CompactCarrier.{u}} (P : PieceEmbedding W) (m : ZeroModel P) :
    (Vertex.zero P m).boundaryImage = P.map '' (𝓡∂ 3).boundary P.Piece :=
  rfl

theorem PieceEmbedding.image_toComponent {Q : CompactCarrier.{u}} {DQ : Q.Components}
    {i : Fin DQ.count} (P : PieceEmbedding Q) (h : range P.map ⊆ (DQ.piece i : Set Q.Carrier))
    (A : Set (P.toComponent h).Piece) :
    (P.toComponent h).map '' A = Subtype.val ⁻¹' (P.map '' A) :=
  image_componentRestrict h A

/-- A vertex is a ball if a re-embedding of it is. -/
theorem Vertex.isBall_of_isBall_ofMap {W W' : CompactCarrier.{u}} {v : Vertex W}
    {g : v.piece.Piece → W'.Carrier} {hs : ContMDiff (𝓡∂ 3) W'.model ∞ g}
    {hb : ∀ q, Bijective (mfderiv (𝓡∂ 3) W'.model g q)} {hi : Injective g}
    (h : (v.ofMap g hs hb hi).IsBall) : v.IsBall := by
  obtain ⟨P', e', h⟩ := h
  cases v with
  | zero P m =>
    cases m with
    | ball e => exact ⟨P, e, rfl⟩
    | solidTorus e => cases h
    | twistedIBundle e => cases h
    | puncturedRP3 c f hf hr => cases h
  | closedZero C => cases h
  | slim P m => cases h
  | cuspCore P e => cases h

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- The seam sphere lies in the image of each side vertex. -/
theorem zeroSphere_subset_image (b : Bool) :
    (D.sphereSeam c).zeroSphere ⊆ (D.vertex (D.sphereSide c b)).image := by
  rintro _ ⟨z, rfl⟩
  cases b
  · exact D.sphereSide_pos c z 0 le_rfl zero_lt_one
  · exact D.sphereSide_neg c z 0 le_rfl (by norm_num)

/-- A face that is not a side of the cut seam avoids the seam sphere. -/
theorem face_disjoint_zeroSphere {f : Fin D.faceCount} (hf : ∀ b, D.faceKind f ≠ .sphereSeam c b) :
    Disjoint (D.face f) (D.sphereSeam c).zeroSphere := by
  obtain ⟨f₀, -, hf₀⟩ := D.sphereSeam_face c true
  have hface : D.face f₀ = (D.sphereSeam c).zeroSphere := (D.face_sphereSeam f₀ c true hf₀).1
  rw [← hface]
  refine D.face_disjoint f f₀ (fun h => hf true (h ▸ hf₀)) ?_ ?_
  · rintro c' b' ⟨h1, h2⟩
    rw [hf₀] at h2
    injection h2 with hc hb
    subst hc
    cases b'
    · exact hf false h1
    · simp at hb
  · rintro c' b' ⟨-, h2⟩
    rw [hf₀] at h2
    cases h2

theorem face_subset_compl_zeroSphere {f : Fin D.faceCount}
    (hf : ∀ b, D.faceKind f ≠ .sphereSeam c b) : D.face f ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  fun _ hx hxS => Set.disjoint_left.mp (D.face_disjoint_zeroSphere c hf) hx hxS

/-- The transport of a vertex image off the seam sphere lies in the lift. -/
theorem transport_image_subset_range_liftVertex (k : Fin D.vertexCount) :
    X.transport '' ((D.vertex k).image \ (D.sphereSeam c).zeroSphere) ⊆
      range (D.liftVertex c X k).map := by
  rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
  rw [Vertex.image_eq_range_piece] at hy
  obtain ⟨q, rfl⟩ := hy
  exact ⟨q, D.liftVertex_map_of_notMem c X k hyS⟩

/-- The lift of a vertex: the transport off the seam sphere, the caps on it. -/
theorem range_liftVertex_subset (k : Fin D.vertexCount) :
    range (D.liftVertex c X k).map ⊆
      X.transport '' ((D.vertex k).image \ (D.sphereSeam c).zeroSphere) ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c k)))) := by
  rintro _ ⟨q, rfl⟩
  by_cases hq : (D.vertex k).piece.map q ∈ (D.sphereSeam c).zeroSphere
  · obtain ⟨z, hz⟩ := hq
    right
    change X.capping.core (X.sideLift _ ((D.vertex k).piece.map q)) ∈ _
    rw [← hz, X.sideLift_of_mem]
    exact X.core_cutSphere_mem_range_cap _ z
  · left
    refine ⟨_, ⟨?_, hq⟩, (D.liftVertex_map_of_notMem c X k hq).symm⟩
    rw [Vertex.image_eq_range_piece]
    exact ⟨q, rfl⟩

/-- A vertex that is not a side of the cut seam is lifted by the transport. -/
theorem range_liftVertex_of_notSide {k : Fin D.vertexCount} (hk : ∀ b, k ≠ D.sphereSide c b) :
    range (D.liftVertex c X k).map =
      X.transport '' ((D.vertex k).image \ (D.sphereSeam c).zeroSphere) := by
  have hdis := D.vertex_image_disjoint_sphereCollar (hk true) (hk false)
  have hsd : (D.vertex k).image \ (D.sphereSeam c).zeroSphere = (D.vertex k).image :=
    sdiff_eq_left.mpr (hdis.mono_right (D.sphereSeam c).zeroSphere_subset_target)
  rw [hsd]
  exact D.range_liftVertex_of_ne c X (hk true) (hk false)

/-- The model-boundary image of a lifted vertex off the seam sphere. -/
theorem image_boundary_liftVertex_of_notMem (k : Fin D.vertexCount)
    {A : Set (D.vertex k).piece.Piece}
    (hA : ∀ q ∈ A, (D.vertex k).piece.map q ∉ (D.sphereSeam c).zeroSphere) :
    (D.liftVertex c X k).map '' A = X.transport '' ((D.vertex k).piece.map '' A) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, (D.liftVertex_map_of_notMem c X k (hA q hq)).symm⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, D.liftVertex_map_of_notMem c X k (hA q hq)⟩

/-- A side vertex of the component `i` has its cap in the component `i`. -/
theorem spherePiece_eq_of_ccV (b : Bool) (hk : D.ccV c X DQ i (D.sphereSide c b)) :
    X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i := by
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have hz := D.zeroSphere_subset_image c b ⟨z₀, rfl⟩
  rw [Vertex.image_eq_range_piece] at hz
  obtain ⟨q, hq⟩ := hz
  have h1 : X.capping.core (X.cutSphere (sideCopy b) z₀) ∈ DQ.piece i := by
    rw [← D.liftVertex_map_of_mem c X b hq]
    exact hk ⟨q, rfl⟩
  exact (piece_eq_of_mem h1 (X.sphere_mem_spherePiece DQ _ z₀)).symm

/-- The lifted vertex (same piece manifold and model, the lifted map). -/
def liftVertexV (k : Fin D.vertexCount) : Vertex X.Q :=
  (D.vertex k).ofMap (D.liftVertex c X k).map (D.liftVertex c X k).smooth
    (D.liftVertex c X k).mfderiv_bijective (D.liftVertex c X k).injective

theorem image_liftVertexV (k : Fin D.vertexCount) :
    (D.liftVertexV c X k).image = range (D.liftVertex c X k).map :=
  Vertex.image_ofMap _ _ _ _ _

theorem boundaryImage_liftVertexV (k : Fin D.vertexCount) :
    (D.liftVertexV c X k).boundaryImage =
      (D.liftVertex c X k).map '' (𝓡∂ 3).boundary (D.vertex k).piece.Piece :=
  Vertex.boundaryImage_ofMap _ _ _ _ _

/-- The `S² × I` hypothesis of a side. -/
abbrev SideSphereInterval (b : Bool) : Prop :=
  ∃ (P : PieceEmbedding W)
    (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
    D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)

/-- The ball of S3a: a capped `S² × I` side together with its cap. -/
def ccBallPiece (b : Bool) (hb : D.SideSphereInterval c b) : PieceEmbedding X.Q :=
  (D.exists_capUnion_ball_of_sphereInterval c X b hb.choose_spec.choose_spec).choose

/-- The ball model of `ccBallPiece`. -/
def ccBallModel (b : Bool) (hb : D.SideSphereInterval c b) :
    (D.ccBallPiece c X b hb).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  (D.exists_capUnion_ball_of_sphereInterval c X b hb.choose_spec.choose_spec).choose_spec.choose

theorem range_ccBallPiece (b : Bool) (hb : D.SideSphereInterval c b) :
    range (D.ccBallPiece c X b hb).map = range (D.liftVertex c X (D.sphereSide c b)).map ∪
      range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) :=
  (D.exists_capUnion_ball_of_sphereInterval c X b
    hb.choose_spec.choose_spec).choose_spec.choose_spec.1

theorem boundary_ccBallPiece (b : Bool) (hb : D.SideSphereInterval c b) :
    (D.ccBallPiece c X b hb).map '' (𝓡∂ 3).boundary (D.ccBallPiece c X b hb).Piece =
      X.transport '' ((D.vertex (D.sphereSide c b)).boundaryImage \
        (D.sphereSeam c).zeroSphere) :=
  (D.exists_capUnion_ball_of_sphereInterval c X b
    hb.choose_spec.choose_spec).choose_spec.choose_spec.2

/-- The ball of a side of the component `i` lies in the piece `i`. -/
theorem range_ccBallPiece_subset (b : Bool) (hb : D.SideSphereInterval c b)
    (hk : D.ccV c X DQ i (D.sphereSide c b)) :
    range (D.ccBallPiece c X b hb).map ⊆ DQ.piece i := by
  rw [D.range_ccBallPiece]
  refine union_subset hk ?_
  have h := X.range_cap_subset_spherePiece DQ (sideCopy b)
  rwa [D.spherePiece_eq_of_ccV c X DQ i b hk] at h

/-- The range of the ball: the transported side off the seam sphere and the cap. -/
theorem range_ccBallPiece_eq (b : Bool) (hb : D.SideSphereInterval c b) :
    range (D.ccBallPiece c X b hb).map =
      X.transport '' ((D.vertex (D.sphereSide c b)).image \ (D.sphereSeam c).zeroSphere) ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) := by
  rw [D.range_ccBallPiece]
  apply Subset.antisymm
  · refine union_subset ?_ subset_union_right
    have h := D.range_liftVertex_subset c X (D.sphereSide c b)
    rwa [D.vertexSide_sphereSide] at h
  · exact union_subset_union_left _ (D.transport_image_subset_range_liftVertex c X _)

end DecompositionCertificate

/-! ## The new vertex family -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

theorem _root_.GC.GraphManifold.Assembly.sideCopy_injective : Injective sideCopy := by
  intro b b' h
  cases b <;> cases b' <;> first | rfl | exact absurd h (by decide)

variable {D c} in
theorem isSide_iff {k : Fin D.vertexCount} :
    k = D.sphereSide c (D.vertexSide c k) ↔ ∃ b, k = D.sphereSide c b := by
  constructor
  · intro h
    exact ⟨_, h⟩
  · rintro ⟨b, rfl⟩
    rw [D.vertexSide_sphereSide]

theorem ne_sphereSide_of_not {k : Fin D.vertexCount}
    (h : ¬ k = D.sphereSide c (D.vertexSide c k)) (b : Bool) : k ≠ D.sphereSide c b :=
  fun hb => h (isSide_iff.mpr ⟨b, hb⟩)

theorem ccV_side {k : Fin D.vertexCount} (hs : k = D.sphereSide c (D.vertexSide c k))
    (hk : D.ccV c X DQ i k) : D.ccV c X DQ i (D.sphereSide c (D.vertexSide c k)) := by
  rw [← hs]
  exact hk

/-- The cap part of a vertex: the cap of its copy for a side of the cut seam, empty otherwise. -/
def ccCapPart (k : Fin D.vertexCount) : Set X.Q.Carrier :=
  if k = D.sphereSide c (D.vertexSide c k) then
    range (X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c k))))
  else ∅

theorem ccCapPart_subset_capSet (k : Fin D.vertexCount) : D.ccCapPart c X k ⊆ X.capSet := by
  unfold ccCapPart
  split_ifs
  · exact subset_iUnion (fun j => range (X.capping.cap j)) _
  · exact empty_subset _

theorem disjoint_ccCapPart {k k' : Fin D.vertexCount} (hkk : k ≠ k') :
    Disjoint (D.ccCapPart c X k) (D.ccCapPart c X k') := by
  unfold ccCapPart
  split_ifs with h1 h2
  · refine X.capping.cap_disjoint fun h => hkk ?_
    rw [h1, h2]
    exact congrArg (D.sphereSide c) (sideCopy_injective (Fin.cast_injective _ h))
  · exact disjoint_empty _
  · exact empty_disjoint _
  · exact empty_disjoint _

variable (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
  D.SideSphereInterval c b)

/-- **The vertex `k` of the component `i`**: a capped `S² × I` side becomes the ball of S3a,
every other vertex is lifted. -/
def ccVertexOf (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k) :
    Vertex (GC.Topology.componentCarrier X.Q DQ i) :=
  if hs : k = D.sphereSide c (D.vertexSide c k) then
    have hk' := D.ccV_side c X DQ i hs hk
    have hb := hcap _ (D.spherePiece_eq_of_ccV c X DQ i _ hk')
    .zero ((D.ccBallPiece c X _ hb).toComponent (D.range_ccBallPiece_subset c X DQ i _ hb hk'))
      (.ball (D.ccBallModel c X _ hb))
  else (D.liftVertexV c X k).toComponent (by rw [image_liftVertexV]; exact hk)

/-- **The vertex family of the inherited certificate.** -/
def ccVertex (k' : Fin (Nat.card {k // D.ccV c X DQ i k})) :
    Vertex (GC.Topology.componentCarrier X.Q DQ i) :=
  D.ccVertexOf c X DQ i hcap (ccEquiv _ k').1 (ccEquiv _ k').2

theorem image_ccVertexOf (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k) :
    (D.ccVertexOf c X DQ i hcap k hk).image = Subtype.val ⁻¹'
      (X.transport '' ((D.vertex k).image \ (D.sphereSeam c).zeroSphere) ∪ D.ccCapPart c X k) := by
  unfold ccVertexOf ccCapPart
  split_ifs with hs
  · change range (PieceEmbedding.toComponent _ _).map = _
    rw [PieceEmbedding.range_toComponent, D.range_ccBallPiece_eq, ← hs]
  · rw [Vertex.image_toComponent, image_liftVertexV,
      D.range_liftVertex_of_notSide c X (D.ne_sphereSide_of_not c hs), union_empty]

theorem boundaryImage_ccVertexOf (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k) :
    (D.ccVertexOf c X DQ i hcap k hk).boundaryImage = Subtype.val ⁻¹'
      (X.transport '' ((D.vertex k).boundaryImage \ (D.sphereSeam c).zeroSphere)) := by
  unfold ccVertexOf
  split_ifs with hs
  · rw [Vertex.boundaryImage_zero, PieceEmbedding.image_toComponent]
    have hb := D.boundary_ccBallPiece c X (D.vertexSide c k)
      (hcap _ (D.spherePiece_eq_of_ccV c X DQ i _ (D.ccV_side c X DQ i hs hk)))
    rw [← hs] at hb
    exact congrArg (Subtype.val ⁻¹' ·) hb
  · have hns := D.ne_sphereSide_of_not c hs
    have hdis := D.vertex_image_disjoint_sphereCollar (hns true) (hns false)
    have hA : ∀ q ∈ (𝓡∂ 3).boundary (D.vertex k).piece.Piece,
        (D.vertex k).piece.map q ∉ (D.sphereSeam c).zeroSphere := fun q _ hq =>
      Set.disjoint_left.mp hdis (by rw [Vertex.image_eq_range_piece]; exact ⟨q, rfl⟩)
        ((D.sphereSeam c).zeroSphere_subset_target hq)
    have hsd : (D.vertex k).boundaryImage \ (D.sphereSeam c).zeroSphere =
        (D.vertex k).boundaryImage := by
      refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
      rintro _ ⟨q, hq, rfl⟩
      exact hA q hq
    rw [Vertex.boundaryImage_toComponent, boundaryImage_liftVertexV, hsd,
      D.image_boundary_liftVertex_of_notMem c X k hA]
    rfl

theorem ccVertexOf_ne_closedZero (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (k : Fin D.vertexCount)
    (hk : D.ccV c X DQ i k) (C : ClosedZeroPiece (GC.Topology.componentCarrier X.Q DQ i)) :
    D.ccVertexOf c X DQ i hcap k hk ≠ .closedZero C := by
  unfold ccVertexOf
  split_ifs with hs
  · intro h
    cases h
  · exact Vertex.toComponent_ne_closedZero (Vertex.ofMap_ne_closedZero (hnz k) _ _ _ _) _ C

/-- A non-ball vertex of the component is a lifted vertex, and a ball only if the old one is. -/
theorem isBall_of_isBall_ccVertexOf (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k)
    (h : (D.ccVertexOf c X DQ i hcap k hk).IsBall) :
    (D.vertex k).IsBall ∨ ∃ b, k = D.sphereSide c b := by
  unfold ccVertexOf at h
  split_ifs at h with hs
  · exact Or.inr ⟨_, hs⟩
  · exact Or.inl (Vertex.isBall_of_isBall_ofMap (Vertex.isBall_of_isBall_ofMap h))

theorem isBall_ccVertexOf_of_side (k : Fin D.vertexCount) (hk : D.ccV c X DQ i k)
    (hs : k = D.sphereSide c (D.vertexSide c k)) : (D.ccVertexOf c X DQ i hcap k hk).IsBall := by
  unfold ccVertexOf
  split_ifs
  exact Vertex.isBall_zero_ball _ _

end DecompositionCertificate

/-! ## Membership in the component -/

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The transport carries the external collar targets onto the retained collar targets. -/
theorem transport_image_externalTarget (a : Fin n) :
    X.transport '' (E.collar a).target = (X.capping.retained.collar (Fin.cast X.hn.symm a)).target := by
  rw [← (E.collar a).toPartialEquiv.image_source_eq_target,
    ← (X.capping.retained.collar _).toPartialEquiv.image_source_eq_target, image_image,
    E.source_eq, X.capping.retained.source_eq]
  exact image_congr fun p hp => X.transport_externalCollar a hp

/-- The transport carries the external tori onto the retained tori. -/
theorem transport_image_range_torusMap (a : Fin n) :
    X.transport '' range (E.torusMap a) = range (X.capping.retained.torusMap (Fin.cast X.hn.symm a)) := by
  rw [← range_comp]
  exact congrArg range (funext fun t => X.transport_externalCollar a (zero_mem_halfCollarSource t))

include X in
/-- The external collar targets avoid the seam sphere. -/
theorem externalTarget_subset_compl (a : Fin n) : (E.collar a).target ⊆ S.zeroSphereᶜ := by
  intro x hx
  rw [← (E.collar a).toPartialEquiv.image_source_eq_target, E.source_eq] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact X.externalCollar_notMem_zeroSphere a hp

end SphereCutCapped

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

variable {D c X DQ i}

theorem ccV_of_mem {k : Fin D.vertexCount} {q : (D.vertex k).piece.Piece}
    (h : (D.liftVertex c X k).map q ∈ DQ.piece i) : D.ccV c X DQ i k :=
  subset_piece_of_mem (D.liftVertex c X k).isConnected_range.isPreconnected ⟨q, rfl⟩ h

theorem ccV_of_transport_mem {k : Fin D.vertexCount} {y : W.Carrier} (hy : y ∈ (D.vertex k).image)
    (hyS : y ∉ (D.sphereSeam c).zeroSphere) (h : X.transport y ∈ DQ.piece i) : D.ccV c X DQ i k := by
  obtain ⟨q, hq⟩ := D.transport_image_subset_range_liftVertex c X k ⟨y, ⟨hy, hyS⟩, rfl⟩
  exact ccV_of_mem (hq ▸ h)

theorem ccH_of_mem {h : Fin D.handleCount} {p : ClosedCell 2 × Icc (0 : ℝ) 1}
    (hp : (D.liftHandle c X h).map p ∈ DQ.piece i) : D.ccH c X DQ i h := by
  have := connectedSpace_closedCell_two_prod_Icc
  exact subset_piece_of_mem (isConnected_range (D.liftHandle c X h).smooth.continuous).isPreconnected
    ⟨p, rfl⟩ hp

theorem ccE_of_mem {e : Fin D.edgeCircleCount} {q : (D.liftEdgeCircle c X e).piece.Piece}
    (hq : (D.liftEdgeCircle c X e).piece.map q ∈ DQ.piece i) : D.ccE c X DQ i e :=
  subset_piece_of_mem (D.liftEdgeCircle c X e).piece.isConnected_range.isPreconnected ⟨q, rfl⟩ hq

theorem torusTarget_subset_compl (d : Fin D.torusSeamCount) :
    (D.torusSeam d).collar.target ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.sphere_torus_seam_disjoint c d).symm

theorem sphereTarget_subset_compl {c' : Fin D.sphereSeamCount} (hc : c' ≠ c) :
    (D.sphereSeam c').collar.target ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_disjoint hc)

theorem ccT_of_mem {d : Fin D.torusSeamCount} {x : W.Carrier} (hx : x ∈ (D.torusSeam d).collar.target)
    (h : X.transport x ∈ DQ.piece i) : D.ccT c X DQ i d :=
  subset_piece_of_mem (X.isPreconnected_transport_image (D.torusSeam d).isPreconnected_target
    (D.torusTarget_subset_compl d)) ⟨x, hx, rfl⟩ h

theorem ccS_of_mem {c' : Fin D.sphereSeamCount} (hc : c' ≠ c) {x : W.Carrier}
    (hx : x ∈ (D.sphereSeam c').collar.target) (h : X.transport x ∈ DQ.piece i) :
    D.ccS c X DQ i c' :=
  ⟨hc, subset_piece_of_mem (X.isPreconnected_transport_image (D.sphereSeam c').isPreconnected_target
    (D.sphereTarget_subset_compl hc)) ⟨x, hx, rfl⟩ h⟩

theorem ccS_ne {c' : Fin D.sphereSeamCount} (h : D.ccS c X DQ i c') : c' ≠ c :=
  h.1

/-- The transport of a vertex image off the seam sphere lies in the piece of the vertex. -/
theorem transport_image_vertex_subset {k : Fin D.vertexCount} (hk : D.ccV c X DQ i k) :
    X.transport '' ((D.vertex k).image \ (D.sphereSeam c).zeroSphere) ⊆ DQ.piece i :=
  (D.transport_image_subset_range_liftVertex c X k).trans hk

/-- A face of the component lies (transported) in the piece. -/
theorem transport_face_subset {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) :
    X.transport '' D.face f ⊆ DQ.piece i := by
  refine (image_mono ?_).trans (transport_image_vertex_subset hf.2)
  exact subset_sdiff.mpr ⟨(D.face_subset_boundaryImage f).trans (Vertex.boundaryImage_subset_image' _),
    D.face_disjoint_zeroSphere c hf.1⟩

/-- A face lying in a vertex of the component, not a side of the cut seam, is a face of the
component. -/
theorem ccF_of_ccV {f : Fin D.faceCount} (hf : ∀ b, D.faceKind f ≠ .sphereSeam c b)
    {x : W.Carrier} (hx : x ∈ D.face f) (h : X.transport x ∈ DQ.piece i) : D.ccF c X DQ i f :=
  ⟨hf, ccV_of_transport_mem ((Vertex.boundaryImage_subset_image' _) (D.face_subset_boundaryImage f hx))
    (fun hxS => Set.disjoint_left.mp (D.face_disjoint_zeroSphere c hf) hx hxS) h⟩

/-! ### Face kinds of a face of the component -/

theorem portPiece_eq_of_face {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) {a : Fin n}
    (hk : D.faceKind f = .external a) :
    PortRestriction.portPiece X.capping.retained DQ (Fin.cast X.hn.symm a) = i := by
  have hface := (D.face_external f a hk).1
  have hsub := transport_face_subset hf
  rw [hface, X.transport_image_range_torusMap] at hsub
  let t : Torus := (1, 1)
  exact PortRestriction.portPiece_eq_iff.mpr (PortRestriction.target_subset_piece_of_mem _ DQ _
    (PortRestriction.torusMap_mem_target _ _ t) (hsub ⟨t, rfl⟩))

theorem ccT_of_face {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) {d : Fin D.torusSeamCount}
    {b : Bool} (hk : D.faceKind f = .torusSeam d b) : D.ccT c X DQ i d := by
  have hface := (D.face_torusSeam f d b hk).1
  let t : Torus := (1, 1)
  have hx : (D.torusSeam d).collar (t, 0) ∈ D.face f := by rw [hface]; exact ⟨t, rfl⟩
  refine ccT_of_mem ((D.torusSeam d).collar.map_source ?_) (transport_face_subset hf ⟨_, hx, rfl⟩)
  rw [(D.torusSeam d).source_eq]
  exact ⟨by norm_num, by norm_num⟩

theorem ccS_of_face {f : Fin D.faceCount} (hf : D.ccF c X DQ i f) {c' : Fin D.sphereSeamCount}
    {b : Bool} (hk : D.faceKind f = .sphereSeam c' b) : D.ccS c X DQ i c' := by
  have hface := (D.face_sphereSeam f c' b hk).1
  have hc : c' ≠ c := by
    rintro rfl
    exact hf.1 b hk
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have hx : (D.sphereSeam c').collar (z₀, 0) ∈ D.face f := by rw [hface]; exact ⟨z₀, rfl⟩
  exact ccS_of_mem hc ((D.sphereSeam c').collar.map_source ((D.sphereSeam c').zero_mem_source z₀))
    (transport_face_subset hf ⟨_, hx, rfl⟩)

variable (D c X DQ i)

/-! ## The translated face kinds -/

open Classical in
/-- **The face kinds translated into the component `i`** (ports, torus seams and the other sphere
seams of the component renumbered; anything outside the component becomes `partitioned`, which never
happens for a face of the component). -/
def ccKind : FaceKind n D.torusSeamCount D.sphereSeamCount →
    FaceKind (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))
      (Nat.card {d // D.ccT c X DQ i d}) (Nat.card {c' // D.ccS c X DQ i c'})
  | .external a =>
    if h : PortRestriction.portPiece X.capping.retained DQ (Fin.cast X.hn.symm a) = i then
      .external ((PortRestriction.componentPortEquiv X.capping.retained DQ i).symm ⟨_, h⟩)
    else .partitioned
  | .torusSeam d b => if h : D.ccT c X DQ i d then .torusSeam ((ccEquiv _).symm ⟨d, h⟩) b
    else .partitioned
  | .sphereSeam c' b => if h : D.ccS c X DQ i c' then .sphereSeam ((ccEquiv _).symm ⟨c', h⟩) b
    else .partitioned
  | .partitioned => .partitioned

variable {D c X DQ i}

theorem ccKind_external {a : Fin n}
    (h : PortRestriction.portPiece X.capping.retained DQ (Fin.cast X.hn.symm a) = i) :
    D.ccKind c X DQ i (.external a) =
      .external ((PortRestriction.componentPortEquiv X.capping.retained DQ i).symm ⟨_, h⟩) := by
  simp [ccKind, h]

theorem ccKind_torusSeam {d : Fin D.torusSeamCount} (h : D.ccT c X DQ i d) (b : Bool) :
    D.ccKind c X DQ i (.torusSeam d b) = .torusSeam ((ccEquiv _).symm ⟨d, h⟩) b := by
  simp [ccKind, h]

theorem ccKind_sphereSeam {c' : Fin D.sphereSeamCount} (h : D.ccS c X DQ i c') (b : Bool) :
    D.ccKind c X DQ i (.sphereSeam c' b) = .sphereSeam ((ccEquiv _).symm ⟨c', h⟩) b := by
  simp [ccKind, h]

theorem ccKind_partitioned : D.ccKind c X DQ i .partitioned = .partitioned :=
  rfl

theorem eq_of_ccKind_eq_external {κ : FaceKind n D.torusSeamCount D.sphereSeamCount}
    {a : Fin (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))}
    (h : D.ccKind c X DQ i κ = .external a) :
    κ = .external (Fin.cast X.hn (PortRestriction.componentPortEquiv X.capping.retained DQ i a).1) := by
  cases κ with
  | external a₀ =>
    simp only [ccKind] at h
    split_ifs at h with h₀
    injection h with h
    rw [← h, Equiv.apply_symm_apply]
    simp
  | torusSeam d b =>
    simp only [ccKind] at h
    split_ifs at h
  | sphereSeam c' b =>
    simp only [ccKind] at h
    split_ifs at h
  | partitioned => cases h

theorem eq_of_ccKind_eq_torusSeam {κ : FaceKind n D.torusSeamCount D.sphereSeamCount}
    {d : Fin (Nat.card {d // D.ccT c X DQ i d})} {b : Bool}
    (h : D.ccKind c X DQ i κ = .torusSeam d b) : κ = .torusSeam (ccEquiv _ d).1 b := by
  cases κ with
  | external a₀ =>
    simp only [ccKind] at h
    split_ifs at h
  | torusSeam d₀ b₀ =>
    simp only [ccKind] at h
    split_ifs at h with h₀
    injection h with h hb
    rw [← h, ← hb, Equiv.apply_symm_apply]
  | sphereSeam c' b₀ =>
    simp only [ccKind] at h
    split_ifs at h
  | partitioned => cases h

theorem eq_of_ccKind_eq_sphereSeam {κ : FaceKind n D.torusSeamCount D.sphereSeamCount}
    {c'' : Fin (Nat.card {c' // D.ccS c X DQ i c'})} {b : Bool}
    (h : D.ccKind c X DQ i κ = .sphereSeam c'' b) : κ = .sphereSeam (ccEquiv _ c'').1 b := by
  cases κ with
  | external a₀ =>
    simp only [ccKind] at h
    split_ifs at h
  | torusSeam d₀ b₀ =>
    simp only [ccKind] at h
    split_ifs at h
  | sphereSeam c₀ b₀ =>
    simp only [ccKind] at h
    split_ifs at h with h₀
    injection h with h hb
    rw [← h, ← hb, Equiv.apply_symm_apply]
  | partitioned => cases h

/-- On a face of the component, `partitioned` is not created. -/
theorem eq_partitioned_of_ccKind {f : Fin D.faceCount} (hf : D.ccF c X DQ i f)
    (h : D.ccKind c X DQ i (D.faceKind f) = .partitioned) : D.faceKind f = .partitioned := by
  cases hk : D.faceKind f with
  | external a =>
    rw [hk, ccKind_external (portPiece_eq_of_face hf hk)] at h
    cases h
  | torusSeam d b =>
    rw [hk, ccKind_torusSeam (ccT_of_face hf hk)] at h
    cases h
  | sphereSeam c' b =>
    rw [hk, ccKind_sphereSeam (ccS_of_face hf hk)] at h
    cases h
  | partitioned => rfl

end DecompositionCertificate

/-! ## Traces and the faces of the component -/

theorem ccEquiv_symm_eq_iff {α : Type*} [Finite α] {P : α → Prop} {a : α} {h : P a}
    {k : Fin (Nat.card {a // P a})} : (ccEquiv P).symm ⟨a, h⟩ = k ↔ a = (ccEquiv P k).1 := by
  rw [Equiv.symm_apply_eq, Subtype.ext_iff]

/-- Unions over the renumbered subtype are unions over the predicate. -/
theorem iUnion_ccEquiv {α β : Type*} [Finite α] (P : α → Prop) (g : α → Set β) :
    (⋃ k : Fin (Nat.card {a // P a}), g (ccEquiv P k).1) = ⋃ (a : α) (_ : P a), g a := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, (ccEquiv P k).2, hk⟩
  · rintro ⟨a, ha, hx⟩
    refine ⟨(ccEquiv P).symm ⟨a, ha⟩, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hx

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E) (DQ : X.Q.Components) (i : Fin DQ.count)

/-- **The trace homeomorphism**: the trace in the component of a transported set off the seam
sphere is homeomorphic to the set. -/
def traceHomeomorph {A : Set W.Carrier} (hA : A ⊆ S.zeroSphereᶜ)
    (hi : X.transport '' A ⊆ DQ.piece i) :
    (Subtype.val ⁻¹' (X.transport '' A) : Set (GC.Topology.componentCarrier X.Q DQ i).Carrier) ≃ₜ A :=
  (preimageValHomeomorph hi).trans
    (X.transport.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hA rfl).symm

end SphereCutCapped

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- **The faces of the component**: traces of the transported faces. -/
def ccFace (f' : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    Set (GC.Topology.componentCarrier X.Q DQ i).Carrier :=
  Subtype.val ⁻¹' (X.transport '' D.face (ccEquiv _ f').1)

/-- The owner of a face of the component. -/
def ccFaceOwner (f' : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    Fin (Nat.card {k // D.ccV c X DQ i k}) :=
  (ccEquiv _).symm ⟨D.faceOwner (ccEquiv _ f').1, (ccEquiv _ f').2.2⟩

/-- The model of a face of the component (the old model through the trace homeomorphism). -/
def ccFaceModel (f' : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    (D.ccFace c X DQ i f' ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕
      (D.ccFace c X DQ i f' ≃ₜ Circle × Circle) :=
  Sum.map
    (fun e => (X.traceHomeomorph DQ i (D.face_subset_compl_zeroSphere c (ccEquiv _ f').2.1)
      (transport_face_subset (ccEquiv _ f').2)).trans e)
    (fun e => (X.traceHomeomorph DQ i (D.face_subset_compl_zeroSphere c (ccEquiv _ f').2.1)
      (transport_face_subset (ccEquiv _ f').2)).trans e)
    (D.faceModel (ccEquiv _ f').1)

/-- The kind of a face of the component. -/
def ccFaceKind (f' : Fin (Nat.card {f // D.ccF c X DQ i f})) :
    FaceKind (Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i))
      (Nat.card {d // D.ccT c X DQ i d}) (Nat.card {c' // D.ccS c X DQ i c'}) :=
  D.ccKind c X DQ i (D.faceKind (ccEquiv _ f').1)

variable {D c X DQ i}

theorem ccFaceOwner_eq_iff {f' : Fin (Nat.card {f // D.ccF c X DQ i f})}
    {k' : Fin (Nat.card {k // D.ccV c X DQ i k})} :
    D.ccFaceOwner c X DQ i f' = k' ↔ D.faceOwner (ccEquiv _ f').1 = (ccEquiv _ k').1 :=
  ccEquiv_symm_eq_iff

/-- A sphere face of the component comes from a sphere face. -/
theorem faceModel_inl_of_ccFaceModel {f' : Fin (Nat.card {f // D.ccF c X DQ i f})}
    {e' : D.ccFace c X DQ i f' ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (h : D.ccFaceModel c X DQ i f' = .inl e') :
    ∃ e : D.face (ccEquiv _ f').1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      D.faceModel (ccEquiv _ f').1 = .inl e := by
  unfold ccFaceModel at h
  rcases hm : D.faceModel (ccEquiv _ f').1 with e | e
  · exact ⟨e, rfl⟩
  · rw [hm] at h
    cases h

/-- The model boundary of a vertex off the seam sphere is the union of its faces that are not
sides of the cut seam. -/
theorem boundaryImage_sdiff_zeroSphere (k : Fin D.vertexCount) :
    (D.vertex k).boundaryImage \ (D.sphereSeam c).zeroSphere =
      ⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k ∧ ∀ b, D.faceKind f ≠ .sphereSeam c b),
        D.face f := by
  ext y
  simp only [mem_sdiff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hy, hyS⟩
    rw [← D.face_exhausted k] at hy
    obtain ⟨f, hfo, hyf⟩ := mem_iUnion₂.mp hy
    refine ⟨f, ⟨hfo, fun b hb => hyS ?_⟩, hyf⟩
    rw [(D.face_sphereSeam f c b hb).1] at hyf
    exact hyf
  · rintro ⟨f, ⟨hfo, hf⟩, hyf⟩
    refine ⟨?_, fun hyS => Set.disjoint_left.mp (D.face_disjoint_zeroSphere c hf) hyf hyS⟩
    rw [← D.face_exhausted k]
    exact mem_iUnion₂.mpr ⟨f, hfo, hyf⟩

end DecompositionCertificate

/-! ## Consumer (G3) -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components)
  (i : Fin DQ.count)

/-- **Consumer (G3).** On a capped component all of whose caps belong to `S² × I` sides, the
vertices of the component (an injective renumbering of old vertices) form a family of vertices of
the component carrier without closed zero vertex; each image is the trace of the transported old
image off the seam sphere together with the cap of a side, each model-boundary image the trace of
the transported old one off the seam sphere, and the sides of the cut seam become balls. -/
theorem exists_ccVertexFamily (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hcap : ∀ b, X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)) = i →
      D.SideSphereInterval c b) :
    ∃ (m : ℕ) (V : Fin m → Vertex (GC.Topology.componentCarrier X.Q DQ i))
      (ι : Fin m → Fin D.vertexCount), Injective ι ∧
      (∀ k', (V k').image = Subtype.val ⁻¹' (X.transport '' ((D.vertex (ι k')).image \
        (D.sphereSeam c).zeroSphere) ∪ D.ccCapPart c X (ι k'))) ∧
      (∀ k', (V k').boundaryImage = Subtype.val ⁻¹' (X.transport ''
        ((D.vertex (ι k')).boundaryImage \ (D.sphereSeam c).zeroSphere))) ∧
      (∀ k' b, ι k' = D.sphereSide c b → (V k').IsBall) ∧
      ∀ k' C, V k' ≠ .closedZero C := by
  refine ⟨_, D.ccVertex c X DQ i hcap, fun k' => (ccEquiv _ k').1,
    fun k k' h => (ccEquiv _).injective (Subtype.ext h), fun k' => ?_, fun k' => ?_,
    fun k' b hb => ?_, fun k' C => ?_⟩
  · exact D.image_ccVertexOf c X DQ i hcap _ _
  · exact D.boundaryImage_ccVertexOf c X DQ i hcap _ _
  · exact D.isBall_ccVertexOf_of_side c X DQ i hcap _ _ (isSide_iff.mpr ⟨b, hb⟩)
  · exact D.ccVertexOf_ne_closedZero c X DQ i hcap hnz _ _ C

end DecompositionCertificate

end GC.GraphManifold.Assembly
