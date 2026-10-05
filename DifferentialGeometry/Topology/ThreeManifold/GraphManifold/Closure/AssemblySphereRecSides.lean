import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpaceApplications

/-!
# FC42 sphere recursion, packet S2 (certificate level): the sides of a sphere seam and the lifts

Lane ASM-SPH (review 40 §2.4 first layer; §3.4 for the side lemma). For a certificate
`D : DecompositionCertificate W E` and a sphere seam `c`:

* `SphereSeam.openHalf j`: the open half collar of side `j` (signed height `> 0`); every open set
  meeting the collar target meets an open half collar (`exists_openHalf_of_inter_target`), and one
  meeting the seam sphere meets both (`inter_openHalf_nonempty_of_mem_zeroSphere`).
* `sphereSide_true_ne_false`: the two sides of a sphere seam are different vertices (otherwise the
  whole two-sided collar lies in one vertex image, so the seam sphere — a face, hence in the
  model-boundary image — is in the ambient interior of the image: impossible on `W.interior` by
  ASM-CYC2's boundary criterion `Vertex.boundaryImage_inter_interior_subset`). Lane ASM-CYC2 owns
  the statement `sphereSide_ne` (its G3, not built at the time of writing); this is the same fact
  under a different name.
* `sideVertex_side`: a side vertex stays on its side of the seam (density of interior points,
  `exists_mem_inter_interior_range`, and `vertex_disjoint`);
  `vertex_image_disjoint_sphereCollar`, `edgeCircle_image_disjoint_sphereCollar`: the vertices
  that are not sides, and all edge-circle pieces, avoid the whole collar.
* the lifts into the capped carrier of `X : SphereCutCapped W (D.sphereSeam c) E`, all by the one
  transport / side lift: `liftVertex` (every vertex, the side vertices on their own copy of the cut
  sphere), `liftHandle`, `liftEdgeCircle`, `liftTorusSeam`, `liftOtherSphereSeam`, `liftRimChart`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## Open half collars -/

namespace SphereSeam

variable {W : CompactCarrier.{u}} (S : SphereSeam W)

/-- The open half collar of side `j`: collar points of positive signed height. -/
def openHalf (j : Fin 2) : Set W.Carrier :=
  S.collar '' {p | p ∈ S.collar.source ∧ 0 < cutSideSign j * p.2}

theorem isOpen_openHalf (j : Fin 2) : IsOpen (S.openHalf j) :=
  S.collar.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (S.collar.open_source.inter (isOpen_lt continuous_const (continuous_const.mul continuous_snd)))
    fun _ hp => hp.1

theorem collar_mem_openHalf {j : Fin 2} {p : ClosureSphere.{u} × ℝ} (hp : p ∈ S.collar.source)
    (h : 0 < cutSideSign j * p.2) : S.collar p ∈ S.openHalf j :=
  ⟨p, ⟨hp, h⟩, rfl⟩

/-- An open set through a point of the seam sphere meets both open half collars. -/
theorem inter_openHalf_nonempty_of_mem_zeroSphere {V : Set W.Carrier} (hV : IsOpen V)
    {y : W.Carrier} (hyV : y ∈ V) (hy : y ∈ S.zeroSphere) (j : Fin 2) :
    (V ∩ S.openHalf j).Nonempty := by
  obtain ⟨z, rfl⟩ := hy
  let γ : ℝ → ClosureSphere.{u} × ℝ := fun t => (z, cutSideSign j * t)
  have hγ : Continuous γ := continuous_const.prodMk (continuous_const.mul continuous_id)
  have hγ0 : γ 0 = (z, 0) := by simp [γ]
  have hcont : ContinuousAt (fun t => S.collar (γ t)) 0 := by
    refine ContinuousAt.comp (f := γ) ?_ hγ.continuousAt
    rw [hγ0]
    exact S.collar.toOpenPartialHomeomorph.continuousAt (S.zero_mem_source z)
  have hmem : (fun t => S.collar (γ t)) ⁻¹' V ∈ 𝓝 (0 : ℝ) := by
    apply hcont.preimage_mem_nhds
    rw [hγ0]
    exact hV.mem_nhds hyV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  set t : ℝ := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_half_pos
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) one_half_lt_one
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have htV : S.collar (γ t) ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact htε)
  have hsrc : γ t ∈ S.collar.source := by
    refine S.mem_source_iff.mpr ?_
    have habs : |cutSideSign j * t| < 1 := by rw [abs_cutSideSign_mul, abs_of_pos ht0]; exact ht1
    exact abs_lt.mp habs
  refine ⟨S.collar (γ t), htV, S.collar_mem_openHalf hsrc ?_⟩
  change 0 < cutSideSign j * (cutSideSign j * t)
  rw [← mul_assoc, cutSideSign_mul_self, one_mul]
  exact ht0

/-- An open set meeting the collar target meets an open half collar. -/
theorem exists_openHalf_of_inter_target {V : Set W.Carrier} (hV : IsOpen V)
    (hne : (V ∩ S.collar.target).Nonempty) : ∃ j, (V ∩ S.openHalf j).Nonempty := by
  obtain ⟨y, hyV, hyT⟩ := hne
  have hp : S.collar.symm y ∈ S.collar.source := S.collar.map_target hyT
  have hy : S.collar (S.collar.symm y) = y := S.collar_collar_symm hyT
  rcases lt_trichotomy (S.collar.symm y).2 0 with hneg | hzero | hpos
  · refine ⟨1, y, hyV, ?_⟩
    rw [← hy]
    refine S.collar_mem_openHalf hp ?_
    simp only [cutSideSign]
    norm_num
    exact hneg
  · refine ⟨0, S.inter_openHalf_nonempty_of_mem_zeroSphere hV hyV ?_ 0⟩
    rw [← hy, S.collar_mem_zeroSphere_iff hp]
    exact hzero
  · refine ⟨0, y, hyV, ?_⟩
    rw [← hy]
    refine S.collar_mem_openHalf hp ?_
    simp only [cutSideSign]
    norm_num
    exact hpos

end SphereSeam

/-- The copy of the cut sphere on side `b` of a certificate seam: `b = false` (collar `s ≥ 0`) is
copy `0`, `b = true` (collar `s ≤ 0`) is copy `1`. -/
def sideCopy (b : Bool) : Fin 2 :=
  if b then 1 else 0

theorem cutSideSign_sideCopy (b : Bool) : cutSideSign (sideCopy b) = if b then -1 else 1 := by
  cases b <;> rfl

theorem cutSideSign_sideCopy_not (b : Bool) :
    cutSideSign (sideCopy (!b)) = -cutSideSign (sideCopy b) := by
  cases b <;> simp [cutSideSign_sideCopy]

theorem exists_sideCopy_eq (j : Fin 2) : ∃ b, sideCopy b = j := by
  fin_cases j
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-! ## The sides of a sphere seam of a certificate -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The open half collar of side `b` lies in the side vertex `b`. -/
theorem openHalf_subset_image (c : Fin D.sphereSeamCount) (b : Bool) :
    (D.sphereSeam c).openHalf (sideCopy b) ⊆ (D.vertex (D.sphereSide c b)).image := by
  rintro _ ⟨p, ⟨hp, hpos⟩, rfl⟩
  have hs := (D.sphereSeam c).mem_source_iff.mp hp
  rw [cutSideSign_sideCopy] at hpos
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hpos
    exact D.sphereSide_pos c p.1 p.2 hpos.le hs.2
  · simp only [↓reduceIte, neg_mul, one_mul, neg_pos] at hpos
    exact D.sphereSide_neg c p.1 p.2 hpos.le hs.1

theorem openHalf_subset_interior_image (c : Fin D.sphereSeamCount) (b : Bool) :
    (D.sphereSeam c).openHalf (sideCopy b) ⊆ interior (D.vertex (D.sphereSide c b)).image :=
  interior_maximal (D.openHalf_subset_image c b) ((D.sphereSeam c).isOpen_openHalf _)

/-- **The two sides of a sphere seam are different vertices.** (Same fact as ASM-CYC2's frozen
`sphereSide_ne`.) -/
theorem sphereSide_true_ne_false (c : Fin D.sphereSeamCount) :
    D.sphereSide c true ≠ D.sphereSide c false := by
  intro hk
  set k := D.sphereSide c true with hkdef
  have hT : (D.sphereSeam c).collar.target ⊆ (D.vertex k).image := by
    intro x hx
    have hp := (D.sphereSeam c).collar.map_target hx
    have hs := (D.sphereSeam c).mem_source_iff.mp hp
    rw [← (D.sphereSeam c).collar_collar_symm hx]
    rcases le_or_gt ((D.sphereSeam c).collar.symm x).2 0 with hle | hgt
    · exact D.sphereSide_neg c _ _ hle hs.1
    · rw [hk]
      exact D.sphereSide_pos c _ _ hgt.le hs.2
  have hTi : (D.sphereSeam c).collar.target ⊆ interior (D.vertex k).image :=
    interior_maximal hT (D.sphereSeam c).collar.open_target
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face c true
  have hface := (D.face_sphereSeam f c true hfk).1
  have hx : (D.sphereSeam c).collar (z₀, 0) ∈ D.face f := by
    rw [hface]
    exact ⟨z₀, rfl⟩
  have hxb : (D.sphereSeam c).collar (z₀, 0) ∈ (D.vertex k).boundaryImage := by
    rw [← D.face_exhausted k]
    exact mem_iUnion₂.mpr ⟨f, hfo, hx⟩
  have hxT : (D.sphereSeam c).collar (z₀, 0) ∈ (D.sphereSeam c).collar.target :=
    (D.sphereSeam c).collar.map_source ((D.sphereSeam c).zero_mem_source z₀)
  exact Vertex.boundaryImage_inter_interior_subset _ ⟨hxb, hTi hxT⟩
    ((D.sphereSeam c).target_interior hxT)

theorem sphereSide_ne_not (c : Fin D.sphereSeamCount) (b : Bool) :
    D.sphereSide c b ≠ D.sphereSide c (!b) := by
  cases b
  · exact (D.sphereSide_true_ne_false c).symm
  · exact D.sphereSide_true_ne_false c

/-- A side vertex does not meet the opposite open half collar. -/
theorem disjoint_image_openHalf_not (c : Fin D.sphereSeamCount) (b : Bool) :
    Disjoint (D.vertex (D.sphereSide c b)).image ((D.sphereSeam c).openHalf (sideCopy (!b))) := by
  rw [Set.disjoint_left]
  intro x hx hxo
  rw [Vertex.image_eq_range_piece] at hx
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨y, hyo, hyi⟩ := exists_mem_inter_interior_range finrank_euclideanSpace_fin
    (D.vertex (D.sphereSide c b)).piece.smooth (D.vertex (D.sphereSide c b)).piece.mfderiv_bijective
    ((D.sphereSeam c).isOpen_openHalf _) hxo
  rw [← Vertex.image_eq_range_piece] at hyi
  exact Set.disjoint_left.mp (D.vertex_disjoint (D.sphereSide_ne_not c b)) hyi
    (D.openHalf_subset_interior_image c (!b) hyo)

/-- **A side vertex stays on its side of the seam.** -/
theorem sideVertex_side (c : Fin D.sphereSeamCount) (b : Bool)
    {q : (D.vertex (D.sphereSide c b)).piece.Piece} {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ (D.sphereSeam c).collar.source)
    (h : (D.vertex (D.sphereSide c b)).piece.map q = (D.sphereSeam c).collar p) :
    0 ≤ cutSideSign (sideCopy b) * p.2 := by
  by_contra hneg
  have hpos : 0 < cutSideSign (sideCopy (!b)) * p.2 := by
    rw [cutSideSign_sideCopy_not, neg_mul]
    linarith
  have hx : (D.sphereSeam c).collar p ∈ (D.vertex (D.sphereSide c b)).image := by
    rw [← h, Vertex.image_eq_range_piece]
    exact ⟨q, rfl⟩
  exact Set.disjoint_left.mp (D.disjoint_image_openHalf_not c b) hx
    ((D.sphereSeam c).collar_mem_openHalf hp hpos)

/-- A full-rank map whose interior image avoids the interiors of both side vertices avoids the
whole seam collar. -/
theorem disjoint_sphereCollar_of_interior {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] {f : M → W.Carrier}
    (hf : ContMDiff (𝓡∂ 3) W.model ∞ f) (hbij : ∀ q, Bijective (mfderiv (𝓡∂ 3) W.model f q))
    (c : Fin D.sphereSeamCount)
    (hdis : ∀ b, Disjoint (interior (range f)) (interior (D.vertex (D.sphereSide c b)).image)) :
    Disjoint (range f) (D.sphereSeam c).collar.target := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ hqT
  obtain ⟨y, hyT, hyi⟩ := exists_mem_inter_interior_range finrank_euclideanSpace_fin hf hbij
    (D.sphereSeam c).collar.open_target hqT
  obtain ⟨j, w, hwi, hwo⟩ := (D.sphereSeam c).exists_openHalf_of_inter_target isOpen_interior
    ⟨y, hyi, hyT⟩
  obtain ⟨b, rfl⟩ := exists_sideCopy_eq j
  exact Set.disjoint_left.mp (hdis b) hwi (D.openHalf_subset_interior_image c b hwo)

/-- **A vertex that is not a side of the seam avoids the whole seam collar.** -/
theorem vertex_image_disjoint_sphereCollar {c : Fin D.sphereSeamCount} {k : Fin D.vertexCount}
    (h1 : k ≠ D.sphereSide c true) (h2 : k ≠ D.sphereSide c false) :
    Disjoint (D.vertex k).image (D.sphereSeam c).collar.target := by
  rw [Vertex.image_eq_range_piece]
  refine D.disjoint_sphereCollar_of_interior (D.vertex k).piece.smooth
    (D.vertex k).piece.mfderiv_bijective c fun b => ?_
  rw [← Vertex.image_eq_range_piece]
  refine D.vertex_disjoint fun h => ?_
  cases b
  · exact h2 h
  · exact h1 h

/-- **An edge-circle piece avoids every sphere seam collar.** -/
theorem edgeCircle_image_disjoint_sphereCollar (c : Fin D.sphereSeamCount)
    (e : Fin D.edgeCircleCount) :
    Disjoint (range (D.edgeCircle e).piece.map) (D.sphereSeam c).collar.target :=
  D.disjoint_sphereCollar_of_interior (D.edgeCircle e).piece.smooth
    (D.edgeCircle e).piece.mfderiv_bijective c fun _ => D.edgeCircle_vertex_disjoint e _

theorem subset_compl_zeroSphere_of_disjoint {c : Fin D.sphereSeamCount} {A : Set W.Carrier}
    (h : Disjoint A (D.sphereSeam c).collar.target) : A ⊆ (D.sphereSeam c).zeroSphereᶜ :=
  fun _ hx hz => Set.disjoint_left.mp h hx ((D.sphereSeam c).zeroSphere_subset_target hz)

/-! ## The lifts of the certificate data into the capped carrier -/

/-- The side of vertex `k` for the seam `c` (`true` exactly for the side `true` vertex). -/
def vertexSide (c : Fin D.sphereSeamCount) (k : Fin D.vertexCount) : Bool :=
  decide (k = D.sphereSide c true)

theorem vertexSide_sphereSide (c : Fin D.sphereSeamCount) (b : Bool) :
    D.vertexSide c (D.sphereSide c b) = b := by
  cases b
  · exact decide_eq_false (D.sphereSide_true_ne_false c).symm
  · exact decide_eq_true rfl

/-- Every vertex stays on its side (vacuously for the vertices that are not sides). -/
theorem vertex_side_condition (c : Fin D.sphereSeamCount) (k : Fin D.vertexCount)
    {q : (D.vertex k).piece.Piece} {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ (D.sphereSeam c).collar.source)
    (h : (D.vertex k).piece.map q = (D.sphereSeam c).collar p) :
    0 ≤ cutSideSign (sideCopy (D.vertexSide c k)) * p.2 := by
  by_cases h1 : k = D.sphereSide c true
  · subst h1
    rw [D.vertexSide_sphereSide]
    exact D.sideVertex_side c true hp h
  · by_cases h2 : k = D.sphereSide c false
    · subst h2
      rw [D.vertexSide_sphereSide]
      exact D.sideVertex_side c false hp h
    · exfalso
      have hx : (D.sphereSeam c).collar p ∈ (D.vertex k).image := by
        rw [← h, Vertex.image_eq_range_piece]
        exact ⟨q, rfl⟩
      exact Set.disjoint_left.mp (D.vertex_image_disjoint_sphereCollar h1 h2) hx
        ((D.sphereSeam c).collar.map_source hp)

variable (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E)

/-- **S2. The lift of vertex `k`** into the capped carrier (side vertices on their own copy of the
cut sphere). -/
def liftVertex (k : Fin D.vertexCount) : PieceEmbedding X.Q :=
  X.liftPiece (D.vertex k).piece (sideCopy (D.vertexSide c k))
    fun _ _ hp h => D.vertex_side_condition c k hp h

theorem liftVertex_map (k : Fin D.vertexCount) (q : (D.vertex k).piece.Piece) :
    (D.liftVertex c X k).map q =
      X.capping.core (X.sideLift (sideCopy (D.vertexSide c k)) ((D.vertex k).piece.map q)) :=
  rfl

theorem liftVertex_map_of_side (b : Bool) (q : (D.vertex (D.sphereSide c b)).piece.Piece) :
    (D.liftVertex c X (D.sphereSide c b)).map q =
      X.capping.core (X.sideLift (sideCopy b) ((D.vertex (D.sphereSide c b)).piece.map q)) := by
  rw [liftVertex_map, D.vertexSide_sphereSide]

theorem liftVertex_map_of_notMem (k : Fin D.vertexCount) {q : (D.vertex k).piece.Piece}
    (hq : (D.vertex k).piece.map q ∉ (D.sphereSeam c).zeroSphere) :
    (D.liftVertex c X k).map q = X.transport ((D.vertex k).piece.map q) :=
  X.liftPiece_map_of_notMem _ _ _ hq

theorem fold_coreInverse_liftVertex (k : Fin D.vertexCount) (q : (D.vertex k).piece.Piece) :
    X.fold (X.coreInverse ((D.liftVertex c X k).map q)) = (D.vertex k).piece.map q :=
  X.fold_coreInverse_liftPiece _ _ _ q

/-- A vertex that is not a side of the seam is lifted by the transport alone. -/
theorem range_liftVertex_of_ne {k : Fin D.vertexCount} (h1 : k ≠ D.sphereSide c true)
    (h2 : k ≠ D.sphereSide c false) :
    range (D.liftVertex c X k).map = X.transport '' (D.vertex k).image := by
  have hA := D.subset_compl_zeroSphere_of_disjoint (D.vertex_image_disjoint_sphereCollar h1 h2)
  rw [Vertex.image_eq_range_piece] at hA ⊢
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨q, rfl⟩, (D.liftVertex_map_of_notMem c X k (hA ⟨q, rfl⟩)).symm⟩
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, D.liftVertex_map_of_notMem c X k (hA ⟨q, rfl⟩)⟩

/-- The lifted side vertex `b` on the seam sphere: copy `sideCopy b` of the cut sphere. -/
theorem liftVertex_map_of_mem (b : Bool) {q : (D.vertex (D.sphereSide c b)).piece.Piece}
    {z : ClosureSphere.{u}}
    (hq : (D.vertex (D.sphereSide c b)).piece.map q = (D.sphereSeam c).collar (z, 0)) :
    (D.liftVertex c X (D.sphereSide c b)).map q = X.capping.core (X.cutSphere (sideCopy b) z) := by
  rw [D.liftVertex_map_of_side c X b, hq, X.sideLift_of_mem]

/-- **S2. The lifted handle.** -/
def liftHandle (h : Fin D.handleCount) : EdgeHandle X.Q :=
  X.liftEdgeHandle (D.handle h)
    (D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_handle_disjoint c h).symm)

/-- **S2. The lifted edge-circle piece.** -/
def liftEdgeCircle (e : Fin D.edgeCircleCount) : EdgeCirclePiece X.Q :=
  X.liftEdgeCirclePiece (D.edgeCircle e)
    (D.subset_compl_zeroSphere_of_disjoint (D.edgeCircle_image_disjoint_sphereCollar c e))

/-- **S2. The lifted torus seam.** -/
def liftTorusSeam (d : Fin D.torusSeamCount) : TorusSeam X.Q :=
  X.liftTorusSeam (D.torusSeam d)
    (D.subset_compl_zeroSphere_of_disjoint (D.sphere_torus_seam_disjoint c d).symm)

/-- **S2. Another lifted sphere seam.** -/
def liftOtherSphereSeam {c' : Fin D.sphereSeamCount} (hc : c' ≠ c) : SphereSeam X.Q :=
  X.liftSphereSeam (D.sphereSeam c')
    (D.subset_compl_zeroSphere_of_disjoint (D.sphereSeam_disjoint hc))

/-- **S2. The lifted rim chart.** -/
def liftRimChart (h : Fin D.handleCount) (b : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) X.Q.model (Circle × (ℝ × ℝ)) X.Q.Carrier ∞ :=
  X.liftPartialDiffeomorph (D.rimChart h b)
    (D.subset_compl_zeroSphere_of_disjoint (D.rim_sphereSeam_disjoint h b c))

theorem liftRimChart_source (h : Fin D.handleCount) (b : Bool) :
    (D.liftRimChart c X h b).source = (D.rimChart h b).source :=
  X.liftPartialDiffeomorph_source _ _

theorem liftRimChart_apply (h : Fin D.handleCount) (b : Bool) (p : Circle × (ℝ × ℝ)) :
    D.liftRimChart c X h b p = X.transport (D.rimChart h b p) :=
  rfl

end DecompositionCertificate

end GC.GraphManifold.Assembly
