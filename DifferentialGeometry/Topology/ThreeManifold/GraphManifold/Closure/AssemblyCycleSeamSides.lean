import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpaceApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionBallFace

/-!
# FC42 packet G3: seam sides, faces are boundary components, bad vertices

Review 40 §3.4 (B7 (b)) and §1.4; statements frozen by lane ASM-CYC2
(`build-logs/scratch/ASM-CYC2/H1Targets.lean`, section G3), proved here verbatim (packet moved to
lane ASM-CYC3 by the lead).

* **Seam sides.** `sphereSide_ne`: the two sides of a sphere seam are different vertices;
  `torusSide_ne`: if the `true` side of a torus seam is the vertex `k`, the `false` side is not `k`
  (`none / none` stays allowed). Proof: otherwise the whole open collar target lies in the vertex
  image, so the seam points are ambient interior points of the image; they are also in the face of
  that seam side, i.e. images of model-boundary points, and lie in `W.interior` (the collar targets
  do) — impossible by the boundary criterion of packet G1
  (`Vertex.boundaryImage_inter_interior_subset`, from `not_mem_interior_range_of_isBoundaryPoint`).
* **Faces are actual boundary components.** Two different faces of one vertex are disjoint
  (`face_disjoint_of_faceOwner_eq`: V4 `face_disjoint`, the seam-side exception being excluded by the
  side theorems). Faces are compact, connected (sphere or torus) and finitely many, so each is open
  and closed in the model-boundary image of its owner: `face_eq_connectedComponentIn`, and
  `face_eq_boundaryImage_of_isPreconnected`.
* **Bad vertices.** `badVertexCount` counts the vertices that are not balls (`Vertex.IsBall`) and own
  a partitioned sphere face; `partitionedSphereFace_ball_of_badVertexCount_eq_zero` is the terminal
  B5 (the `hball` input of the cycle partition `nonempty_cyclePartition`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-! ## Seam sides -/

/-- A point of a face which is an ambient interior point of the owner's image lies off
`W.interior`. -/
theorem not_mem_interior_image_of_mem_face (f : Fin D.faceCount) {x : W.Carrier}
    (hx : x ∈ D.face f) (hxW : x ∈ W.interior) :
    x ∉ interior (D.vertex (D.faceOwner f)).image := fun hxi =>
  (D.vertex (D.faceOwner f)).boundaryImage_inter_interior_subset
    ⟨D.face_subset_boundaryImage f hx, hxi⟩ hxW

/-- **G3.** The two sides of a sphere seam are different vertices. -/
theorem sphereSide_ne (c : Fin D.sphereSeamCount) : D.sphereSide c true ≠ D.sphereSide c false := by
  intro heq
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face c true
  obtain ⟨x, hx⟩ := D.face_nonempty f
  have hface := (D.face_sphereSeam f c true hfk).1
  have hx' := hx
  rw [hface] at hx'
  obtain ⟨z, rfl⟩ := hx'
  have hsrc : ∀ p, p ∈ (D.sphereSeam c).collar.source ↔ -1 < p.2 ∧ p.2 < 1 := fun p => by
    rw [(D.sphereSeam c).source_eq]
    simp [sphereSignedCollarSource]
  have hz : (z, (0 : ℝ)) ∈ (D.sphereSeam c).collar.source := (hsrc _).mpr ⟨by norm_num, by norm_num⟩
  -- the whole collar target lies in the image of the common side vertex
  have hT : (D.sphereSeam c).collar.target ⊆ (D.vertex (D.sphereSide c true)).image := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ : ∃ p, p ∈ (D.sphereSeam c).collar.source ∧ (D.sphereSeam c).collar p = y :=
      ⟨_, (D.sphereSeam c).collar.map_target hy, (D.sphereSeam c).collar.right_inv hy⟩
    obtain ⟨h1, h2⟩ := (hsrc p).mp hp
    by_cases hs : p.2 ≤ 0
    · exact D.sphereSide_neg c p.1 p.2 hs h1
    · rw [heq]
      exact D.sphereSide_pos c p.1 p.2 (not_le.mp hs).le h2
  have hint : (D.sphereSeam c).collar (z, 0) ∈ interior (D.vertex (D.faceOwner f)).image := by
    rw [hfo]
    exact interior_maximal hT (D.sphereSeam c).collar.open_target
      ((D.sphereSeam c).collar.map_source hz)
  exact D.not_mem_interior_image_of_mem_face f hx
    ((D.sphereSeam c).target_interior ((D.sphereSeam c).collar.map_source hz)) hint

/-- **G3.** A torus seam does not have the same vertex on both sides (`none / none` is allowed by
the certificate fields and is NOT excluded here). -/
theorem torusSide_ne (c : Fin D.torusSeamCount) (k : Fin D.vertexCount)
    (hk : D.torusSide c true = some k) : D.torusSide c false ≠ some k := by
  intro hk'
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c true k hk
  have hface := (D.face_torusSeam f c true hfk).1
  have hsrc : ∀ p, p ∈ (D.torusSeam c).collar.source ↔ -1 < p.2 ∧ p.2 < 1 := fun p => by
    rw [(D.torusSeam c).source_eq]
    rfl
  let t : Torus := (1, 1)
  have hz : (t, (0 : ℝ)) ∈ (D.torusSeam c).collar.source := (hsrc _).mpr ⟨by norm_num, by norm_num⟩
  have hx : (D.torusSeam c).collar (t, 0) ∈ D.face f := by
    rw [hface]
    exact ⟨t, rfl⟩
  have hT : (D.torusSeam c).collar.target ⊆ (D.vertex k).image := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ : ∃ p, p ∈ (D.torusSeam c).collar.source ∧ (D.torusSeam c).collar p = y :=
      ⟨_, (D.torusSeam c).collar.map_target hy, (D.torusSeam c).collar.right_inv hy⟩
    obtain ⟨h1, h2⟩ := (hsrc p).mp hp
    by_cases hs : p.2 ≤ 0
    · have := D.torusSide_neg c p.1 p.2 h1 hs
      rwa [hk] at this
    · have := D.torusSide_pos c p.1 p.2 (not_le.mp hs).le h2
      rwa [hk'] at this
  have hint : (D.torusSeam c).collar (t, 0) ∈ interior (D.vertex (D.faceOwner f)).image := by
    rw [hfo]
    exact interior_maximal hT (D.torusSeam c).collar.open_target
      ((D.torusSeam c).collar.map_source hz)
  exact D.not_mem_interior_image_of_mem_face f hx
    ((D.torusSeam c).target_interior ((D.torusSeam c).collar.map_source hz)) hint

/-! ## Faces are actual boundary components -/

/-- **G3.** Two different faces of the same vertex are disjoint. -/
theorem face_disjoint_of_faceOwner_eq {f f' : Fin D.faceCount} (hne : f ≠ f')
    (hown : D.faceOwner f = D.faceOwner f') : Disjoint (D.face f) (D.face f') := by
  refine D.face_disjoint f f' hne ?_ ?_
  · rintro c b ⟨h1, h2⟩
    have e1 := (D.face_sphereSeam f c b h1).2
    have e2 := (D.face_sphereSeam f' c (!b) h2).2
    have hside : D.sphereSide c b = D.sphereSide c (!b) := by rw [e1, e2, hown]
    cases b
    · exact D.sphereSide_ne c hside.symm
    · exact D.sphereSide_ne c hside
  · rintro c b ⟨h1, h2⟩
    have e1 := (D.face_torusSeam f c b h1).2
    have e2 := (D.face_torusSeam f' c (!b) h2).2
    rw [← hown] at e2
    cases b
    · exact D.torusSide_ne c _ e2 e1
    · exact D.torusSide_ne c _ e1 e2

/-- A face is connected (a two-sphere or a torus). -/
theorem isConnected_face (f : Fin D.faceCount) : IsConnected (D.face f) := by
  rw [isConnected_iff_connectedSpace]
  rcases D.faceModel f with φ | ψ
  · exact φ.symm.surjective.connectedSpace φ.symm.continuous
  · exact ψ.symm.surjective.connectedSpace ψ.symm.continuous

/-- The other faces of the owner of `f`. -/
theorem boundaryImage_subset_face_union (f : Fin D.faceCount) :
    (D.vertex (D.faceOwner f)).boundaryImage ⊆
      D.face f ∪ ⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = D.faceOwner f) (_ : f' ≠ f),
        D.face f' := by
  intro x hx
  rw [← D.face_exhausted] at hx
  obtain ⟨f', hx⟩ := mem_iUnion.mp hx
  obtain ⟨hf', hx⟩ := mem_iUnion.mp hx
  by_cases h : f' = f
  · exact Or.inl (h ▸ hx)
  · exact Or.inr (mem_iUnion₂.mpr ⟨f', hf', mem_iUnion.mpr ⟨h, hx⟩⟩)

theorem isClosed_otherFaces (f : Fin D.faceCount) :
    IsClosed (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = D.faceOwner f) (_ : f' ≠ f),
      D.face f') :=
  isClosed_iUnion_of_finite fun f' => isClosed_iUnion_of_finite fun _ =>
    isClosed_iUnion_of_finite fun _ => D.isClosed_face f'

theorem disjoint_otherFaces (f : Fin D.faceCount) :
    Disjoint (D.face f)
      (⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = D.faceOwner f) (_ : f' ≠ f), D.face f') :=
  disjoint_iUnion_right.mpr fun _ => disjoint_iUnion_right.mpr fun hown =>
    disjoint_iUnion_right.mpr fun hne => D.face_disjoint_of_faceOwner_eq (Ne.symm hne) hown.symm

/-- A preconnected subset of the owner's boundary image meeting a face lies in it. -/
theorem subset_face_of_isPreconnected (f : Fin D.faceCount) {s : Set W.Carrier}
    (hs : IsPreconnected s) (hsB : s ⊆ (D.vertex (D.faceOwner f)).boundaryImage)
    {z : W.Carrier} (hzs : z ∈ s) (hz : z ∈ D.face f) : s ⊆ D.face f := by
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hs
  have hempty : s ∩ (D.face f ∩
      ⋃ (f' : Fin D.faceCount) (_ : D.faceOwner f' = D.faceOwner f) (_ : f' ≠ f), D.face f') = ∅ := by
    rw [(D.disjoint_otherFaces f).inter_eq, inter_empty]
  rcases hs _ _ (D.isClosed_face f) (D.isClosed_otherFaces f)
    (hsB.trans (D.boundaryImage_subset_face_union f)) hempty with h | h
  · exact h
  · exact (Set.disjoint_left.mp (D.disjoint_otherFaces f) hz (h hzs)).elim

/-- **G3, faces are actual boundary components:** each face is the connected component, inside
the model-boundary image of its owner, of each of its points. -/
theorem face_eq_connectedComponentIn (f : Fin D.faceCount) {z : W.Carrier} (hz : z ∈ D.face f) :
    D.face f = connectedComponentIn (D.vertex (D.faceOwner f)).boundaryImage z := by
  apply Subset.antisymm
  · exact (D.isConnected_face f).isPreconnected.subset_connectedComponentIn hz
      (D.face_subset_boundaryImage f)
  · exact D.subset_face_of_isPreconnected f (isPreconnected_connectedComponentIn)
      (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn (D.face_subset_boundaryImage f hz)) hz

/-- **G3.** A vertex with a preconnected model-boundary image has exactly one face: each of its
faces is its whole boundary image. -/
theorem face_eq_boundaryImage_of_isPreconnected {k : Fin D.vertexCount}
    (hk : IsPreconnected (D.vertex k).boundaryImage) (f : Fin D.faceCount) (hf : D.faceOwner f = k) :
    D.face f = (D.vertex k).boundaryImage := by
  subst hf
  refine Subset.antisymm (D.face_subset_boundaryImage f) ?_
  obtain ⟨z, hz⟩ := D.face_nonempty f
  exact D.subset_face_of_isPreconnected f hk Subset.rfl (D.face_subset_boundaryImage f hz) hz

/-! ## Bad vertices and the terminal B5 -/

open Classical in
/-- **G3 / N-packet definition.** The number of BAD vertices: not a ball (`Vertex.IsBall`, lane
ASM-CYC3's shared predicate, `Closure/AssemblyCycleBallVertex.lean`), and owner of a partitioned
face with a sphere model (review 40 §1.4). -/
def badVertexCount : ℕ :=
  (Finset.univ.filter fun k : Fin D.vertexCount =>
    ¬ (D.vertex k).IsBall ∧
      ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned ∧
        ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e).card

/-- **G3, terminal B5** (review 40 §1.4). -/
theorem partitionedSphereFace_ball_of_badVertexCount_eq_zero (hbad : D.badVertexCount = 0)
    (f : Fin D.faceCount) (hf : D.faceKind f = .partitioned)
    (hS : ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) :
    (D.vertex (D.faceOwner f)).IsBall := by
  classical
  by_contra hnot
  have hmem : D.faceOwner f ∈ (Finset.univ.filter fun k : Fin D.vertexCount =>
      ¬ (D.vertex k).IsBall ∧
        ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned ∧
          ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            D.faceModel f = .inl e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot, f, rfl, hf, hS⟩
  rw [badVertexCount, Finset.card_eq_zero] at hbad
  convert Finset.notMem_empty _ (hbad ▸ hmem)

end DecompositionCertificate

end GC.GraphManifold.Assembly
