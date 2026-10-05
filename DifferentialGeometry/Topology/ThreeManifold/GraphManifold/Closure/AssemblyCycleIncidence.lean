import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleVerticalApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models

/-!
# FC42 packet H1 (part b): global incidence and disjointness; corrected B9, B10, B11

Lane ASM-CYC2, review 40 §4.3–§4.5 (frozen statements:
`build-logs/scratch/ASM-CYC2/H1Targets.lean`).

* `handle_point_cases`: a handle point is model-interior, vertical (rim × open interval), an
  end-disk point off the rim, or a corner (rim × end).
* `false_of_handle_mem_piece`: no full-rank piece whose interior avoids the interiors of the handle,
  the circle region and the two end vertices passes through a handle point (interior: density;
  vertical: vertical propagation + no third piece; end disk: no third piece; corner: the full rim
  chart).
* **Global statements:** `handle_images_disjoint`, `handle_image_disjoint_edgeCircle`, the
  incidence formula `handle_inter_vertex_image`, `ball_image_disjoint_vertex_image`,
  `ball_image_disjoint_edgeCircle`, `ball_image_subset_interior`.
* **Corrected dry stubs of FC42** (`build-logs/scratch/ASM-V3/FC42Dry.lean`): B11
  `cycle_handle_disjoint` (same hypotheses as the dry stub), B9 `cycle_handle_ball_inter` (with the
  builder hypotheses `hbinj`, `hv`, `hends`), B10 `cycle_ball_disjoint` (with `hpart`) and its
  builder form `cycle_ball_disjoint_of_hends`.

The ball statements use lane ASM-CYC3's `Vertex.IsBall` and `face_eq_boundaryImage_of_isBall`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsH1b_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothH1b_ASMCYC2 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsH1b_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothH1b_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **The four kinds of handle points.** -/
theorem handle_point_cases (p : ClosedCell 2 × Icc (0 : ℝ) 1) :
    ((𝓡∂ 2).prod (𝓡∂ 1)).IsInteriorPoint p ∨
      (p.1 ∈ diskRim ∧ 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1) ∨
        (p.1 ∉ diskRim ∧ ∃ b, p.2 = iccEnd b) ∨ (p.1 ∈ diskRim ∧ ∃ b, p.2 = iccEnd b) := by
  by_cases hb : ((𝓡∂ 2).prod (𝓡∂ 1)).IsBoundaryPoint p
  · right
    by_cases he : ∃ b, p.2 = iccEnd b
    · by_cases hr : p.1 ∈ diskRim
      · exact Or.inr (Or.inr ⟨hr, he⟩)
      · exact Or.inr (Or.inl ⟨hr, he⟩)
    · left
      have hb' := handle_isBoundaryPoint_iff.mp hb
      have hr : p.1 ∈ diskRim := by
        rcases hb' with h1 | h2 | h3
        · exact h1
        · exact (he ⟨false, h2⟩).elim
        · exact (he ⟨true, h3⟩).elim
      refine ⟨hr, ?_⟩
      rcases eq_endpoints_or_mem_Ioo_of_mem_Icc p.2.2 with h0 | h1 | hm
      · exact (he ⟨false, Subtype.ext (by simp [iccEnd, h0])⟩).elim
      · exact (he ⟨true, Subtype.ext (by simp [iccEnd, h1])⟩).elim
      · exact hm
  · left
    exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint p).mpr hb

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The rim circle of a handle end lies in that end disk. -/
theorem handle_rim_mem_endDisk (h : Fin D.handleCount) (b : Bool) (x : ClosedCell 2) :
    (D.handle h).map (x, iccEnd b) ∈ (D.handle h).endDisk b :=
  ⟨x, rfl⟩

/-- End disks lie in the model-boundary image, hence the image, of their end vertex. -/
theorem endDisk_subset_image (h : Fin D.handleCount) (b : Bool) :
    (D.handle h).endDisk b ⊆ (D.vertex (D.handleEnd h b)).image := by
  intro z hz
  have h1 := D.face_subset_boundaryImage (D.handleFace h b) (D.handleEnd_face h b hz)
  rw [D.handleFace_owner] at h1
  obtain ⟨m, -, hm⟩ := h1
  rw [Vertex.image_eq_range_piece]
  exact ⟨m, hm⟩

section Piece

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I ∞ M'] {F : M' → W.Carrier}

/-- **No foreign piece through a handle point.** -/
theorem false_of_handle_mem_piece (hdim : Module.finrank ℝ E' = 3)
    (hF : ContMDiff I W.model ∞ F) (hbij : ∀ q, Bijective (mfderiv I W.model F q))
    (h : Fin D.handleCount) (p : ClosedCell 2 × Icc (0 : ℝ) 1)
    (hmem : (D.handle h).map p ∈ range F)
    (hHF : Disjoint (interior (range (D.handle h).map)) (interior (range F)))
    (hRF : Disjoint (interior D.circ.region) (interior (range F)))
    (hVF : ∀ b, Disjoint (interior (D.vertex (D.handleEnd h b)).image) (interior (range F))) :
    False := by
  obtain ⟨x, t⟩ := p
  rcases handle_point_cases (x, t) with hint | ⟨hx, ht0, ht1⟩ | ⟨hx, b, hb⟩ | ⟨hx, b, hb⟩
  · obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty hdim hF hbij isOpen_interior
      ⟨_, (D.handle h).map_mem_interior_range hint, hmem⟩
    exact Set.disjoint_left.mp hHF hw1 hw2
  · exact D.false_of_vertical_mem_region_of_piece hdim hF hbij h hx ht0 ht1
      (D.handle_vertical_subset_region h ⟨(x, t), ⟨hx, mem_univ _⟩, rfl⟩) hmem hHF hRF
  · simp only at hb
    subst hb
    exact D.false_of_endDisk_of_piece hdim hF hbij h hx b hmem hHF (hVF b)
  · simp only at hb
    subst hb
    have hT := D.handle_rim_mem_target h b hx
    have hdisj := D.disjoint_rimChart_target_of_interior (S := range F)
      (fun O hO hne => inter_interior_range_nonempty hdim hF hbij hO hne) h b (hVF b).symm
      hHF.symm hRF.symm
    exact Set.disjoint_left.mp hdisj hmem hT

end Piece

/-! ## Handles -/

/-- **H1, closed handle images are disjoint** (review 40 §4.3). -/
theorem handle_images_disjoint :
    Pairwise fun h h' => Disjoint (range (D.handle h).map) (range (D.handle h').map) := by
  intro h h' hne
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ hz
  exact D.false_of_handle_mem_piece finrank_handleModel (D.handle h').smooth
    (D.handle h').mfderiv_bijective h p hz (D.handle_disjoint hne) (D.circ_handle_disjoint h')
    (fun b => D.vertex_handle_disjoint _ h')

/-- **H1.** Handles meet no edge circle piece. -/
theorem handle_image_disjoint_edgeCircle (h : Fin D.handleCount) (e : Fin D.edgeCircleCount) :
    Disjoint (range (D.handle h).map) (range (D.edgeCircle e).piece.map) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ hz
  exact D.false_of_handle_mem_piece finrank_euclideanSpace_fin (D.edgeCircle e).piece.smooth
    (D.edgeCircle e).piece.mfderiv_bijective h p hz (D.edgeCircle_handle_disjoint e h).symm
    (D.circ_edgeCircle_disjoint e) (fun b => (D.edgeCircle_vertex_disjoint e _).symm)

/-- **H1, global handle–vertex incidence** (review 40 §4.4). -/
theorem handle_inter_vertex_image (h : Fin D.handleCount) (v : Fin D.vertexCount) :
    range (D.handle h).map ∩ (D.vertex v).image =
      ⋃ (b : Bool) (_ : D.handleEnd h b = v), (D.handle h).endDisk b := by
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨x, t⟩, rfl⟩, hz⟩
    have hz' := hz
    rw [Vertex.image_eq_range_piece] at hz'
    have hHF : Disjoint (interior (range (D.handle h).map))
        (interior (range (D.vertex v).piece.map)) := by
      rw [← Vertex.image_eq_range_piece]
      exact (D.vertex_handle_disjoint v h).symm
    rcases handle_point_cases (x, t) with hint | ⟨hx, ht0, ht1⟩ | ⟨hx, b, hb⟩ | ⟨hx, b, hb⟩
    · obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_euclideanSpace_fin
        (D.vertex v).piece.smooth (D.vertex v).piece.mfderiv_bijective isOpen_interior
        ⟨_, (D.handle h).map_mem_interior_range hint, hz'⟩
      exact (Set.disjoint_left.mp hHF hw1 hw2).elim
    · have hRF : Disjoint (interior D.circ.region) (interior (range (D.vertex v).piece.map)) := by
        rw [← Vertex.image_eq_range_piece]
        exact D.circ_vertex_disjoint v
      exact (D.false_of_vertical_mem_region_of_piece finrank_euclideanSpace_fin
        (D.vertex v).piece.smooth (D.vertex v).piece.mfderiv_bijective h hx ht0 ht1
        (D.handle_vertical_subset_region h ⟨(x, t), ⟨hx, mem_univ _⟩, rfl⟩) hz' hHF hRF).elim
    · simp only at hb
      subst hb
      by_cases hv : D.handleEnd h b = v
      · exact mem_iUnion₂.mpr ⟨b, hv, ⟨x, rfl⟩⟩
      · have hVF : Disjoint (interior (D.vertex (D.handleEnd h b)).image)
            (interior (range (D.vertex v).piece.map)) := by
          rw [← Vertex.image_eq_range_piece]
          exact D.vertex_disjoint hv
        exact (D.false_of_endDisk_of_piece finrank_euclideanSpace_fin (D.vertex v).piece.smooth
          (D.vertex v).piece.mfderiv_bijective h hx b hz' hHF hVF).elim
    · simp only at hb
      subst hb
      by_cases hv : D.handleEnd h b = v
      · exact mem_iUnion₂.mpr ⟨b, hv, ⟨x, rfl⟩⟩
      · exact (Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target h b v (Ne.symm hv)) hz
          (D.handle_rim_mem_target h b hx)).elim
  · intro z hz
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hz
    refine ⟨?_, ?_⟩
    · obtain ⟨x, rfl⟩ := hzb
      exact ⟨_, rfl⟩
    · rw [← hb]
      exact D.endDisk_subset_image h b hzb

/-! ## Balls -/

/-- A point of a vertex image off its ambient interior is in its model-boundary image. -/
theorem mem_boundaryImage_of_not_mem_interior {v : Vertex W} {z : W.Carrier} (hz : z ∈ v.image)
    (hzi : z ∉ interior v.image) : z ∈ v.boundaryImage := by
  rw [Vertex.image_eq_range_piece] at hz hzi
  obtain ⟨m, rfl⟩ := hz
  by_cases hm : (𝓡∂ 3).IsInteriorPoint m
  · exact (hzi (v.piece.toPieceFold.map_mem_interior_range hm)).elim
  · exact ⟨m, ((𝓡∂ 3).isBoundaryPoint_iff_not_isInteriorPoint m).mpr hm, rfl⟩

/-- A common point of two distinct vertices is in neither ambient interior. -/
theorem not_mem_interior_of_mem_two {k k' : Fin D.vertexCount} (hkk' : k ≠ k') {z : W.Carrier}
    (hz' : z ∈ (D.vertex k').image) :
    z ∉ interior (D.vertex k).image := by
  intro hint
  rw [Vertex.image_eq_range_piece (D.vertex k')] at hz'
  obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_euclideanSpace_fin
    (D.vertex k').piece.smooth (D.vertex k').piece.mfderiv_bijective isOpen_interior ⟨z, hint, hz'⟩
  rw [← Vertex.image_eq_range_piece] at hw2
  exact Set.disjoint_left.mp (D.vertex_disjoint hkk') hw1 hw2

/-- **H1 (for ASM-CYC3).** A ball vertex owning a partitioned face has closed image disjoint from
the image of ANY other vertex. -/
theorem ball_image_disjoint_vertex_image {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    (hpart : ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned) {k' : Fin D.vertexCount}
    (hkk' : k ≠ k') : Disjoint (D.vertex k).image (D.vertex k').image := by
  obtain ⟨f, hfo, hfk⟩ := hpart
  rw [Set.disjoint_left]
  intro z hz hz'
  have hzB : z ∈ (D.vertex k).boundaryImage :=
    mem_boundaryImage_of_not_mem_interior hz (D.not_mem_interior_of_mem_two hkk' hz')
  have hzB' : z ∈ (D.vertex k').boundaryImage :=
    mem_boundaryImage_of_not_mem_interior hz' (D.not_mem_interior_of_mem_two (Ne.symm hkk') hz)
  rw [← D.face_eq_boundaryImage_of_isBall hk hfo] at hzB
  rw [← D.face_exhausted] at hzB'
  obtain ⟨f', hzf'⟩ := mem_iUnion.mp hzB'
  obtain ⟨hfo', hzf'⟩ := mem_iUnion.mp hzf'
  have hne : f ≠ f' := fun he => hkk' (by rw [← hfo, ← hfo', he])
  have hdisj := D.face_disjoint f f' hne (fun c b hc => by rw [hfk] at hc; cases hc.1)
    (fun c b hc => by rw [hfk] at hc; cases hc.1)
  exact Set.disjoint_left.mp hdisj hzB hzf'

/-- The face of a ball owning a partitioned face: its whole boundary image is end disks, arcs and
loops; a point of it is either on an end disk or in the circle region. -/
theorem mem_endDisk_or_region_of_partitioned {f : Fin D.faceCount}
    (hfk : D.faceKind f = .partitioned) {z : W.Carrier} (hz : z ∈ D.face f) :
    (∃ h b, z ∈ (D.handle h).endDisk b) ∨ z ∈ D.circ.region := by
  have hreg := D.face_region_inter f hfk
  rw [← D.face_partition f hfk] at hz
  rcases hz with (hd | ha) | hl
  · obtain ⟨h, hd⟩ := mem_iUnion.mp hd
    obtain ⟨b, hd⟩ := mem_iUnion.mp hd
    obtain ⟨-, hd⟩ := mem_iUnion.mp hd
    exact Or.inl ⟨h, b, hd⟩
  · right
    have hzf : z ∈ D.face f := by
      rw [← D.face_partition f hfk]
      exact Or.inl (Or.inr ha)
    have : z ∈ D.face f ∩ D.circ.region := by
      rw [hreg]
      exact Or.inl ha
    exact this.2
  · right
    have : z ∈ D.face f ∩ D.circ.region := by
      rw [hreg]
      exact Or.inr hl
    exact this.2

/-- **H1 (for ASM-CYC3).** A ball vertex owning a partitioned face meets no edge circle piece. -/
theorem ball_image_disjoint_edgeCircle {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    (hpart : ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned) (e : Fin D.edgeCircleCount) :
    Disjoint (D.vertex k).image (range (D.edgeCircle e).piece.map) := by
  obtain ⟨f, hfo, hfk⟩ := hpart
  rw [Set.disjoint_left]
  intro z hz hze
  have hzi : z ∉ interior (D.vertex k).image := by
    intro hint
    obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_euclideanSpace_fin
      (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective isOpen_interior
      ⟨z, hint, hze⟩
    exact Set.disjoint_left.mp (D.edgeCircle_vertex_disjoint e k) hw2 hw1
  have hzB := mem_boundaryImage_of_not_mem_interior hz hzi
  have hzf : z ∈ D.face f := by
    rw [D.face_eq_boundaryImage_of_isBall hk hfo]
    exact hzB
  rcases D.mem_endDisk_or_region_of_partitioned hfk hzf with ⟨h, b, hzd⟩ | hzR
  · obtain ⟨x, rfl⟩ := hzd
    exact Set.disjoint_left.mp (D.handle_image_disjoint_edgeCircle h e) ⟨_, rfl⟩ hze
  · rcases D.region_trichotomy hzR with hint | hent | ⟨h, b, hrim, -⟩
    · obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_euclideanSpace_fin
        (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective isOpen_interior
        ⟨z, hint, hze⟩
      exact Set.disjoint_left.mp (D.circ_edgeCircle_disjoint e) hw1 hw2
    · obtain ⟨q, hq⟩ := hze
      have hA := Vertex.exists_entering hzB
      rw [← hq] at hA hent
      exact false_of_two_entering_and_piece finrank_euclideanSpace_fin
        (D.edgeCircle e).piece.smooth (D.edgeCircle e).piece.mfderiv_bijective q hA hent
        (D.circ_vertex_disjoint k).symm (D.edgeCircle_vertex_disjoint e k).symm
        (D.circ_edgeCircle_disjoint e)
    · obtain ⟨x, -, rfl⟩ := hrim
      exact Set.disjoint_left.mp (D.handle_image_disjoint_edgeCircle h e) ⟨_, rfl⟩ hze

/-- **H1 (for the L1 lanes).** The image of a ball vertex owning a partitioned face lies in the
interior of `W` (its whole boundary is that face: end disks in handles, arcs and loops in the circle
region). -/
theorem ball_image_subset_interior {k : Fin D.vertexCount} (hk : (D.vertex k).IsBall)
    (hpart : ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned) :
    (D.vertex k).image ⊆ (W.interior : Set W.Carrier) := by
  obtain ⟨f, hfo, hfk⟩ := hpart
  intro z hz
  by_cases hzB : z ∈ (D.vertex k).boundaryImage
  · rw [← D.face_eq_boundaryImage_of_isBall hk hfo] at hzB
    rcases D.mem_endDisk_or_region_of_partitioned hfk hzB with ⟨h, b, ⟨x, rfl⟩⟩ | hzR
    · exact (D.handle h).interior ⟨_, rfl⟩
    · exact D.circ.region_subset_interior hzR
  · rw [Vertex.image_eq_range_piece] at hz
    obtain ⟨m, rfl⟩ := hz
    have hm : (𝓡∂ 3).IsInteriorPoint m := by
      rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
      exact fun hb => hzB ⟨m, hb, rfl⟩
    exact ((D.vertex k).piece.smooth.mdifferentiableAt
      (by simp)).isInteriorPoint_of_surjective_mfderiv ((D.vertex k).piece.mfderiv_bijective m).2 hm

end DecompositionCertificate

/-! ## Corrected B11, B9, B10 -/

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **Corrected B11** (dry `dry_cycle_handle_disjoint`, same hypotheses; `dry_orient` is the built
`EdgeHandle.orient`). -/
theorem cycle_handle_disjoint (D : DecompositionCertificate W E) (len : ℕ)
    (handleIdx : Fin len → Fin D.handleCount) (hinj : Injective handleIdx) (σ : Fin len → Bool) :
    Pairwise fun k k' => Disjoint (range ((D.handle (handleIdx k)).orient (σ k)).map)
      (range ((D.handle (handleIdx k')).orient (σ k')).map) := by
  intro k k' hkk'
  rw [EdgeHandle.orient_range, EdgeHandle.orient_range]
  exact D.handle_images_disjoint fun he => hkk' (hinj he)

/-- **Corrected B9** (dry `dry_cycle_handle_ball_inter` was false for arbitrary `P`): with the
builder hypotheses `hbinj`, `hv`, `hends` of `dry_cycleOfCertificate`. For `len = 1` both end
disks lie on the same ball and both terms of the union are present. -/
theorem cycle_handle_ball_inter (D : DecompositionCertificate W E) (len : ℕ)
    (ballIdx : Fin len → Fin D.vertexCount) (hbinj : Injective ballIdx)
    (P : Fin len → PieceEmbedding W) (eB : ∀ k, (P k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hv : ∀ k, D.vertex (ballIdx k) = .zero (P k) (.ball (eB k)))
    (handleIdx : Fin len → Fin D.handleCount) (σ : Fin len → Bool)
    (hends : ∀ k b, D.handleEnd (handleIdx k) (xor b (σ k)) = ballIdx (rimBall len k b))
    (k j : Fin len) :
    range ((D.handle (handleIdx k)).orient (σ k)).map ∩ range (P j).map =
      (if j = k then ((D.handle (handleIdx k)).orient (σ k)).endDisk false else ∅) ∪
        (if j = finRotate len k then ((D.handle (handleIdx k)).orient (σ k)).endDisk true
          else ∅) := by
  have hPj : range (P j).map = (D.vertex (ballIdx j)).image := by rw [hv j]; rfl
  rw [EdgeHandle.orient_range, hPj, D.handle_inter_vertex_image, EdgeHandle.orient_endDisk,
    EdgeHandle.orient_endDisk]
  have hcond : ∀ b, D.handleEnd (handleIdx k) (xor b (σ k)) = ballIdx j ↔ rimBall len k b = j :=
    fun b => by rw [hends k b, hbinj.eq_iff]
  ext z
  simp only [mem_iUnion, exists_prop, mem_union]
  constructor
  · rintro ⟨b', hb', hz⟩
    have hb'' : b' = xor (xor b' (σ k)) (σ k) := by cases b' <;> cases σ k <;> rfl
    rw [hb''] at hb' hz
    rcases hxb : xor b' (σ k) with _ | _
    · rw [hxb] at hb' hz
      have := (hcond false).mp hb'
      simp only [rimBall_false] at this
      left
      split_ifs with hj
      · exact hz
      · exact (hj this.symm).elim
    · rw [hxb] at hb' hz
      have := (hcond true).mp hb'
      simp only [rimBall_true] at this
      right
      split_ifs with hj
      · exact hz
      · exact (hj this.symm).elim
  · rintro (hz | hz)
    · split_ifs at hz with hj
      · exact ⟨xor false (σ k), (hcond false).mpr (by simp [hj]), hz⟩
      · exact hz.elim
    · split_ifs at hz with hj
      · exact ⟨xor true (σ k), (hcond true).mpr (by simp [hj]), hz⟩
      · exact hz.elim

/-- **Corrected B10** (dry `dry_cycle_ball_disjoint` is false under V4: two hemispheres of `S³`):
with `hpart`, each ball owns a partitioned face. -/
theorem cycle_ball_disjoint (D : DecompositionCertificate W E) (len : ℕ)
    (ballIdx : Fin len → Fin D.vertexCount) (hinj : Injective ballIdx)
    (P : Fin len → PieceEmbedding W) (eB : ∀ k, (P k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hv : ∀ k, D.vertex (ballIdx k) = .zero (P k) (.ball (eB k)))
    (hpart : ∀ k, ∃ f, D.faceOwner f = ballIdx k ∧ D.faceKind f = .partitioned) :
    Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map) := by
  intro k k' hkk'
  have hP : ∀ j, range (P j).map = (D.vertex (ballIdx j)).image := fun j => by rw [hv j]; rfl
  rw [hP, hP]
  exact D.ball_image_disjoint_vertex_image ⟨P k, eB k, hv k⟩ (hpart k)
    fun he => hkk' (hinj he)

/-- **Corrected B10, builder form:** `hpart` produced from `hends` and `handleFace_kind`. -/
theorem cycle_ball_disjoint_of_hends (D : DecompositionCertificate W E) (len : ℕ)
    (ballIdx : Fin len → Fin D.vertexCount) (hinj : Injective ballIdx)
    (P : Fin len → PieceEmbedding W) (eB : ∀ k, (P k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hv : ∀ k, D.vertex (ballIdx k) = .zero (P k) (.ball (eB k)))
    (handleIdx : Fin len → Fin D.handleCount) (σ : Fin len → Bool)
    (hends : ∀ k b, D.handleEnd (handleIdx k) (xor b (σ k)) = ballIdx (rimBall len k b)) :
    Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map) :=
  cycle_ball_disjoint D len ballIdx hinj P eB hv fun k =>
    ⟨D.handleFace (handleIdx k) (xor false (σ k)),
      by rw [D.handleFace_owner, hends k false, rimBall_false],
      D.handleFace_kind _ _⟩

end GC.GraphManifold.Assembly
