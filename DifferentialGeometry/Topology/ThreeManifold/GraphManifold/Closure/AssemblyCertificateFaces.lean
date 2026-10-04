import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.ClosedBall.UnitDisk
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceRecognition

/-!
# The FC39 certificate: the per-vertex boundary partition and the FC40 inputs

Structural lemmas on the face fields of `DecompositionCertificate W E` (`AssemblyCertificate.lean`, V2
review item 3, D4):

* **Faces partition the vertex boundaries.** `boundaryImage_eq_iUnion_face`, `face_subset_boundaryImage`;
  faces are compact (`isCompact_face`, from `faceModel`), end disks and arcs are compact, loops are
  closed; end disks, arcs and loops lie in their owner face.
* **Endpoint bijection.** `arcEndEquiv j : Bool ≃ {hb // handleArc hb.1 hb.2 = j}`: every arc has
  exactly two handle ends.
* **FC40 input shape on a partitioned face `f`.** With `Y := face f`, the disks
  `FaceEnd f = {hb // handleFace hb.1 hb.2 = f}` (`faceDisk`), the strata
  `FaceStratum f = arcs of f ⊕ loops of f` (`faceStratumSet`) and the side map `faceSide` (the arc
  through the rim of the disk), the hypotheses of `Surface.disk_face_count_torus`
  (`Surface/Recognition/DiskFaceRecognition.lean:180`; wrapped by `Connected/DiskFaceDegree.lean:38–66`)
  are proved from the fields: closedness, nonemptiness, cover, disjointness, `hDB`, the degree `hdeg`
  (2 for an arc, 0 for a loop: the endpoint bijection), `hdisk` (the end-disk parametrization from
  `endDisk_rim`, through the adapter `Disk 2 ≃ ClosedCell 2`) and `hann` (from `arcAnnulus_end`).
  The degree is fed directly: the `DiskFaceDegree` wrappers ask for an equivalence with the boundary of
  a compact `𝓡∂ 1` manifold per stratum, and the tree has no `𝓡∂ 1` model of the circle for loops.
* **Consumer (FC40 on a torus face).** A partitioned face homeomorphic to `T²` contains no handle end
  and exactly one stratum (`card_faceStratum_eq_one_and_card_faceEnd_eq_zero`); it has no arc, and
  it is one whole loop face (`exists_loop_eq_face_of_torus`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsFaces_ASMCERT : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-- The rim of the closed disk is its unit circle. -/
theorem diskRim_eq : diskRim = {x : ClosedCell 2 | ‖x.val‖ = 1} :=
  DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1

/-- The adapter between the two closed unit disks of the tree (`Disk 2` of FC40, `ClosedCell 2` of
the handles). -/
def diskToCell (x : Disk 2) : ClosedCell 2 :=
  ⟨x.1, mem_closedBall_zero_iff.1 x.2⟩

/-- The inverse adapter. -/
def cellToDisk (x : ClosedCell 2) : Disk 2 :=
  ⟨x.1, mem_closedBall_zero_iff.2 x.2⟩

@[simp]
theorem diskToCell_cellToDisk (x : ClosedCell 2) : diskToCell (cellToDisk x) = x :=
  rfl

theorem continuous_diskToCell : Continuous diskToCell :=
  continuous_subtype_val.subtype_mk _

theorem injective_diskToCell : Injective diskToCell := fun _ _ h =>
  Subtype.ext (congrArg (fun c : ClosedCell 2 => c.1) h)

theorem mem_diskSphere_iff_diskToCell_mem_diskRim {x : Disk 2} :
    x ∈ diskSphere 2 ↔ diskToCell x ∈ diskRim := by
  rw [diskRim_eq, mem_diskSphere]
  rfl

namespace EdgeHandle

variable {W : CompactCarrier.{u}} (H : EdgeHandle W)

theorem continuous_endMap (b : Bool) : Continuous fun x : ClosedCell 2 => H.map (x, iccEnd b) :=
  H.smooth.continuous.comp (continuous_id.prodMk continuous_const)

theorem isCompact_endDisk (b : Bool) : IsCompact (H.endDisk b) :=
  isCompact_range (H.continuous_endMap b)

theorem isClosed_endDisk (b : Bool) : IsClosed (H.endDisk b) :=
  (H.isCompact_endDisk b).isClosed

end EdgeHandle

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-! ## Faces partition the vertex boundaries -/

theorem boundaryImage_eq_iUnion_face (k : Fin D.vertexCount) :
    (D.vertex k).boundaryImage = ⋃ (f : Fin D.faceCount) (_ : D.faceOwner f = k), D.face f :=
  (D.face_exhausted k).symm

theorem face_subset_boundaryImage (f : Fin D.faceCount) :
    D.face f ⊆ (D.vertex (D.faceOwner f)).boundaryImage := by
  rw [D.boundaryImage_eq_iUnion_face]
  exact subset_iUnion₂ (s := fun f' (_ : D.faceOwner f' = D.faceOwner f) => D.face f') f rfl

theorem isCompact_face (f : Fin D.faceCount) : IsCompact (D.face f) := by
  rcases D.faceModel f with φ | φ
  · have : CompactSpace (D.face f) := φ.symm.compactSpace
    exact isCompact_iff_compactSpace.2 this
  · have : CompactSpace (D.face f) := φ.symm.compactSpace
    exact isCompact_iff_compactSpace.2 this

theorem isClosed_face (f : Fin D.faceCount) : IsClosed (D.face f) :=
  (D.isCompact_face f).isClosed

theorem isCompact_arcFace (j : Fin D.arcFaceCount) : IsCompact (D.arcFace j) :=
  D.arcAnnulus_range j ▸ isCompact_range (D.arcAnnulus_continuous j)

theorem isClosed_arcFace (j : Fin D.arcFaceCount) : IsClosed (D.arcFace j) :=
  (D.isCompact_arcFace j).isClosed

theorem arcFace_nonempty (j : Fin D.arcFaceCount) : (D.arcFace j).Nonempty := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 2)) (x := 0)
    (r := 1)).2 zero_le_one
  rw [← D.arcAnnulus_range j]
  exact ⟨_, ⟨(⟨v, hv⟩, iccEnd false), rfl⟩⟩

theorem endDisk_subset_face (h : Fin D.handleCount) (b : Bool) :
    (D.handle h).endDisk b ⊆ D.face (D.handleFace h b) :=
  D.handleEnd_face h b

theorem arcFace_subset_face (j : Fin D.arcFaceCount) : D.arcFace j ⊆ D.face (D.arcOwner j) := by
  rw [← D.face_partition _ (D.arcOwner_kind j)]
  exact subset_union_of_subset_left (subset_union_of_subset_right
    (subset_iUnion₂ (s := fun j' (_ : D.arcOwner j' = D.arcOwner j) => D.arcFace j') j rfl) _) _

theorem loopFace_subset_face (j : Fin D.loopFaceCount) :
    D.loopFace j ⊆ D.face (D.loopOwner j) := by
  rw [← D.face_partition _ (D.loopOwner_kind j)]
  exact subset_union_of_subset_right
    (subset_iUnion₂ (s := fun j' (_ : D.loopOwner j' = D.loopOwner j) => D.loopFace j') j rfl) _

/-! ## The endpoint bijection -/

theorem handleFace_arcEnd (j : Fin D.arcFaceCount) (e : Bool) :
    D.handleFace (D.arcEnd j e).1 (D.arcEnd j e).2 = D.arcOwner j :=
  (D.handleArc_owner _ _).symm.trans (congrArg D.arcOwner (D.arcEnd_arc j e))

/-- **Endpoint bijection.** The two ends of arc `j` are exactly the handle ends whose rim lies on it. -/
def arcEndEquiv (j : Fin D.arcFaceCount) :
    Bool ≃ {hb : Fin D.handleCount × Bool // D.handleArc hb.1 hb.2 = j} :=
  Equiv.ofBijective (fun e => ⟨D.arcEnd j e, D.arcEnd_arc j e⟩)
    ⟨fun e e' h => D.arcEnd_injective j (congrArg Subtype.val h), fun ⟨⟨h, b⟩, hj⟩ => by
      obtain ⟨e, he⟩ := D.arcEnd_surjective h b
      subst hj
      exact ⟨e, Subtype.ext he⟩⟩

@[simp]
theorem arcEndEquiv_apply (j : Fin D.arcFaceCount) (e : Bool) :
    (D.arcEndEquiv j e : Fin D.handleCount × Bool) = D.arcEnd j e :=
  rfl

/-! ## The FC40 input shape on one face -/

/-- The handle ends whose end disk lies in face `f`: the disks of FC40. -/
abbrev FaceEnd (f : Fin D.faceCount) : Type :=
  {hb : Fin D.handleCount × Bool // D.handleFace hb.1 hb.2 = f}

/-- The circle-region strata of face `f`, its arcs and its loops: the bundle components of FC40. -/
abbrev FaceStratum (f : Fin D.faceCount) : Type :=
  {j : Fin D.arcFaceCount // D.arcOwner j = f} ⊕ {j : Fin D.loopFaceCount // D.loopOwner j = f}

/-- The end disk of a handle end, inside its face. -/
def faceDisk (f : Fin D.faceCount) (i : D.FaceEnd f) : Set (D.face f) :=
  Subtype.val ⁻¹' (D.handle i.1.1).endDisk i.1.2

/-- An arc or loop face, inside its owner face. -/
def faceStratumSet (f : Fin D.faceCount) : D.FaceStratum f → Set (D.face f)
  | .inl j => Subtype.val ⁻¹' D.arcFace j.1
  | .inr j => Subtype.val ⁻¹' D.loopFace j.1

/-- The stratum met by an end disk: the arc through its rim. -/
def faceSide (f : Fin D.faceCount) (i : D.FaceEnd f) : D.FaceStratum f :=
  .inl ⟨D.handleArc i.1.1 i.1.2, (D.handleArc_owner _ _).trans i.2⟩

theorem isClosed_faceDisk (f : Fin D.faceCount) (i : D.FaceEnd f) : IsClosed (D.faceDisk f i) :=
  ((D.handle i.1.1).isClosed_endDisk i.1.2).preimage continuous_subtype_val

theorem isClosed_faceStratumSet (f : Fin D.faceCount) (j : D.FaceStratum f) :
    IsClosed (D.faceStratumSet f j) := by
  rcases j with j | j
  · exact (D.isClosed_arcFace j.1).preimage continuous_subtype_val
  · exact (D.loopFace_closed j.1).preimage continuous_subtype_val

theorem faceStratumSet_nonempty (f : Fin D.faceCount) (j : D.FaceStratum f) :
    (D.faceStratumSet f j).Nonempty := by
  rcases j with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨x, hx⟩ := D.arcFace_nonempty j
    exact ⟨⟨x, hj ▸ D.arcFace_subset_face j hx⟩, hx⟩
  · obtain ⟨x, hx⟩ := D.loopFace_nonempty j
    exact ⟨⟨x, hj ▸ D.loopFace_subset_face j hx⟩, hx⟩

/-- FC40 `hcover`: the end disks and the strata cover a partitioned face. -/
theorem iUnion_faceDisk_union_iUnion_faceStratumSet {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) :
    (⋃ i, D.faceDisk f i) ∪ (⋃ j, D.faceStratumSet f j) = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hy := (Set.ext_iff.1 (D.face_partition f hf) y.1).2 y.2
  simp only [mem_union, mem_iUnion] at hy
  rcases hy with (⟨h, b, hhb, hy⟩ | ⟨j, hj, hy⟩) | ⟨j, hj, hy⟩
  · exact Or.inl (mem_iUnion.2 ⟨⟨(h, b), hhb⟩, hy⟩)
  · exact Or.inr (mem_iUnion.2 ⟨.inl ⟨j, hj⟩, hy⟩)
  · exact Or.inr (mem_iUnion.2 ⟨.inr ⟨j, hj⟩, hy⟩)

/-- FC40 `hDD`. -/
theorem pairwise_disjoint_faceDisk (f : Fin D.faceCount) :
    Pairwise (Disjoint on D.faceDisk f) := fun i i' hii' =>
  (D.endDisk_disjoint i.1.1 i.1.2 i'.1.1 i'.1.2 fun h => hii' (Subtype.ext h)).preimage _

/-- FC40 `hBB`. -/
theorem pairwise_disjoint_faceStratumSet (f : Fin D.faceCount) :
    Pairwise (Disjoint on D.faceStratumSet f) := by
  rintro (j | j) (j' | j') hjj'
  · exact (D.arcFace_disjoint fun h => hjj' (congrArg Sum.inl (Subtype.ext h))).preimage _
  · exact (D.arc_loop_disjoint j.1 j'.1).preimage _
  · exact (D.arc_loop_disjoint j'.1 j.1).symm.preimage _
  · exact (D.loopFace_disjoint fun h => hjj' (congrArg Sum.inr (Subtype.ext h))).preimage _

/-- FC40 `hDB`: an end disk meets only the arc through its rim. -/
theorem faceSide_eq_of_nonempty (f : Fin D.faceCount) (i : D.FaceEnd f) (j : D.FaceStratum f)
    (hij : (D.faceDisk f i ∩ D.faceStratumSet f j).Nonempty) : D.faceSide f i = j := by
  obtain ⟨y, hyD, hyB⟩ := hij
  rcases j with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact congrArg Sum.inl (Subtype.ext (D.handleArc_meets i.1.1 i.1.2 j ⟨y.1, hyD, hyB⟩))
  · exact ((D.endDisk_loop_disjoint i.1.1 i.1.2 j).le_bot ⟨hyD, hyB⟩).elim

theorem card_filter_faceSide_inl (f : Fin D.faceCount) (j : {j : Fin D.arcFaceCount // D.arcOwner j = f}) :
    (Finset.univ.filter fun i => D.faceSide f i = .inl j).card = 2 := by
  rw [← Fintype.card_subtype]
  refine (Fintype.card_congr (Equiv.ofBijective
    (fun e : Bool => (⟨⟨D.arcEnd j.1 e, (D.handleFace_arcEnd j.1 e).trans j.2⟩,
      congrArg Sum.inl (Subtype.ext (D.arcEnd_arc j.1 e))⟩ :
        {i : D.FaceEnd f // D.faceSide f i = .inl j})) ⟨?_, ?_⟩)).symm.trans Fintype.card_bool
  · intro e e' h
    exact D.arcEnd_injective j.1 (congrArg (fun i => i.1.1) h)
  · rintro ⟨⟨⟨h, b⟩, hhb⟩, hside⟩
    have hj : D.handleArc h b = j.1 := congrArg Subtype.val (Sum.inl_injective hside)
    obtain ⟨e, he⟩ := D.arcEnd_surjective h b
    rw [hj] at he
    exact ⟨e, Subtype.ext (Subtype.ext he)⟩

theorem card_filter_faceSide_inr (f : Fin D.faceCount)
    (j : {j : Fin D.loopFaceCount // D.loopOwner j = f}) :
    (Finset.univ.filter fun i => D.faceSide f i = .inr j).card = 0 :=
  Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ h => Sum.inl_ne_inr h)

/-- FC40 `hdeg`: every stratum has `0` (loop) or `2` (arc) disks. -/
theorem card_filter_faceSide (f : Fin D.faceCount) (j : D.FaceStratum f) :
    (Finset.univ.filter fun i => D.faceSide f i = j).card = 0 ∨
      (Finset.univ.filter fun i => D.faceSide f i = j).card = 2 := by
  rcases j with j | j
  · exact Or.inr (D.card_filter_faceSide_inl f j)
  · exact Or.inl (D.card_filter_faceSide_inr f j)

/-- FC40 `hdisk`: the end disk parametrization, with the rim–stratum equality from `endDisk_rim`. -/
theorem exists_disk_param (f : Fin D.faceCount) (i : D.FaceEnd f) :
    ∃ g : Disk 2 → D.face f, Continuous g ∧ Injective g ∧ range g = D.faceDisk f i ∧
      g '' diskSphere 2 = D.faceDisk f i ∩ D.faceStratumSet f (D.faceSide f i) := by
  obtain ⟨⟨h, b⟩, hhb⟩ := i
  have hmem : ∀ x : ClosedCell 2, (D.handle h).map (x, iccEnd b) ∈ D.face f := fun x =>
    hhb ▸ D.endDisk_subset_face h b ⟨x, rfl⟩
  refine ⟨fun x => ⟨(D.handle h).map (diskToCell x, iccEnd b), hmem _⟩,
    (((D.handle h).continuous_endMap b).comp continuous_diskToCell).subtype_mk _, ?_, ?_, ?_⟩
  · intro x x' hxx'
    exact injective_diskToCell (congrArg Prod.fst ((D.handle h).injective
      (congrArg Subtype.val hxx')))
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨diskToCell x, rfl⟩
    · rintro ⟨c, hc⟩
      exact ⟨cellToDisk c, Subtype.ext hc⟩
  · ext y
    have hrim := D.endDisk_rim h b
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (D.handle h).map (diskToCell x, iccEnd b) ∈
          (D.handle h).endDisk b ∩ D.arcFace (D.handleArc h b) :=
        hrim ▸ ⟨diskToCell x, mem_diskSphere_iff_diskToCell_mem_diskRim.1 hx, rfl⟩
      exact ⟨this.1, this.2⟩
    · rintro ⟨hyD, hyB⟩
      have hy : y.1 ∈ (D.handle h).endDisk b ∩ D.arcFace (D.handleArc h b) := ⟨hyD, hyB⟩
      rw [← hrim] at hy
      obtain ⟨c, hc, hcy⟩ := hy
      refine ⟨cellToDisk c, mem_diskSphere_iff_diskToCell_mem_diskRim.2 hc, Subtype.ext hcy⟩

/-- FC40 `hann`: the annulus parametrization of an arc with its two end circles. -/
theorem exists_annulus_param (f : Fin D.faceCount) (j : D.FaceStratum f)
    (hj : (Finset.univ.filter fun i => D.faceSide f i = j).card = 2) :
    ∃ a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → D.face f,
      Continuous a ∧ Injective a ∧ range a = D.faceStratumSet f j ∧ ∀ i, D.faceSide f i = j →
        D.faceDisk f i ∩ D.faceStratumSet f j = a '' {q | (q.2 : ℝ) = 0} ∨
          D.faceDisk f i ∩ D.faceStratumSet f j = a '' {q | (q.2 : ℝ) = 1} := by
  rcases j with ⟨j, hjf⟩ | j
  swap
  · rw [D.card_filter_faceSide_inr] at hj
    exact absurd hj (by norm_num)
  have hmem : ∀ q, D.arcAnnulus j q ∈ D.face f := fun q =>
    hjf ▸ D.arcFace_subset_face j (D.arcAnnulus_range j ▸ mem_range_self q)
  refine ⟨fun q => ⟨D.arcAnnulus j q, hmem q⟩,
    (D.arcAnnulus_continuous j).subtype_mk _, fun q q' h =>
      D.arcAnnulus_injective j (congrArg Subtype.val h), ?_, ?_⟩
  · ext y
    change y ∈ range _ ↔ y.1 ∈ D.arcFace j
    rw [← D.arcAnnulus_range j]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, Subtype.ext hq⟩
  · rintro ⟨⟨h, b⟩, hhb⟩ hside
    have hj' : D.handleArc h b = j := congrArg Subtype.val (Sum.inl_injective hside)
    obtain ⟨e, he⟩ := D.arcEnd_surjective h b
    rw [hj'] at he
    have hend := D.arcAnnulus_end j e
    rw [he] at hend
    have key : D.faceDisk f ⟨(h, b), hhb⟩ ∩ D.faceStratumSet f (.inl ⟨j, hjf⟩) =
        (fun q => (⟨D.arcAnnulus j q, hmem q⟩ : D.face f)) '' {q | q.2 = iccEnd e} := by
      ext y
      change y.1 ∈ (D.handle h).endDisk b ∧ y.1 ∈ D.arcFace j ↔ _
      rw [← mem_inter_iff, hend]
      constructor
      · rintro ⟨q, hq, hqy⟩
        exact ⟨q, hq, Subtype.ext hqy⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
    rw [key]
    cases e
    · left
      congr 1
      exact Set.ext fun q => Subtype.ext_iff
    · right
      congr 1
      exact Set.ext fun q => Subtype.ext_iff

/-! ## The consumer: FC40 on a torus face -/

/-- **FC40 on a partitioned torus face.** It contains no handle end and exactly one stratum. -/
theorem card_faceStratum_eq_one_and_card_faceEnd_eq_zero {f : Fin D.faceCount}
    (hf : D.faceKind f = .partitioned) (φ : D.face f ≃ₜ Circle × Circle) :
    Fintype.card (D.FaceStratum f) = 1 ∧ Fintype.card (D.FaceEnd f) = 0 :=
  Surface.disk_face_count_torus φ (D.faceDisk f) (D.faceStratumSet f) (D.isClosed_faceDisk f)
    (D.isClosed_faceStratumSet f) (D.faceStratumSet_nonempty f)
    (D.iUnion_faceDisk_union_iUnion_faceStratumSet hf) (D.pairwise_disjoint_faceDisk f)
    (D.pairwise_disjoint_faceStratumSet f) (D.faceSide f) (D.faceSide_eq_of_nonempty f)
    (D.card_filter_faceSide f) (D.exists_disk_param f) (D.exists_annulus_param f)

/-- A partitioned torus face contains no handle end disk. -/
theorem handleFace_ne_of_torus {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ Circle × Circle) (h : Fin D.handleCount) (b : Bool) : D.handleFace h b ≠ f :=
  fun hhb => (Fintype.card_eq_zero_iff.1
    (D.card_faceStratum_eq_one_and_card_faceEnd_eq_zero hf φ).2).false ⟨(h, b), hhb⟩

/-- A partitioned torus face has no arc. -/
theorem arcOwner_ne_of_torus {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ Circle × Circle) (j : Fin D.arcFaceCount) : D.arcOwner j ≠ f := fun hj =>
  D.handleFace_ne_of_torus hf φ _ _ ((D.handleFace_arcEnd j false).trans hj)

/-- **A partitioned torus face is one whole loop face.** -/
theorem exists_loop_eq_face_of_torus {f : Fin D.faceCount} (hf : D.faceKind f = .partitioned)
    (φ : D.face f ≃ₜ Circle × Circle) :
    ∃ j : Fin D.loopFaceCount, D.loopOwner j = f ∧ D.face f = D.loopFace j ∧
      ∀ j' : Fin D.loopFaceCount, D.loopOwner j' = f → j' = j := by
  have hcard := (D.card_faceStratum_eq_one_and_card_faceEnd_eq_zero hf φ).1
  obtain ⟨s, hs⟩ := Fintype.card_eq_one_iff.1 hcard
  rcases s with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact absurd hj (D.arcOwner_ne_of_torus hf φ j)
  have huniq : ∀ j' : Fin D.loopFaceCount, D.loopOwner j' = f → j' = j := fun j' hj' =>
    congrArg Subtype.val (Sum.inr_injective (hs (.inr ⟨j', hj'⟩)))
  refine ⟨j, hj, ?_, huniq⟩
  apply Subset.antisymm
  · intro x hx
    rw [← D.face_partition f hf] at hx
    simp only [mem_union, mem_iUnion] at hx
    rcases hx with (⟨h, b, hhb, -⟩ | ⟨j', hj', -⟩) | ⟨j', hj', hx⟩
    · exact absurd hhb (D.handleFace_ne_of_torus hf φ h b)
    · exact absurd hj' (D.arcOwner_ne_of_torus hf φ j')
    · exact huniq j' hj' ▸ hx
  · exact hj ▸ D.loopFace_subset_face j

end DecompositionCertificate

end GC.GraphManifold.Assembly
