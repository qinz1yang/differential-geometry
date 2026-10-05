import DifferentialGeometry.Topology.Surface.Recognition.DiskFaceRecognition

/-!
# The embedded face partition of a closed face and its disk count (lane B-BCF134; BCF03 / FC40)

Blueprint `master207B.tex`, BCF03 (B:9834–9884) and review 69 D69-9: BCF03 first outputs the
EMBEDDED face partition of every component `Y` of `∂M₂` — `Y = A_Y ∪ B_Y` with `A_Y` a finite
disjoint union of whole horizontal disks and `B_Y` a compact circle-bundle surface meeting each disk
in its whole boundary circle — and only THEN applies FC40 for the counts.

`EmbeddedFacePartition_BCF Y` records exactly the data FC40a / FC40b consume (generic, no geometry):
finitely many closed disks `disk i` and closed nonempty circle-bundle pieces `piece j` covering `Y`,
pairwise disjoint within each family, the side map (a disk meets only its own piece), the degree
condition (each piece carries `0` or `2` disks), disk parametrizations whose boundary circle is the
whole intersection with the side piece, annulus parametrizations of the pieces with two disks, and
an open projection to the circle for the pieces without disks.

* `EmbeddedFacePartition_BCF.diskCount_eq_two_of_sphere`: a sphere face has exactly two disks;
* `EmbeddedFacePartition_BCF.diskCount_eq_zero_of_torus`: a torus face has none;
* `EmbeddedFacePartition_BCF.pieceCount_eq_one`: a connected face has exactly one piece;
* `EmbeddedFacePartition_BCF.exists_piece_eq_univ_of_torus`: a torus face IS one whole
  circle-bundle piece (the cusp branch of BCF03: `H_b` lies in the circle remainder, no disk).
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

/-- **The embedded face partition of a face `Y`** (BCF03.a, the FC40 input): `diskCount` closed
disks and `pieceCount` closed nonempty circle-bundle pieces covering `Y`, with side map, degree
condition, disk / annulus parametrizations and the open circle projection of a disk-free piece. -/
structure EmbeddedFacePartition_BCF (Y : Type*) [TopologicalSpace Y] where
  /-- The number of horizontal disks. -/
  diskCount : ℕ
  /-- The number of circle-bundle pieces. -/
  pieceCount : ℕ
  /-- The horizontal disks `A_Y = ⋃ disk i`. -/
  disk : Fin diskCount → Set Y
  /-- The circle-bundle pieces `B_Y = ⋃ piece j`. -/
  piece : Fin pieceCount → Set Y
  /-- The piece carrying the boundary circle of a disk. -/
  side : Fin diskCount → Fin pieceCount
  isClosed_disk : ∀ i, IsClosed (disk i)
  isClosed_piece : ∀ j, IsClosed (piece j)
  piece_nonempty : ∀ j, (piece j).Nonempty
  cover : (⋃ i, disk i) ∪ (⋃ j, piece j) = univ
  disk_disjoint : Pairwise (Disjoint on disk)
  piece_disjoint : Pairwise (Disjoint on piece)
  /-- A disk meets only its side piece. -/
  side_spec : ∀ i j, (disk i ∩ piece j).Nonempty → side i = j
  /-- Every piece carries `0` (base a circle) or `2` (base an interval) disks. -/
  degree : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 ∨
    (Finset.univ.filter (fun i => side i = j)).card = 2
  /-- Each disk is a parametrized closed disk whose boundary circle is its whole intersection with
  its side piece (the common circle is a whole fibre). -/
  disk_param : ∀ i, ∃ h : Disk 2 → Y, Continuous h ∧ Injective h ∧ range h = disk i ∧
    h '' diskSphere 2 = disk i ∩ piece (side i)
  /-- A piece with two disks is an annulus whose two end circles are the disk circles. -/
  annulus_param : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 2 →
    ∃ e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y, Continuous e ∧
      Injective e ∧ range e = piece j ∧ ∀ i, side i = j →
        disk i ∩ piece j = e '' {q | (q.2 : ℝ) = 0} ∨ disk i ∩ piece j = e '' {q | (q.2 : ℝ) = 1}
  /-- A piece without disks is a circle bundle over a circle: an open continuous projection. -/
  circle_base : ∀ j, (Finset.univ.filter (fun i => side i = j)).card = 0 →
    ∃ p : piece j → Circle, Continuous p ∧ IsOpenMap p

namespace EmbeddedFacePartition_BCF

variable {Y : Type*} [TopologicalSpace Y] (P : EmbeddedFacePartition_BCF Y)

/-- **FC40a**: a connected face has exactly one piece and `0` or `2` disks. -/
theorem pieceCount_eq_one_and_diskCount [ConnectedSpace Y] :
    P.pieceCount = 1 ∧ (P.diskCount = 0 ∨ P.diskCount = 2) := by
  have h := disk_face_count_dichotomy P.disk P.piece P.isClosed_disk P.isClosed_piece
    P.piece_nonempty P.cover P.disk_disjoint P.piece_disjoint P.side P.side_spec P.degree
  simpa only [Fintype.card_fin] using h

/-- A connected face has exactly one circle-bundle piece. -/
theorem pieceCount_eq_one [ConnectedSpace Y] : P.pieceCount = 1 :=
  P.pieceCount_eq_one_and_diskCount.1

/-- **FC40, sphere face**: exactly two disks. -/
theorem diskCount_eq_two_of_sphere (φ : Y ≃ₜ SphereTwo) : P.diskCount = 2 := by
  have h := disk_face_count_sphereTwo φ P.disk P.piece P.isClosed_disk P.isClosed_piece
    P.piece_nonempty P.cover P.disk_disjoint P.piece_disjoint P.side P.side_spec P.degree
    P.circle_base
  simpa only [Fintype.card_fin] using h.2

/-- **FC40, torus face**: no disk. -/
theorem diskCount_eq_zero_of_torus (φ : Y ≃ₜ Circle × Circle) : P.diskCount = 0 := by
  have h := disk_face_count_torus φ P.disk P.piece P.isClosed_disk P.isClosed_piece
    P.piece_nonempty P.cover P.disk_disjoint P.piece_disjoint P.side P.side_spec P.degree
    P.disk_param P.annulus_param
  simpa only [Fintype.card_fin] using h.2

/-- **A face without disks is one whole circle-bundle piece.** -/
theorem exists_piece_eq_univ_of_diskCount_eq_zero [ConnectedSpace Y] (h0 : P.diskCount = 0) :
    ∃ j, P.piece j = univ := by
  have h1 := P.pieceCount_eq_one
  refine ⟨⟨0, by omega⟩, eq_univ_of_forall fun y => ?_⟩
  have hy : y ∈ (⋃ i, P.disk i) ∪ (⋃ j, P.piece j) := P.cover ▸ mem_univ y
  rcases hy with hy | hy
  · obtain ⟨i, -⟩ := mem_iUnion.mp hy
    exact (Fin.elim0 (h0 ▸ i))
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by have := j.2; omega)
    exact hj0 ▸ hj

/-- **The cusp branch of BCF03**: a torus face is one whole circle-bundle piece (no horizontal
disk). -/
theorem exists_piece_eq_univ_of_torus (φ : Y ≃ₜ Circle × Circle) : ∃ j, P.piece j = univ := by
  have : ConnectedSpace Y := φ.symm.surjective.connectedSpace φ.symm.continuous
  exact P.exists_piece_eq_univ_of_diskCount_eq_zero (P.diskCount_eq_zero_of_torus φ)

end EmbeddedFacePartition_BCF

end DifferentialGeometry.Topology.Surface
