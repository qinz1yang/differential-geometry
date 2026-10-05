import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.OldPortCollar

/-!
# Chapter-14 assembly, item L1: the certificate produces `rim_quadrant`

Erratum E-L1 adds the field `BallHandleCycle.rim_quadrant` (the open quadrant `{0 < x, 0 < y}` of a
rim chart meets no ball and no handle). This file derives it from the FC39 certificate as built by
lane ASM-CERT (`AssemblyCertificate.lean`), with no new certificate clause:

* `rim_region` puts the image of the open quadrant inside `circ.region`; the image is open, so it
  lies in `interior circ.region`;
* a vertex image and a handle image are images of manifolds (with boundary or corners) under maps with
  bijective differential, so a point of such an image in an open set `O` gives a point of `O` in the
  ambient INTERIOR of the image (`exists_mem_inter_interior_range`: density of manifold interior
  points, Mathlib's `isInteriorPoint_of_surjective_mfderiv`, and the local inverse function theorem
  `GC.Seifert.image_mem_nhds_of_mfderiv_injective`);
* `circ_vertex_disjoint` and `circ_handle_disjoint` then exclude it.

`DecompositionCertificate.rim_quadrant` is the field in the shape of `BallHandleCycle` for any
choice of the cycle's balls (vertices) and handles.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1P : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1P : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- A point of the image of a map with bijective differential that lies in an open set `O` gives a
point of `O` in the ambient interior of the image. -/
theorem exists_mem_inter_interior_range {E' H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H] {I : ModelWithCorners ℝ E' H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hdim : Module.finrank ℝ E' = 3) {W : CompactCarrier.{u}} {f : M → W.Carrier}
    (hf : ContMDiff I W.model ∞ f) (hbij : ∀ q, Bijective (mfderiv I W.model f q))
    {O : Set W.Carrier} (hO : IsOpen O) {x : M} (hx : f x ∈ O) :
    (O ∩ interior (range f)).Nonempty := by
  have hU : IsOpen (f ⁻¹' O) := hO.preimage hf.continuous
  obtain ⟨y, hyU, hyint⟩ :=
    (ModelWithCorners.dense_interior I (M := M)).inter_open_nonempty _ hU ⟨x, hx⟩
  have hint : W.model.IsInteriorPoint (f y) :=
    (hf.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv (hbij y).2 hyint
  have hdim' : Module.finrank ℝ E' = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [hdim, finrank_euclideanSpace_fin]
  have hnhds := GC.Seifert.image_mem_nhds_of_mfderiv_injective hf hyint hint (hbij y).1 hdim'
    Filter.univ_mem
  rw [image_univ] at hnhds
  exact ⟨f y, hyU, mem_interior_iff_mem_nhds.mpr hnhds⟩

/-- The image of a vertex is the range of its piece map. -/
theorem Vertex.image_eq_range_piece {W : CompactCarrier.{u}} (v : Vertex W) :
    v.image = range v.piece.map := by
  cases v <;> rfl

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The image of the open quadrant of a rim chart. -/
def rimQuadrant (h : Fin D.handleCount) (b : Bool) : Set W.Carrier :=
  D.rimChart h b '' {p | p ∈ (D.rimChart h b).source ∧ 0 < p.2.1 ∧ 0 < p.2.2}

theorem isOpen_rimQuadrant (h : Fin D.handleCount) (b : Bool) : IsOpen (D.rimQuadrant h b) := by
  apply (D.rimChart h b).toOpenPartialHomeomorph.isOpen_image_of_subset_source _
    (fun p hp => hp.1)
  exact (D.rimChart h b).open_source.inter
    ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)))

theorem rimQuadrant_subset_interior_region (h : Fin D.handleCount) (b : Bool) :
    D.rimQuadrant h b ⊆ interior D.circ.region := by
  apply interior_maximal _ (D.isOpen_rimQuadrant h b)
  rintro z ⟨p, ⟨hp, hx, hy⟩, rfl⟩
  exact (D.rim_region h b hp).mpr ⟨hx.le, hy.le⟩

theorem rimQuadrant_disjoint_vertex (h : Fin D.handleCount) (b : Bool) (k : Fin D.vertexCount) :
    Disjoint (D.rimQuadrant h b) (D.vertex k).image := by
  rw [Set.disjoint_left]
  intro z hzO hzV
  rw [Vertex.image_eq_range_piece] at hzV
  obtain ⟨x, rfl⟩ := hzV
  obtain ⟨w, hwO, hwV⟩ := exists_mem_inter_interior_range (I := 𝓡∂ 3) finrank_euclideanSpace_fin
    (D.vertex k).piece.smooth (D.vertex k).piece.mfderiv_bijective (D.isOpen_rimQuadrant h b) hzO
  rw [← Vertex.image_eq_range_piece] at hwV
  exact Set.disjoint_left.mp (D.circ_vertex_disjoint k)
    (D.rimQuadrant_subset_interior_region h b hwO) hwV

theorem rimQuadrant_disjoint_handle (h : Fin D.handleCount) (b : Bool) (h' : Fin D.handleCount) :
    Disjoint (D.rimQuadrant h b) (range (D.handle h').map) := by
  rw [Set.disjoint_left]
  rintro z hzO ⟨x, rfl⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  obtain ⟨w, hwO, hwH⟩ := exists_mem_inter_interior_range (I := (𝓡∂ 2).prod (𝓡∂ 1)) hdim
    (D.handle h').smooth (D.handle h').mfderiv_bijective (D.isOpen_rimQuadrant h b) hzO
  exact Set.disjoint_left.mp (D.circ_handle_disjoint h')
    (D.rimQuadrant_subset_interior_region h b hwO) hwH

/-- **The producer of `rim_quadrant`.** For any choice of the cycle's balls (vertices) and handles,
the open quadrant of every certificate rim chart meets none of them. -/
theorem rim_quadrant {len : ℕ} (ballIdx : Fin len → Fin D.vertexCount)
    (handleIdx : Fin len → Fin D.handleCount) (h : Fin D.handleCount) (b : Bool)
    (p : Circle × (ℝ × ℝ)) (hp : p ∈ (D.rimChart h b).source) (hx : 0 < p.2.1) (hy : 0 < p.2.2) :
    D.rimChart h b p ∉
      (⋃ j, range (D.vertex (ballIdx j)).piece.map) ∪ ⋃ j, range (D.handle (handleIdx j)).map := by
  have hO : D.rimChart h b p ∈ D.rimQuadrant h b := ⟨p, ⟨hp, hx, hy⟩, rfl⟩
  rintro (hz | hz)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    rw [← Vertex.image_eq_range_piece] at hj
    exact Set.disjoint_left.mp (D.rimQuadrant_disjoint_vertex h b (ballIdx j)) hO hj
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (D.rimQuadrant_disjoint_handle h b (handleIdx j)) hO hj

end DecompositionCertificate

end GC.GraphManifold.Assembly
