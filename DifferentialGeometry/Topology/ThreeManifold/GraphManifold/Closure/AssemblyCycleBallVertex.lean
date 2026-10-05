import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Surface.Recognition.CircleOpenMap

/-!
# FC42: ball vertices (shared predicate)

`Vertex.IsBall v`: the vertex `v` of the FC39 certificate is a zero vertex with the ball model
`ZeroModel.ball`. Shared by the FC42 lanes (the cycle partition H2 of lane ASM-CYC3 and the count
`badVertexCount` of lane ASM-CYC2: a vertex is bad if it is not a ball and owns a partitioned
sphere face). Basic facts: the introduction rule, the other vertex kinds are not balls, and the
image of a ball vertex is the range of its piece.

Also here, for the same lanes: **a two-sphere is not a torus**
(`false_of_homeomorph_sphereTwo_of_homeomorph_torus`, from the tree's
`not_isOpenMap_circle_of_homeomorph_sphereTwo`: the sphere has no continuous open map to the
circle), the image of a continuous injective torus is a torus (`homeomorphRangeOfTorus`), and the
model boundary image of a ball vertex is a two-sphere (`Vertex.IsBall.nonempty_boundaryImage_homeomorph_sphereTwo`:
`∂ ClosedCell 3` is the unit sphere, diffeomorphisms preserve the boundary, the piece map is a
closed embedding), hence nonempty and connected.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-- A vertex is a ball: a zero vertex with the ball model. -/
def Vertex.IsBall {W : CompactCarrier.{u}} (v : Vertex W) : Prop :=
  ∃ (P : PieceEmbedding W) (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3), v = .zero P (.ball e)

namespace Vertex

variable {W : CompactCarrier.{u}}

theorem isBall_zero_ball (P : PieceEmbedding W) (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    (Vertex.zero P (.ball e)).IsBall :=
  ⟨P, e, rfl⟩

theorem not_isBall_closedZero (C : ClosedZeroPiece W) : ¬ (Vertex.closedZero C).IsBall := by
  rintro ⟨P, e, h⟩
  cases h

theorem not_isBall_slim (P : PieceEmbedding W) (m : SlimModel P) : ¬ (Vertex.slim P m).IsBall := by
  rintro ⟨P', e, h⟩
  cases h

theorem not_isBall_cuspCore (P : PieceEmbedding W)
    (e : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece) :
    ¬ (Vertex.cuspCore P e).IsBall := by
  rintro ⟨P', e', h⟩
  cases h

/-- The piece of a ball vertex. -/
def IsBall.piece {v : Vertex W} (h : v.IsBall) : PieceEmbedding W :=
  h.choose

/-- The ball model of a ball vertex. -/
def IsBall.model {v : Vertex W} (h : v.IsBall) : h.piece.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  h.choose_spec.choose

theorem IsBall.eq {v : Vertex W} (h : v.IsBall) : v = .zero h.piece (.ball h.model) :=
  h.choose_spec.choose_spec

theorem IsBall.piece_eq {v : Vertex W} (h : v.IsBall) : v.piece = h.piece :=
  congrArg Vertex.piece h.eq

theorem IsBall.image_eq {v : Vertex W} (h : v.IsBall) : v.image = range h.piece.map :=
  congrArg Vertex.image h.eq

theorem IsBall.boundaryImage_eq {v : Vertex W} (h : v.IsBall) :
    v.boundaryImage = h.piece.map '' (𝓡∂ 3).boundary h.piece.Piece :=
  congrArg Vertex.boundaryImage h.eq

end Vertex

/-! ## A two-sphere is not a torus; the boundary of a ball vertex is a two-sphere -/

/-- **A space homeomorphic to the two-sphere is not homeomorphic to the torus.** -/
theorem false_of_homeomorph_sphereTwo_of_homeomorph_torus {X : Type*} [TopologicalSpace X]
    (φ : X ≃ₜ SphereTwo) (ψ : X ≃ₜ Circle × Circle) : False :=
  DifferentialGeometry.Topology.Surface.not_isOpenMap_circle_of_homeomorph_sphereTwo φ
    (continuous_fst.comp ψ.continuous) (isOpenMap_fst.comp ψ.isOpenMap)

/-- The image of a continuous injective map from the torus into a Hausdorff space is a torus. -/
def homeomorphRangeOfTorus {Y : Type*} [TopologicalSpace Y] [T2Space Y] {g : Circle × Circle → Y}
    (hg : Continuous g) (hinj : Injective g) : range g ≃ₜ Circle × Circle :=
  ((hg.isClosedEmbedding hinj).isEmbedding.toHomeomorph).symm

/-- A ball piece: the image of its model boundary is the image of the unit sphere. -/
theorem image_boundary_eq_range_of_ball {W : CompactCarrier.{u}} (P : PieceEmbedding W)
    (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    P.map '' (𝓡∂ 3).boundary P.Piece =
      range fun z : SphereTwo =>
        P.map (e.symm ⟨z.1, le_of_eq (mem_sphere_zero_iff_norm.mp z.2)⟩) := by
  have hS : ∀ x : ClosedCell 3, (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.1‖ = 1 := fun x =>
    Set.ext_iff.mp (DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2) x
  have hbd : ∀ q : P.Piece, q ∈ (𝓡∂ 3).boundary P.Piece ↔ ‖(e q).1‖ = 1 := fun q =>
    ((e.isLocalDiffeomorph q).isBoundaryPoint_iff (by simp)).trans (hS (e q))
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨(e q).1, mem_sphere_zero_iff_norm.mpr ((hbd q).mp hq)⟩, ?_⟩
    change P.map (e.symm ⟨(e q).1, _⟩) = P.map q
    rw [show (⟨(e q).1, _⟩ : ClosedCell 3) = e q from rfl, Diffeomorph.symm_apply_apply]
  · rintro ⟨z, rfl⟩
    refine ⟨_, (hbd _).mpr ?_, rfl⟩
    rw [Diffeomorph.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp z.2

namespace Vertex

variable {W : CompactCarrier.{u}}

/-- **The model boundary image of a ball vertex is a two-sphere.** -/
theorem IsBall.nonempty_boundaryImage_homeomorph_sphereTwo {v : Vertex W} (hv : v.IsBall) :
    Nonempty (v.boundaryImage ≃ₜ SphereTwo) := by
  obtain ⟨P, e, rfl⟩ := hv
  let g : SphereTwo → W.Carrier := fun z =>
    P.map (e.symm ⟨z.1, le_of_eq (mem_sphere_zero_iff_norm.mp z.2)⟩)
  have hg : Continuous g :=
    P.continuous_map.comp (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hinj : Injective g := by
    intro z z' h
    have h1 := e.symm.injective (P.injective h)
    exact Subtype.ext (congrArg (fun w : ClosedCell 3 => w.1) h1)
  have hrange : (Vertex.zero P (.ball e)).boundaryImage = range g :=
    image_boundary_eq_range_of_ball P e
  rw [hrange]
  exact ⟨((hg.isClosedEmbedding hinj).isEmbedding.toHomeomorph).symm⟩

theorem IsBall.boundaryImage_nonempty {v : Vertex W} (hv : v.IsBall) : v.boundaryImage.Nonempty := by
  obtain ⟨φ⟩ := hv.nonempty_boundaryImage_homeomorph_sphereTwo
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3)))
    (r := 1)).mpr zero_le_one
  exact ⟨(φ.symm ⟨x, hx⟩).1, (φ.symm ⟨x, hx⟩).2⟩

theorem IsBall.isConnected_boundaryImage {v : Vertex W} (hv : v.IsBall) :
    IsConnected v.boundaryImage := by
  obtain ⟨φ⟩ := hv.nonempty_boundaryImage_homeomorph_sphereTwo
  have h2 := (isConnected_univ (α := SphereTwo)).image _
    (continuous_subtype_val.comp φ.symm.continuous).continuousOn
  rwa [image_univ, range_comp, φ.symm.range_coe, image_univ, Subtype.range_coe] at h2

/-- The model boundary image of a ball vertex is not a torus. -/
theorem IsBall.false_of_homeomorph_torus {v : Vertex W} (hv : v.IsBall) {S : Set W.Carrier}
    (hS : S = v.boundaryImage) (ψ : S ≃ₜ Circle × Circle) : False := by
  obtain ⟨φ⟩ := hv.nonempty_boundaryImage_homeomorph_sphereTwo
  exact false_of_homeomorph_sphereTwo_of_homeomorph_torus ((Homeomorph.setCongr hS).trans φ) ψ

end Vertex

end GC.GraphManifold.Assembly
