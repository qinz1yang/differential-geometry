import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.CutCap

/-!
Geometric cyclic assemblies of actual balls along disjoint embedded disk faces.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

local instance diskFaceCharts : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1

local instance diskFaceSmooth : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) := Handle.closedCellIsManifold 1

local instance diskBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance diskBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

structure CyclicDiskAssembly (W : CompactCarrier.{u}) where
  count : ℕ
  count_pos : 0 < count
  next : Fin count ≃ Fin count
  cyclic : ∀ i j, ∃ r : ℕ, (next : Fin count → Fin count)^[r] i = j
  ball : Fin count → CompactCarrier.{u}
  ballModel : ∀ i, (ball i).Carrier ≃ₘ⟮(ball i).model, 𝓡∂ 3⟯ ClosedCell 3
  face : ∀ i, Bool → C(ClosedCell 2, (ball i).Carrier)
  face_embedding : ∀ i b, IsSmoothEmbedding (𝓡∂ 2) (ball i).model ∞ (face i b)
  face_boundary : ∀ i b z, (ball i).model.IsBoundaryPoint (face i b z)
  face_disjoint : ∀ i, Disjoint (range (face i false)) (range (face i true))
  matching : Fin count → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
  diskCollar : ∀ i, Bool → PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (ball i).model
    (EuclideanSpace ℝ (Fin 2) × EuclideanHalfSpace 1) (ball i).Carrier ∞
  diskCollar_source : ∀ i b, (diskCollar i b).source =
    Metric.ball 0 1 ×ˢ {h | h.val 0 < 1}
  diskCollar_zero : ∀ i b z (hz : ‖z‖ < 1), diskCollar i b (z, halfZero) =
    face i b ⟨z, hz.le⟩
  map : ∀ i, C((ball i).Carrier, W.Carrier)
  map_smooth : ∀ i, ContMDiff (ball i).model W.model ∞ (map i)
  map_mfderiv_bijective : ∀ i x, Bijective (mfderiv (ball i).model W.model (map i) x)
  map_positive : ∀ i x,
    Orientation.map (Fin 3)
      (LinearEquiv.ofBijective (mfderiv (ball i).model W.model (map i) x).toLinearMap
        (map_mfderiv_bijective i x)) ((ball i).orientation.orientation x) =
      W.orientation.orientation (map i x)
  face_eq : ∀ i z, map i (face i true z) =
    map (next i) (face (next i) false (matching i z))
  diskSeam : Fin count → PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) W.model
    (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞
  diskSeam_source : ∀ i, (diskSeam i).source = Metric.ball 0 1 ×ˢ Ioo (-1 : ℝ) 1
  diskSeam_negative : ∀ i z, ‖z‖ < 1 → ∀ s (hs : s ≤ 0), -1 < s →
    diskSeam i (z, s) = map i (diskCollar i true (z, halfPoint (-s) (neg_nonneg.2 hs)))
  diskSeam_positive : ∀ i z (hz : ‖z‖ < 1) s (hs : 0 ≤ s), s < 1 →
    diskSeam i (z, s) = map (next i) (diskCollar (next i) false
      ((matching i ⟨z, hz.le⟩).val, halfPoint s hs))
  covers : ⋃ i, range (map i) = univ
  overlap : ∀ i j x y, map i x = map j y →
    (⟨i, x⟩ : Σ i, (ball i).Carrier) = ⟨j, y⟩ ∨
      (∃ z, j = next i ∧ x = face i true z ∧ y = face j false (matching i z)) ∨
      ∃ z, i = next j ∧ y = face j true z ∧ x = face i false (matching j z)
  external : BoundaryTori W 1
  boundary_exhausted : W.model.boundary W.Carrier = external.image

namespace CyclicDiskAssembly

variable {W : CompactCarrier.{u}} (A : CyclicDiskAssembly W)

def fold (x : Σ i, (A.ball i).Carrier) : W.Carrier := A.map x.1 x.2

theorem fold_surjective : Surjective A.fold := by
  intro x
  have hx : x ∈ ⋃ i, range (A.map i) := A.covers ▸ mem_univ x
  obtain ⟨i, y, hy⟩ := mem_iUnion.mp hx
  exact ⟨⟨i, y⟩, hy⟩

theorem fold_face (i : Fin A.count) (z : ClosedCell 2) :
    A.fold ⟨i, A.face i true z⟩ =
      A.fold ⟨A.next i, A.face (A.next i) false (A.matching i z)⟩ := A.face_eq i z

def boundaryCertificate : MixedBoundaryCertificate W :=
  MixedBoundaryCertificate.ofTori A.external A.boundary_exhausted

end CyclicDiskAssembly

end GC.GraphManifold
