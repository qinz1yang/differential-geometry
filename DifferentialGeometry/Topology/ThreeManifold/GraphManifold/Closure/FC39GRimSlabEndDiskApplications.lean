import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimSlabEndDisk
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAxialCoordinateApplications

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the slab end disk

Lane FC39-G-RIMBOX. Every interval component of the edge export has, in the edge slab of its
two-sided axial coordinate, a polar new end disk with the same image as the old one and height equal
to the level exactly on the rim (`EdgeComponentModels.exists_slabPolarEndDisk_GRIM`, `κ = 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsSEDA_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothSEDA_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}}

/-- **The polar new end disk of every interval component.** -/
theorem EdgeComponentModels.exists_slabPolarEndDisk_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) (i : Fin M.intervalCount) :
    ∃ (V : Set P.Base) (hV : IsOpen V) (φ : P.Base → ℝ),
      (∀ t, φ (M.intervalBase i t) = t) ∧
      let _ := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
        (M := W.pieceInterior (edgeSlab_GRIM P V hV))
      ∃ δ : ℝ, 0 < δ ∧ ∃ D : ClosedCell 2 → W.pieceInterior (edgeSlab_GRIM P V hV),
        ContMDiff (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ D ∧ Injective D ∧
        (∀ w, Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) D w)) ∧
        (∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
          P.height (edgeSlabIncl_GRIM P V hV (D w)) =
            P.level + (‖(w : EuclideanSpace ℝ (Fin 2))‖ - 1)) ∧
        ∀ w : ClosedCell 2, P.height (edgeSlabIncl_GRIM P V hV (D w)) = P.level →
          ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  obtain ⟨V, φ, ε, hV, -, hrange, hφ, hφβ, hφinj, hφs, -, -⟩ :=
    M.exists_intervalBase_twoSidedCoordinate_GRIM i
  refine ⟨V, hV, φ, hφβ, ?_⟩
  intro _
  obtain ⟨δ, hδ0, -, D, hD, hDinj, hDimm, -, -, hpol, hrim, -⟩ :=
    edgeSlab_polarEndDisk_GRIM M i hV hφ hφs hφinj hφβ hrange one_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
  refine ⟨δ, hδ0, D, hD, hDinj, hDimm, fun w hw => ?_, hrim⟩
  rw [hpol w hw, one_mul]

end GC.GraphManifold.Assembly.FC39P0
