import DifferentialGeometry.Topology.ThreeManifold.UncappingOrientation
import DifferentialGeometry.Topology.ThreeManifold.UncappingSmoothStructure
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  [ChartedSpace E3 C.UncappingQuotient] [IsManifold (𝓡 3) ∞ C.UncappingQuotient]
  [PreconnectedSpace M.Carrier]

theorem preservesOrientation_uncapping_of_core
    (o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3)
    (D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hcore : ∀ x : T.core, D (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (x : T.core) :
    letI := C.coreCharts
    (𝓡∂ 3).IsInteriorPoint x →
      Orientation.map (Fin 3)
        ((hi ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (N.orientation.orientation (C.coreInclusion x)) =
          o.orientation (C.uncappingInteriorProjection
            ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩) →
      D.preservesOrientation o M.orientation := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  intro hx hproj
  let y : C.uncappingInterior := ⟨C.coreInclusion x,C.coreInclusion_mem_uncappingInterior x⟩
  let A := ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let B := (D.mfderivToContinuousLinearEquiv (by simp) (C.uncappingInteriorProjection y)).toLinearEquiv
  let L := ((C.isLocalDiffeomorphAt_uncappingInteriorMap_core D.toHomeomorph hcore x hx).mfderivToContinuousLinearEquiv
    (by simp)).toLinearEquiv
  have hlin : A.trans B = L := by
    apply LinearEquiv.ext
    intro w
    change mfderiv (𝓡 3) (𝓡 3) D (C.uncappingInteriorProjection y)
      (mfderiv (𝓡 3) (𝓡 3) C.uncappingInteriorProjection y w) =
      mfderiv (𝓡 3) (𝓡 3) (C.uncappingInteriorMap D.toHomeomorph) y w
    exact (mfderiv_comp_apply y (D.mdifferentiable (by simp) _)
      ((hi y).mdifferentiableAt (by simp)) w).symm
  have hor := C.uncappingInteriorMap_orientation_core D.toHomeomorph hcore x hx
  apply Diffeomorph.preservesOrientation_of_eq_at D o M.orientation (C.uncappingInteriorProjection y)
  change Orientation.map (Fin 3) B (o.orientation (C.uncappingInteriorProjection y)) = _
  change Orientation.map (Fin 3) A (N.orientation.orientation (C.coreInclusion x)) = _ at hproj
  erw [← hproj, ← DifferentialGeometry.orientation_map_trans A B, hlin]
  have hpoint : D (C.uncappingInteriorProjection y) = x.val :=
    C.uncappingInteriorMap_core D.toHomeomorph hcore x
  rw [hpoint]
  exact hor

end DifferentialGeometry.Topology.SphericalCapping
