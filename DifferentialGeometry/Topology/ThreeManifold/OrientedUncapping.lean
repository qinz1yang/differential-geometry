import DifferentialGeometry.Topology.ThreeManifold.UncappingInteriorOrientation
import DifferentialGeometry.Topology.ThreeManifold.UncappingSmoothStructure
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

section Orientation

variable [ChartedSpace E3 C.UncappingQuotient] [IsManifold (𝓡 3) ∞ C.UncappingQuotient]

theorem uncappingInteriorProjection_orientation
    (o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3)
    (D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hcore : ∀ x : T.core, D (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (hD : D.preservesOrientation o M.orientation)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection)
    (y : C.uncappingInterior) :
    Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (N.orientation.orientation y.val) = o.orientation (C.uncappingInteriorProjection y) := by
  have hmap : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap D.toHomeomorph) :=
    fun z => (hi z).comp (𝓡 3) M.Carrier (D.isLocalDiffeomorph _)
  let A := ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let B := (D.mfderivToContinuousLinearEquiv (by simp) (C.uncappingInteriorProjection y)).toLinearEquiv
  let L := ((hmap y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hlin : A.trans B = L := by
    apply LinearEquiv.ext
    intro w
    change mfderiv (𝓡 3) (𝓡 3) D (C.uncappingInteriorProjection y)
      (mfderiv (𝓡 3) (𝓡 3) C.uncappingInteriorProjection y w) =
      mfderiv (𝓡 3) (𝓡 3) (C.uncappingInteriorMap D.toHomeomorph) y w
    exact (mfderiv_comp_apply y (D.mdifferentiable (by simp) _)
      ((hi y).mdifferentiableAt (by simp)) w).symm
  change Orientation.map (Fin 3) A (N.orientation.orientation y.val) = _
  apply (Orientation.map (Fin 3) B).injective
  erw [← DifferentialGeometry.orientation_map_trans A B,hlin]
  exact (C.uncappingInteriorMap_preservesOrientation D.toHomeomorph hcore hmap y).trans (hD _).symm

theorem exists_uncapping_orientation
    (D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier)
    (hcore : ∀ x : T.core, D (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection) :
    ∃ o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3,
      D.preservesOrientation o M.orientation ∧
      ∀ y : C.uncappingInterior,
        Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
          (N.orientation.orientation y.val) = o.orientation (C.uncappingInteriorProjection y) := by
  obtain ⟨o,ho⟩ := Manifold.exists_manifoldOrientation_diffeomorph_map D.symm M.orientation
  have hsymm : D.symm.preservesOrientation M.orientation o := by
    intro x
    rw [ho]
    beta_reduce
    change _ = Orientation.map (Fin 3)
      (D.symm.mfderivToContinuousLinearEquiv (by simp) (D (D.symm x))).toLinearEquiv
      (M.orientation.orientation (D (D.symm x)))
    rw [D.apply_symm_apply]
  have hD : D.preservesOrientation o M.orientation := by
    have heq : D.symm.symm = D := by ext q; rfl
    exact heq ▸ Diffeomorph.preservesOrientation_symm hsymm
  exact ⟨o,hD,C.uncappingInteriorProjection_orientation o D hcore hD hi⟩

end Orientation

theorem exists_oriented_uncapping_smooth_structure :
    ∃ charts : ChartedSpace E3 C.UncappingQuotient,
      let _ := charts
      ∃ _ : IsManifold (𝓡 3) ∞ C.UncappingQuotient,
        ∃ o : ManifoldOrientation (𝓡 3) C.UncappingQuotient 3,
          ∃ D : C.UncappingQuotient ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier,
            (∀ x : T.core, D (Quot.mk C.innerCapRelation
              (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
                (C.coreImageHomeomorph x))) = x.val) ∧
            D.preservesOrientation o M.orientation ∧
            ∃ hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.uncappingInteriorProjection,
              (∀ y : C.uncappingInterior,
                Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
                  (N.orientation.orientation y.val) = o.orientation (C.uncappingInteriorProjection y)) ∧
              ∀ (a : T.Index) (z : S2),
                IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (C.uncappingSeam a)
                  (z,(⟨0,by constructor <;> norm_num⟩ : ConnectedSumQuotient.collarInterval)) := by
  obtain ⟨charts,smooth,D,hcore,hi,hs⟩ := C.exists_uncapping_smooth_structure
  let _ := charts
  let _ := smooth
  obtain ⟨o,ho,hproj⟩ := C.exists_uncapping_orientation D hcore hi
  exact ⟨charts,smooth,o,D,hcore,ho,hi,hproj,hs⟩

end DifferentialGeometry.Topology.SphericalCapping
