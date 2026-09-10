import DifferentialGeometry.Topology.ProjectiveSpace.DiskCharacteristicMap
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

set_option autoImplicit false

noncomputable section

open Metric Topology CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.ProjectiveSpace

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]


def diskBoundaryInclusion : TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (closedBall (0 : E) 1) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, sphere_subset_closedBall x.prop⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [NormedSpace ℝ E] in
theorem isClosedEmbedding_diskBoundaryInclusion : IsClosedEmbedding (diskBoundaryInclusion E) :=
  IsClosedEmbedding.inclusion sphere_subset_closedBall
    (isClosed_sphere.preimage continuous_subtype_val)


def diskAttachingMap : TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (Projectivization ℝ E) :=
  TopCat.ofHom ⟨sphereProjection, continuous_sphereProjection⟩


def diskCellMap : TopCat.of (closedBall (0 : E) 1) ⟶ TopCat.of (Projectivization ℝ (E × ℝ)) :=
  TopCat.ofHom ⟨diskCharacteristicMap, continuous_diskCharacteristicMap⟩


def projectiveCoordinateInclusion :
    TopCat.of (Projectivization ℝ E) ⟶ TopCat.of (Projectivization ℝ (E × ℝ)) :=
  TopCat.ofHom ⟨coordinateInclusion, continuous_coordinateInclusion⟩


@[reassoc (attr := simp)]
theorem diskAttachingMap_comm :
    diskBoundaryInclusion E ≫ diskCellMap E =
      diskAttachingMap E ≫ projectiveCoordinateInclusion E := by
  ext x
  exact diskCharacteristicMap_sphere x

theorem diskAttachment_isPushout [FiniteDimensional ℝ E] :
    IsPushout (diskBoundaryInclusion E) (diskAttachingMap E)
      (diskCellMap E) (projectiveCoordinateInclusion E) := by
  refine ⟨⟨diskAttachingMap_comm E⟩, ⟨?_⟩⟩
  apply PushoutCocone.isColimitAux'
  intro s
  have hfactor : Function.FactorsThrough s.inl.hom (diskCellMap E).hom := by
    intro x y hxy
    rcases (diskCharacteristicMap_eq_iff x y).mp hxy with h | ⟨hx, hxy⟩
    · exact congrArg s.inl h
    · have hy : ‖(y : E)‖ = 1 := by simpa [hxy] using hx
      let sx : sphere (0 : E) 1 := ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
      let sy : sphere (0 : E) 1 := ⟨y.val, mem_sphere_zero_iff_norm.mpr hy⟩
      have he : sphereProjection sx = sphereProjection sy :=
        (sphereProjection_eq_iff sx sy).mpr (Or.inr (Subtype.ext hxy))
      have hsx := ConcreteCategory.congr_hom s.condition sx
      have hsy := ConcreteCategory.congr_hom s.condition sy
      change s.inl x = s.inr (sphereProjection sx) at hsx
      change s.inl y = s.inr (sphereProjection sy) at hsy
      exact hsx.trans ((congrArg s.inr he).trans hsy.symm)
  let q : IsQuotientMap (diskCellMap E).hom := isQuotientMap_diskCharacteristicMap
  let l := TopCat.ofHom (q.lift s.inl.hom hfactor)
  have hl : diskCellMap E ≫ l = s.inl := by
    ext x
    exact ContinuousMap.congr_fun (q.lift_comp s.inl.hom hfactor) x
  refine ⟨l, hl, ?_, ?_⟩
  · ext p
    obtain ⟨x, rfl⟩ := sphereProjection_surjective p
    have h := ConcreteCategory.congr_hom hl (diskBoundaryInclusion E x)
    have hs := ConcreteCategory.congr_hom s.condition x
    change l (diskCharacteristicMap (diskBoundaryInclusion E x)) =
      s.inl (diskBoundaryInclusion E x) at h
    change s.inl (diskBoundaryInclusion E x) = s.inr (sphereProjection x) at hs
    exact (congrArg l (diskCharacteristicMap_sphere x).symm).trans (h.trans hs)
  · intro m hm _
    ext p
    obtain ⟨x, rfl⟩ := diskCharacteristicMap_surjective p
    exact (ConcreteCategory.congr_hom hm x).trans (ConcreteCategory.congr_hom hl x).symm

end DifferentialGeometry.ProjectiveSpace
