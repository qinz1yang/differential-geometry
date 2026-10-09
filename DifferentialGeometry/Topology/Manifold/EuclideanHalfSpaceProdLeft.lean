import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

def euclideanHalfSpaceProdLeftCoordinates (n m : ℕ) :
    (EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1 + m)) :=
  EuclideanSpace.finAddEquivProd.symm

@[simp] theorem euclideanHalfSpaceProdLeftCoordinates_zero (n m : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin m)) :
    euclideanHalfSpaceProdLeftCoordinates n m x 0 = x.1 0 := by
  rfl

def euclideanHalfSpaceProdLeftHomeomorph (n m : ℕ) :
    ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m)) ≃ₜ
      EuclideanHalfSpace (n + 1 + m) where
  toFun x := ⟨euclideanHalfSpaceProdLeftCoordinates n m (((𝓡∂ (n + 1)).prod (𝓡 m)) x), by
    rw [euclideanHalfSpaceProdLeftCoordinates_zero]
    exact x.1.2⟩
  invFun y :=
    (⟨((euclideanHalfSpaceProdLeftCoordinates n m).symm y.1).1, by
      rw [← euclideanHalfSpaceProdLeftCoordinates_zero n m
        ((euclideanHalfSpaceProdLeftCoordinates n m).symm y.1),
        ContinuousLinearEquiv.apply_symm_apply]
      exact y.2⟩, ((euclideanHalfSpaceProdLeftCoordinates n m).symm y.1).2)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change ((euclideanHalfSpaceProdLeftCoordinates n m).symm
        (euclideanHalfSpaceProdLeftCoordinates n m (x.1.val, x.2))).1 = x.1.val
      exact congrArg Prod.fst
        ((euclideanHalfSpaceProdLeftCoordinates n m).symm_apply_apply (x.1.val, x.2))
    · change ((euclideanHalfSpaceProdLeftCoordinates n m).symm
        (euclideanHalfSpaceProdLeftCoordinates n m (x.1.val, x.2))).2 = x.2
      exact congrArg Prod.snd
        ((euclideanHalfSpaceProdLeftCoordinates n m).symm_apply_apply (x.1.val, x.2))
  right_inv y := by
    apply Subtype.ext
    exact (euclideanHalfSpaceProdLeftCoordinates n m).apply_symm_apply y.1
  continuous_toFun :=
    (((euclideanHalfSpaceProdLeftCoordinates n m).continuous.comp
      ((𝓡∂ (n + 1)).prod (𝓡 m)).continuous)).subtype_mk _
  continuous_invFun := by
    have h : Continuous fun y : EuclideanHalfSpace (n + 1 + m) =>
        (euclideanHalfSpaceProdLeftCoordinates n m).symm y.val :=
      (euclideanHalfSpaceProdLeftCoordinates n m).symm.continuous.comp continuous_subtype_val
    exact (h.fst.subtype_mk _).prodMk h.snd

theorem euclideanHalfSpaceProdLeftHomeomorph_model (n m : ℕ)
    (x : ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m))) :
    (𝓡∂ (n + 1 + m)) (euclideanHalfSpaceProdLeftHomeomorph n m x) =
      euclideanHalfSpaceProdLeftCoordinates n m (((𝓡∂ (n + 1)).prod (𝓡 m)) x) := rfl

@[instance_reducible]
def euclideanHalfSpaceProdLeftChartedSpace (n m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m))) M] :
    ChartedSpace (EuclideanHalfSpace (n + 1 + m)) M :=
  chartedSpaceTransHomeomorph (M := M) (euclideanHalfSpaceProdLeftHomeomorph n m)

theorem euclideanHalfSpaceProdLeft_isManifold (n m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m))) M]
    [IsManifold ((𝓡∂ (n + 1)).prod (𝓡 m)) ∞ M] :
    letI := euclideanHalfSpaceProdLeftChartedSpace n m M
    IsManifold (𝓡∂ (n + 1 + m)) ∞ M :=
  isManifold_transHomeomorph ((𝓡∂ (n + 1)).prod (𝓡 m)) (𝓡∂ (n + 1 + m))
    (euclideanHalfSpaceProdLeftHomeomorph n m) (euclideanHalfSpaceProdLeftCoordinates n m)
    (euclideanHalfSpaceProdLeftHomeomorph_model n m)

theorem euclideanHalfSpaceProdLeft_boundary (n m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m))) M] :
    letI := euclideanHalfSpaceProdLeftChartedSpace n m M
    (𝓡∂ (n + 1 + m)).boundary M = ((𝓡∂ (n + 1)).prod (𝓡 m)).boundary M :=
  boundary_transHomeomorph ((𝓡∂ (n + 1)).prod (𝓡 m)) (𝓡∂ (n + 1 + m))
    (euclideanHalfSpaceProdLeftHomeomorph n m) (euclideanHalfSpaceProdLeftCoordinates n m)
    (euclideanHalfSpaceProdLeftHomeomorph_model n m)

theorem euclideanHalfSpaceProdLeft_isInteriorPoint_iff (n m : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanHalfSpace (n + 1)) (EuclideanSpace ℝ (Fin m))) M]
    (x : M) :
    letI := euclideanHalfSpaceProdLeftChartedSpace n m M
    (𝓡∂ (n + 1 + m)).IsInteriorPoint x ↔
      ((𝓡∂ (n + 1)).prod (𝓡 m)).IsInteriorPoint x :=
  isInteriorPoint_transHomeomorph_iff ((𝓡∂ (n + 1)).prod (𝓡 m)) (𝓡∂ (n + 1 + m))
    (euclideanHalfSpaceProdLeftHomeomorph n m) (euclideanHalfSpaceProdLeftCoordinates n m)
    (euclideanHalfSpaceProdLeftHomeomorph_model n m) x

end DifferentialGeometry.Manifold
