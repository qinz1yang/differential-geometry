import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

private abbrev ProdSpace := EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)

private abbrev ProdModel := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

private def prodCoordinatesLinearEquiv : ProdSpace ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (LinearEquiv.prodCongr (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv
      (EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv).trans <|
    (LinearEquiv.prodComm ℝ _ _).trans <|
      (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 2) ℝ ℝ).symm.trans <|
        (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 1 ⊕ Fin 2 => ℝ)
          (finSumFinEquiv (m := 1) (n := 2))).trans <|
          (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.symm

def euclideanHalfSpaceProdCoordinates : ProdSpace ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.toContinuousLinearEquiv prodCoordinatesLinearEquiv

private theorem coordinates_apply_aux (p : ProdSpace) (i : Fin 3) :
    euclideanHalfSpaceProdCoordinates p i =
      (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 2) ℝ ℝ).symm
        (p.2.ofLp, p.1.ofLp) ((finSumFinEquiv (m := 1) (n := 2)).symm i) := by
  simp only [euclideanHalfSpaceProdCoordinates]
  rw [LinearEquiv.coe_toContinuousLinearEquiv']
  simp only [prodCoordinatesLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.prodComm_apply, LinearEquiv.piCongrLeft'_apply, EuclideanSpace.equiv,
    Prod.swap_prod_mk,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp]

@[simp]
theorem euclideanHalfSpaceProdCoordinates_apply_zero (p : ProdSpace) :
    euclideanHalfSpaceProdCoordinates p 0 = p.2 0 := by
  rw [coordinates_apply_aux p 0, show (finSumFinEquiv (m := 1) (n := 2)).symm (0 : Fin 3)
      = Sum.inl 0 from rfl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]

@[simp]
theorem euclideanHalfSpaceProdCoordinates_apply_one (p : ProdSpace) :
    euclideanHalfSpaceProdCoordinates p 1 = p.1 0 := by
  rw [coordinates_apply_aux p 1, show (finSumFinEquiv (m := 1) (n := 2)).symm (1 : Fin 3)
      = Sum.inr 0 from rfl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

@[simp]
theorem euclideanHalfSpaceProdCoordinates_apply_two (p : ProdSpace) :
    euclideanHalfSpaceProdCoordinates p 2 = p.1 1 := by
  rw [coordinates_apply_aux p 2, show (finSumFinEquiv (m := 1) (n := 2)).symm (2 : Fin 3)
      = Sum.inr 1 from rfl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

def euclideanHalfSpaceProdHomeomorph : ProdModel ≃ₜ EuclideanHalfSpace 3 where
  toFun x := ⟨euclideanHalfSpaceProdCoordinates (((𝓡 2).prod (𝓡∂ 1)) x), by
    rw [euclideanHalfSpaceProdCoordinates_apply_zero]
    exact x.2.2⟩
  invFun y :=
    ((euclideanHalfSpaceProdCoordinates.symm y.1).1,
      ⟨(euclideanHalfSpaceProdCoordinates.symm y.1).2, by
        rw [← euclideanHalfSpaceProdCoordinates_apply_zero
          (euclideanHalfSpaceProdCoordinates.symm y.1),
          ContinuousLinearEquiv.apply_symm_apply]
        exact y.2⟩)
  left_inv x := by
    apply Prod.ext
    · simp [modelWithCorners_prod_coe, ContinuousLinearEquiv.symm_apply_apply]
    · exact Subtype.ext (by
        simp [modelWithCorners_prod_coe, ContinuousLinearEquiv.symm_apply_apply])
  right_inv y := by
    apply Subtype.ext
    change euclideanHalfSpaceProdCoordinates
      (euclideanHalfSpaceProdCoordinates.symm y.1) = y.1
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  continuous_toFun := by
    exact Continuous.subtype_mk
      (euclideanHalfSpaceProdCoordinates.continuous.comp (((𝓡 2).prod (𝓡∂ 1))).continuous)
      fun x => by
        simp only [Function.comp_apply]
        rw [euclideanHalfSpaceProdCoordinates_apply_zero]
        exact x.2.2
  continuous_invFun := by
    have hq : Continuous fun y : EuclideanHalfSpace 3 =>
        euclideanHalfSpaceProdCoordinates.symm y.1 :=
      euclideanHalfSpaceProdCoordinates.symm.continuous.comp continuous_subtype_val
    refine (continuous_fst.comp hq).prodMk (Continuous.subtype_mk (continuous_snd.comp hq) ?_)
    intro y
    simp only [Function.comp_apply]
    rw [← euclideanHalfSpaceProdCoordinates_apply_zero
      (euclideanHalfSpaceProdCoordinates.symm y.1), ContinuousLinearEquiv.apply_symm_apply]
    exact y.2

theorem euclideanHalfSpaceProdHomeomorph_model (x : ProdModel) :
    (𝓡∂ 3) (euclideanHalfSpaceProdHomeomorph x) =
      euclideanHalfSpaceProdCoordinates ((𝓡 2).prod (𝓡∂ 1) x) := rfl

@[instance_reducible]
def euclideanHalfSpaceProdChartedSpace (M : Type*) [TopologicalSpace M]
    [ChartedSpace ProdModel M] : ChartedSpace (EuclideanHalfSpace 3) M :=
  chartedSpaceTransHomeomorph (M := M) euclideanHalfSpaceProdHomeomorph

theorem euclideanHalfSpaceProd_isManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace ProdModel M] [IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ M] :
    letI := euclideanHalfSpaceProdChartedSpace M
    IsManifold (𝓡∂ 3) ∞ M :=
  isManifold_transHomeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model

theorem euclideanHalfSpaceProd_boundary (M : Type*) [TopologicalSpace M]
    [ChartedSpace ProdModel M] :
    letI := euclideanHalfSpaceProdChartedSpace M
    (𝓡∂ 3).boundary M = ((𝓡 2).prod (𝓡∂ 1)).boundary M :=
  boundary_transHomeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model

theorem euclideanHalfSpaceProd_isInteriorPoint_iff (M : Type*) [TopologicalSpace M]
    [ChartedSpace ProdModel M] (x : M) :
    letI := euclideanHalfSpaceProdChartedSpace M
    (𝓡∂ 3).IsInteriorPoint x ↔ ((𝓡 2).prod (𝓡∂ 1)).IsInteriorPoint x :=
  isInteriorPoint_transHomeomorph_iff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model x

theorem euclideanHalfSpaceProdHomeomorph_zero :
    euclideanHalfSpaceProdHomeomorph (0, 0) = 0 := by
  apply Subtype.ext
  change (𝓡∂ 3) (euclideanHalfSpaceProdHomeomorph (0, 0)) =
    (𝓡∂ 3) (0 : EuclideanHalfSpace 3)
  rw [euclideanHalfSpaceProdHomeomorph_model]
  change euclideanHalfSpaceProdCoordinates (((𝓡 2).prod (𝓡∂ 1)) (0, 0)) = 0
  rw [show ((𝓡 2).prod (𝓡∂ 1)) (0, 0) = 0 from rfl, map_zero]

private instance instIsManifoldProdModel :
    IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ ProdModel := inferInstance

theorem euclideanHalfSpaceProd_isManifold_self :
    letI := euclideanHalfSpaceProdChartedSpace ProdModel
    IsManifold (𝓡∂ 3) ∞ ProdModel :=
  euclideanHalfSpaceProd_isManifold ProdModel

end DifferentialGeometry.Manifold
