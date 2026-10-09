import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapPlane
import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapSplitting
open DifferentialGeometry.Geometry.Collapse.EdgeCapPlane
open GC.MetricGeometry
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo
  capSurfaceSigma capSurfaceMetricSpace capSurfaceEDist capSurfaceDist
  capSurfaceUniform capSurfaceEMetric capSurfacePseudo
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapRankOne
noncomputable def physicalProductIsometry : E3 ≃ᵢ WithLp 2 (ℝ × E2) where
  toEquiv := capProductCoordinates.symm.toEquiv.trans (WithLp.equiv 2 _).symm
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (WithLp.toLp 2 (capProductCoordinates.symm x))
      (WithLp.toLp 2 (capProductCoordinates.symm y)) = dist x y
    rw [← physical_L2_distance]
    simp only [Diffeomorph.apply_symm_apply]

def realShift (c : ℝ) : ℝ ≃ᵢ ℝ where
  toFun t := t - c
  invFun t := t + c
  left_inv t := sub_add_cancel t c
  right_inv t := add_sub_cancel_right t c
  isometry_toFun := Isometry.of_dist_eq (fun _ _ => dist_sub_right _ _ _)

noncomputable def oneSplittingEquiv (p : E3) :
    E3 ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × E2) :=
  physicalProductIsometry.trans
    (((realShift (capThreeCoord p)).withLpProdCongr 2 (IsometryEquiv.refl E2)).trans
      (realProdIso_SGP E2))

theorem oneSplittingEquiv_base (p : E3) : oneSplittingEquiv p p =
    WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), (capProductCoordinates.symm p).2) := by
  apply (WithLp.equiv 2 _).injective
  change (realFinOneIso_SGP ((capProductCoordinates.symm p).1 - capThreeCoord p),
    (capProductCoordinates.symm p).2) = (0, (capProductCoordinates.symm p).2)
  rw [capThreeCoord, sub_self, map_zero]

theorem actual_one_splitting (p : E3) (β : ℝ) (hβ : 0 < β) (hβone : β < 1) :
    HasEuclideanSplitting.{0, 0} p 1 β := by
  exact ⟨E2, capSurfaceMetricSpace, (capProductCoordinates.symm p).2,
    ⟨(oneSplittingEquiv p).toKleinerLottApprox (oneSplittingEquiv_base p) hβ hβone⟩⟩

theorem oneSplittingEquiv_fst (p x : E3) : (oneSplittingEquiv p x).fst =
    realFinOneIso_SGP (capThreeCoord x - capThreeCoord p) := rfl

theorem actual_one_splitting_native (p : E3) (β : ℝ) (hβ : 0 < β) (hβone : β < 1) :
    @HasEuclideanSplitting.{0, 0} E3
      (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) p 1 β := by
  have hm : capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num) =
      capExampleMetricSpace := by simp
  rw [hm]
  exact actual_one_splitting p β hβ hβone

theorem realCollarPoint_one_splitting : @HasEuclideanSplitting.{0, 0} E3
    (capExampleMetricSpace.rescale (1 : ℝ)⁻¹ (by norm_num)) realCollarPoint 1 (1 / 100) :=
  actual_one_splitting_native realCollarPoint (1 / 100) (by norm_num) (by norm_num)

end DifferentialGeometry.Geometry.Collapse.EdgeCapRankOne
