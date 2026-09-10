import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereAntipodalLength

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance cylinderSphereLengthDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem cylinder_sphere_speed_le (q : SpatialNeckCylinder)
    (v : TangentSpace SpatialNeckCylinderModel q) :
    Real.sqrt ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner q.1 v.1 v.1) ≤
      Real.sqrt (unitCylinderMetric.inner q v v) := by
  apply Real.sqrt_le_sqrt
  change (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner q.1 v.1 v.1 ≤
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner q.1 v.1 v.1 + v.2 * v.2
  nlinarith [sq_nonneg v.2]

theorem unitCylinder_sphere_projection_length_le {γ : ℝ → SpatialNeckCylinder} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b)) :
    metricPathELength (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) (Prod.fst ∘ γ) a b ≤
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ a b := by
  rw [metricPathELength_eq, metricPathELength_eq]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hγd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hfst : MDifferentiableAt SpatialNeckCylinderModel (𝓡 2)
      (Prod.fst : SpatialNeckCylinder → SpatialNeckSphere) (γ t) := mdifferentiableAt_fst
  have hd : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (Prod.fst ∘ γ) t 1 : EuclideanSpace ℝ (Fin 2)) =
      (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1).1 := by
    rw [mfderiv_comp_apply t hfst hγd, mfderiv_fst]
    rfl
  have hi := congrArg₂ (fun V Z : EuclideanSpace ℝ (Fin 2) =>
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (γ t).1 V Z) hd hd
  calc
    _ = ENNReal.ofReal (Real.sqrt
        ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (γ t).1
          (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1).1
          (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1).1)) :=
      congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z)) hi
    _ ≤ _ := ENNReal.ofReal_le_ofReal (cylinder_sphere_speed_le (γ t) _)

theorem unitCylinder_antipodal_length_lower {γ : ℝ → SpatialNeckCylinder} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b))
    (hanti : (γ b).1 = -(γ a).1) :
    ENNReal.ofReal Real.pi ≤
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ a b := by
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) 1 (Prod.fst ∘ γ) (Icc a b) :=
    contMDiff_fst.comp_contMDiffOn hγ
  exact (sphere2_antipodal_length_lower hab hc hanti).trans
    (unitCylinder_sphere_projection_length_le hγ)

theorem unitCylinder_antipodal_length_lower_on_open
    (U : TopologicalSpace.Opens SpatialNeckCylinder) {γ : ℝ → U} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b))
    (hanti : (γ b).val.1 = -(γ a).val.1) :
    ENNReal.ofReal Real.pi ≤ metricPathELength (I := SpatialNeckCylinderModel)
      (unitCylinderMetric.restrictOpen U) γ a b := by
  have hval : ContMDiff SpatialNeckCylinderModel SpatialNeckCylinderModel 1
      (Subtype.val : U → SpatialNeckCylinder) := contMDiff_subtype_val
  have hcomp := hval.comp_contMDiffOn hγ
  exact (unitCylinder_antipodal_length_lower hab hcomp hanti).trans_eq
    (unitCylinder_metricPathELength_restrict_open U hγ).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
