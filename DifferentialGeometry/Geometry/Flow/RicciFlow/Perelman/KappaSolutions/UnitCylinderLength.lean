import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance cylinderLengthSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


theorem unitCylinder_axial_speed_le (q : SpatialNeckCylinder)
    (v : TangentSpace SpatialNeckCylinderModel q) :
    |v.2| ≤ Real.sqrt (unitCylinderMetric.inner q v v) := by
  have hround : 0 ≤ (Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3))
      (n := 2)).inner q.1 v.1 v.1 :=
    Geometry.Riemannian.Exponential.gInner_self_nonneg
      (Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) q.1 v.1
  calc
    |v.2| = Real.sqrt (v.2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (unitCylinderMetric.inner q v v) := by
      apply Real.sqrt_le_sqrt
      change v.2 ^ 2 ≤ (Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3))
        (n := 2)).inner q.1 v.1 v.1 + v.2 * v.2
      nlinarith

theorem unitCylinder_axial_length_lower {γ : ℝ → SpatialNeckCylinder} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b)) :
    ENNReal.ofReal |(γ b).2 - (γ a).2| ≤
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ a b := by
  have hc : ContDiffOn ℝ 1 (Prod.snd ∘ γ) (Icc a b) :=
    (contMDiff_snd.comp_contMDiffOn hγ).contDiffOn
  have hlower := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hc hab
  rw [← ofReal_norm, Real.norm_eq_abs, ← restrict_Ioo_eq_restrict_Icc] at hlower
  apply hlower.trans
  rw [metricPathELength_eq]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have hγd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hder : deriv (Prod.snd ∘ γ) t =
      (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1).2 := by
    have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Prod.snd ∘ γ) t 1 =
        (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1).2 := by
      rw [mfderiv_comp_apply t mdifferentiableAt_snd hγd, mfderiv_snd]
      rfl
    rw [mfderiv_eq_fderiv] at hm
    exact hm
  rw [← ofReal_norm, Real.norm_eq_abs, hder]
  exact ENNReal.ofReal_le_ofReal (unitCylinder_axial_speed_le (γ t) _)

theorem unitCylinder_metricPathELength_restrict_open
    (U : TopologicalSpace.Opens SpatialNeckCylinder) {γ : ℝ → U} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b)) :
    metricPathELength (I := SpatialNeckCylinderModel) (unitCylinderMetric.restrictOpen U) γ a b =
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric
        ((Subtype.val : U → SpatialNeckCylinder) ∘ γ) a b := by
  rw [metricPathELength_eq, metricPathELength_eq]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hγd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hvald := (contMDiff_subtype_val (I := SpatialNeckCylinderModel) (U := U)
    (n := ∞)).mdifferentiableAt (x := γ t) (by decide)
  have hcomp := mfderiv_comp_apply t hvald hγd (1 : ℝ)
  have hid := mfderiv_subtype_val_apply (I := SpatialNeckCylinderModel) U (γ t)
    (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1)
  have hd := hcomp.trans hid
  have hi := congrArg₂
    (fun V Z : EuclideanSpace ℝ (Fin 2) × ℝ => unitCylinderMetric.inner (γ t).val V Z) hd hd
  have hr := SmoothRiemannianMetric.restrictOpen_inner unitCylinderMetric U (γ t)
    (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1)
    (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1)
  exact congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z)) (hr.trans hi.symm)

theorem unitCylinder_axial_length_lower_on_open
    (U : TopologicalSpace.Opens SpatialNeckCylinder) {γ : ℝ → U} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 γ (Icc a b)) :
    ENNReal.ofReal |(γ b).val.2 - (γ a).val.2| ≤
      metricPathELength (I := SpatialNeckCylinderModel) (unitCylinderMetric.restrictOpen U)
        γ a b := by
  have hval : ContMDiff SpatialNeckCylinderModel SpatialNeckCylinderModel ∞
      (Subtype.val : U → SpatialNeckCylinder) := contMDiff_subtype_val
  have hcomp := (hval.of_le (by decide : (1 : WithTop ℕ∞) ≤
    (∞ : WithTop ℕ∞))).comp_contMDiffOn hγ
  have hlower := unitCylinder_axial_length_lower hab hcomp
  exact hlower.trans_eq (unitCylinder_metricPathELength_restrict_open U hγ).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
