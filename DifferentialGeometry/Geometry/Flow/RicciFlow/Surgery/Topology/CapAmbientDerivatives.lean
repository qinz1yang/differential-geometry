import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeBallChartDictionary
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

open private standardNeckCapDenAmbient_eq standardNeckCapDenNe standardNeckCapAmbientS
  standardNeckCapAmbientT from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeBallChartDictionary

private theorem toSpanSingleton_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (L : F →L[ℝ] ℝ) :
    (ContinuousLinearMap.toSpanSingleton ℝ a) ∘SL L = a • L := by
  ext h
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

theorem hasFDerivAt_capNormSq (v : E3) :
    HasFDerivAt (fun w : E3 => ‖w‖ ^ 2) ((2 : ℝ) • innerSL ℝ v) v := by
  simpa only [two_nsmul, two_smul ℝ] using (hasStrictFDerivAt_norm_sq v).hasFDerivAt

theorem hasFDerivAt_capDen (v : E3) :
    HasFDerivAt (fun w : E3 => 1 + standardNeckCapAmbientRadius ^ 2 * ‖w‖ ^ 2)
      ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v) v := by
  have h1 := (hasFDerivAt_capNormSq v).const_mul (standardNeckCapAmbientRadius ^ 2)
  have h2 := h1.const_add (1 : ℝ)
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2

theorem hasFDerivAt_capDenInv (v : E3) :
    HasFDerivAt ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
        ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v)) v := by
  have hden : HasFDerivAt (fun w : E3 => standardNeckCapDenAmbient w)
      ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v) v := by
    simpa only [standardNeckCapDenAmbient_eq] using hasFDerivAt_capDen v
  have hne : standardNeckCapDenAmbient v ≠ 0 :=
    fun hzero => standardNeckCapDenNe v (by simpa only [standardNeckCapDenAmbient_eq] using hzero)
  exact (hasFDerivAt_inv hne).comp v hden

theorem hasFDerivAt_capNumT (v : E3) :
    HasFDerivAt (fun w : E3 => 1 - standardNeckCapAmbientRadius ^ 2 * ‖w‖ ^ 2)
      ((-(2 * standardNeckCapAmbientRadius ^ 2)) • innerSL ℝ v) v := by
  have h := (hasFDerivAt_capNormSq v).const_mul (standardNeckCapAmbientRadius ^ 2)
  have h2 := h.const_sub (1 : ℝ)
  simpa [neg_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2

theorem hasFDerivAt_capSRaw (v : E3) :
    HasFDerivAt (fun w : E3 => (2 * standardNeckCapAmbientRadius) *
        ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient) w)
      ((2 * standardNeckCapAmbientRadius) •
        (ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
          ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v))) v :=
  (hasFDerivAt_capDenInv v).const_mul (2 * standardNeckCapAmbientRadius)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
