import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exp_two_conformalFactor_le_one (z : ℝ) :
    Real.exp (2 * conformalFactor z) ≤ 1 := by
  rw [exp_two_conformalFactor]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hp : 0 < warpingFunction (conformalRadius z) / Real.sqrt 2 :=
    div_pos (warpingFunction_pos (conformalRadius_pos z)) hs
  have hu : warpingFunction (conformalRadius z) / Real.sqrt 2 ≤ 1 :=
    (div_le_one hs).mpr (warpingFunction_le_sqrt_two _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith :
    0 ≤ 1 + warpingFunction (conformalRadius z) / Real.sqrt 2)]

private theorem original_mem {A B : ℝ} (hAB : 2 * A < B)
    (q : insertionCylinder A B) : q.val ∈ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  change -B < q.val.2 ∧ q.val.2 < B
  exact ⟨by have hz := q.property.1; linarith, q.property.2⟩

theorem insertedMetric_inner_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v : TangentSpace IC q)
    (hlower : η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v) ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
  rw [insertedMetric_interpolation]
  have hc : 0 ≤ insertionCutoff A q.val.2 ∧ insertionCutoff A q.val.2 ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hpos := metric_inner_self_nonneg h
    (⟨q.val, original_mem hAB q⟩) v
  have hcomb := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hc.2)
  have hexp := Real.exp_pos (2 * conformalFactor q.val.2)
  have hfactor := exp_two_conformalFactor_le_one q.val.2
  have hblend : insertionCutoff A q.val.2 *
      h.inner ⟨q.val, original_mem hAB q⟩ v v +
      (1 - insertionCutoff A q.val.2) * η *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hblend hexp.le).trans
    (mul_le_of_le_one_left hpos hfactor)

theorem insertedMetric_inner_le_of_metricDerivNorm_le {A B δ : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B)
    (herr : metricDerivNorm 0 h
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
        (DifferentialGeometry.Geometry.Neck.openCylinder B))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
        (DifferentialGeometry.Geometry.Neck.openCylinder B))
      ⟨q.val, original_mem hAB q⟩ ≤ δ)
    (v : TangentSpace IC q) :
    (insertedMetric hA hAB
      (sub_pos.mpr ((Real.sqrt_lt hδ zero_le_one).mpr (by simpa using hδ1))) h).inner
      (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v) ≤
      h.inner ⟨q.val, original_mem hAB q⟩ v v := by
  apply insertedMetric_inner_le_of_cylinder_lower
  have hb := (inner_bounds_of_metricDerivNorm_le
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen
      (DifferentialGeometry.Geometry.Neck.openCylinder B)) h _ herr v).1
  have hnn := metric_inner_self_nonneg (roundCylinderMetric (E := E3) (n := 2)) q.val v
  have hs : δ ≤ Real.sqrt δ := by
    have hsq := Real.sq_sqrt hδ
    have hlo := Real.sqrt_nonneg δ
    have hhi := (Real.sqrt_lt hδ zero_le_one).mpr (by simpa using hδ1)
    nlinarith [mul_nonneg hlo (sub_nonneg.mpr hhi.le)]
  change (1 - δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ _ at hb
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hs 1) hnn).trans hb

end DifferentialGeometry.PDE.RicciFlow.StandardCap
