import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

open Filter Set Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_comparisonAngleNegCurvature_of_pos {I : Type*} {l : Filter I}
    {a b c : I → ℝ} {κ a₀ b₀ c₀ : ℝ} (hκ : 0 < κ)
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀))
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun i => comparisonAngleNegCurvature κ (a i) (b i) (c i)) l
      (𝓝 (comparisonAngleNegCurvature κ a₀ b₀ c₀)) := by
  have hka := ha.const_mul (sqrt κ)
  have hkb := hb.const_mul (sqrt κ)
  have hkc := hc.const_mul (sqrt κ)
  have hnum := ((continuous_cosh.tendsto _).comp hka).mul ((continuous_cosh.tendsto _).comp hkb)
  have hden := ((continuous_sinh.tendsto _).comp hka).mul ((continuous_sinh.tendsto _).comp hkb)
  have hpos : 0 < sinh (sqrt κ * a₀) * sinh (sqrt κ * b₀) :=
    mul_pos (sinh_pos_iff.mpr (mul_pos (sqrt_pos.mpr hκ) ha₀))
      (sinh_pos_iff.mpr (mul_pos (sqrt_pos.mpr hκ) hb₀))
  have hquot := (hnum.sub ((continuous_cosh.tendsto _).comp hkc)).div hden hpos.ne'
  simpa only [comparisonAngleNegCurvature, hκ.ne', ite_false, Function.comp_def, Pi.div_apply] using
    (continuous_arccos.tendsto _).comp hquot

end DifferentialGeometry.Geometry.Comparison.Toponogov
