import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Gradient.SignedDifference
import DifferentialGeometry.Geometry.Metric.LengthPerturbation

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Gradient DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

def cylindricalChart.axialVector (C : cylindricalChart J (M := M)) (x : C.domain) :
    TangentSpace J (C.chart x : M) :=
  mfderiv J J (Subtype.val : C.target → M) (C.chart x)
    (Real.sqrt C.scale • mfderiv ((𝓡 2).prod 𝓘(ℝ)) J C.chart x (0, 1))

theorem cylindricalChart.mvfderiv_axial_axialVector
    (C : cylindricalChart J (M := M)) (x : C.domain) :
    mvfderiv J C.axial (C.chart x : M) (C.axialVector x) = 1 := by
  let q : C.domain → ℝ := fun y ↦ (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2
  have hq : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ q :=
    contMDiff_snd.comp contMDiff_subtype_val
  let u : C.target → ℝ := fun y ↦ (Real.sqrt C.scale)⁻¹ * q (C.chart.symm y)
  have hu : ContMDiff J 𝓘(ℝ) ∞ u := contMDiff_const.mul (hq.comp C.chart.symm.contMDiff)
  change mvfderiv J (Subtype.val.extend u (fun _ ↦ 0)) (C.chart x : M)
    (mfderiv J J (Subtype.val : C.target → M) (C.chart x)
      (Real.sqrt C.scale • mfderiv ((𝓡 2).prod 𝓘(ℝ)) J C.chart x (0, 1))) = 1
  rw [mvfderiv_extend_from_open C.target u _ hu]
  let gS := scaleMetric 2 (by norm_num)
    (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  exact (mvfderiv_scaled_chart_coordinate C.chart q hq C.scale C.scale_pos x (0, 1)).trans
    ((restrictedCylinderAxis_inner gS C.domain x (0, 1)).symm.trans
      (restrictedCylinderAxis_unit gS C.domain x))

variable [FiniteDimensional ℝ F] [IsManifold J ∞ M] [T2Space M]

theorem cylindricalChart.axialVector_length_le_of_metric_close
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C.metricCloseOn g ε U)
    (x : C.domain) (hx : x ∈ U) :
    Real.sqrt (g.inner (C.chart x : M) (C.axialVector x) (C.axialVector x)) ≤
      Real.sqrt (1 + ε) := by
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gC := Diffeomorph.pullbackMetricCross
    (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart
  let gS := scaleMetric 2 (by norm_num)
    (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  let gRef := (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain
  have hb := (sqrt_inner_comparison_of_metric_difference gC gRef x ε hε
    (hsmall x hx 0 (by decide)) (0, 1)).2
  have hunit : gRef.inner x (0, 1) (0, 1) = 1 := restrictedCylinderAxis_unit gS C.domain x
  rw [hunit, Real.sqrt_one, mul_one] at hb
  have heq : g.inner (C.chart x : M) (C.axialVector x) (C.axialVector x) =
      gC.inner x (0, 1) (0, 1) := by
    let v : TangentSpace J (C.chart x) := mfderiv IC J C.chart x (0, 1)
    have hval : mfderiv J J (Subtype.val : C.target → M) (C.chart x)
        (Real.sqrt C.scale • v) = Real.sqrt C.scale • v := by
      rw [mfderiv_subtype_val]
      rfl
    change g.inner (C.chart x : M)
      (mfderiv J J (Subtype.val : C.target → M) (C.chart x) (Real.sqrt C.scale • v))
      (mfderiv J J (Subtype.val : C.target → M) (C.chart x) (Real.sqrt C.scale • v)) = _
    rw [hval]
    change (g.restrictOpen C.target).inner (C.chart x)
      (Real.sqrt C.scale • v) (Real.sqrt C.scale • v) = _
    have hs : (g.restrictOpen C.target).inner (C.chart x)
        (Real.sqrt C.scale • v) (Real.sqrt C.scale • v) =
        C.scale * (g.restrictOpen C.target).inner (C.chart x) v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt C.scale_pos.le]
    exact hs.trans (Diffeomorph.pullbackMetricCross_inner
      (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart x (0, 1) (0, 1)).symm
  rwa [heq]

theorem cylindricalChart.mvfderiv_axialVector_ne_zero_of_gradient_close
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C.metricCloseOn g ε U)
    (q : M → ℝ) (σ δ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hδ : δ * Real.sqrt (1 + ε) < 1) (x : C.domain) (hx : x ∈ U)
    (hgrad : Real.sqrt (g.inner (C.chart x : M)
      (DifferentialGeometry.Geometry.Operator.gradFun g q (C.chart x : M) -
        σ • DifferentialGeometry.Geometry.Operator.gradFun g C.axial (C.chart x : M))
      (DifferentialGeometry.Geometry.Operator.gradFun g q (C.chart x : M) -
        σ • DifferentialGeometry.Geometry.Operator.gradFun g C.axial (C.chart x : M))) ≤ δ) :
    mvfderiv J q (C.chart x : M) (C.axialVector x) ≠ 0 := by
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hgrad
  have h := abs_mvfderiv_signed_difference_le_gradient_norm g q C.axial σ
    (C.chart x : M) (C.axialVector x)
  have hb := h.trans (mul_le_mul hgrad
    (C.axialVector_length_le_of_metric_close g ε hε hsmall x hx)
    (Real.sqrt_nonneg _) hδ0)
  rw [C.mvfderiv_axial_axialVector, mul_one] at hb
  intro hz
  rw [hz, zero_sub, abs_neg] at hb
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [hσabs] at hb
  exact (not_lt_of_ge hb) hδ

end DifferentialGeometry.Geometry.Neck
