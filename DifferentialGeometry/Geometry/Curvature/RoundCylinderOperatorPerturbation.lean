import DifferentialGeometry.Geometry.Curvature.OperatorRicci
import DifferentialGeometry.Geometry.Curvature.ScalarRoundCylinder
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Operator.JetComparison
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open scoped Manifold ContDiff InnerProductSpace BigOperators
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ

private theorem height_derivative (U : TopologicalSpace.Opens (Cyl (E := E)))
    (x : U) (v : TangentSpace IC x) :
    mvfderiv IC (fun y : U => (y : Cyl (E := E)).2) x v = v.2 := by
  rw [mvfderiv_restrictOpen U Prod.snd x v mdifferentiableAt_snd]
  change mfderiv IC 𝓘(ℝ) Prod.snd (x : Cyl (E := E)) v = v.2
  rw [mfderiv_snd]
  rfl

theorem ricciTensor_restricted_roundCylinder_eq_metric_sub_height
    (U : TopologicalSpace.Opens (Cyl (E := E))) (x : U) (v w : TangentSpace IC x) :
    ricciTensor ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x v w =
      (((roundCylinderMetric (E := E) (n := 2)).restrictOpen U).inner x v w -
        mvfderiv IC (fun y : U => (y : Cyl (E := E)).2) x v *
          mvfderiv IC (fun y : U => (y : Cyl (E := E)).2) x w) / 2 := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
    norm_num)
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC U.isOpen)
  rw [ricciTensor_restrictOpen, ricciTensor_roundCylinder,
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
    SmoothRiemannianMetric.restrictOpen_inner, height_derivative, height_derivative]
  erw [roundCylinderMetric, cylinderMetric_inner, scaleMetric_inner]
  change ((2 : ℝ) - 1) * (roundMetric (E := E) (n := 2)).inner (x : Cyl (E := E)).1 v.1 w.1 =
    ((2 * (roundMetric (E := E) (n := 2)).inner (x : Cyl (E := E)).1 v.1 w.1 + v.2 * w.2) -
      v.2 * w.2) / 2
  ring

theorem abs_traceNormalizedCurvatureOperatorAt_sub_height_sq_le
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B)
    (c : EuclideanSpace ℝ (Fin 3)) :
    |⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ -
      (mvfderiv IC (fun y : U => (y : Cyl (E := E)).2) x (bivectorNormalAt x B c)) ^ 2| ≤
        7205 * ε * ‖c‖ ^ 2 := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let N := bivectorNormalAt x B c
  have hn : h.inner x N N = ‖c‖ ^ 2 := bivectorNormalAt_inner_self h x B hB c
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hg0 : 0 ≤ g.inner x N N := metric_inner_self_nonneg g x N
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact (hsmall 0 (by norm_num)).trans hε)
  have hg : g.inner x N N ≤ 2 * ‖c‖ ^ 2 := by
    simpa only [hn] using ((metricUniformEquivalentOn_symm heq).2 x (Set.mem_singleton x) N).2
  have hεg : ε * g.inner x N N ≤ 2 * ε * ‖c‖ ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left hg hε0
    nlinarith only [hb]
  have hm : |‖c‖ ^ 2 - g.inner x N N| ≤ 2 * ε * ‖c‖ ^ 2 := by
    have hb := metricDifference_abs_le h g g x N N
    rw [mul_assoc, Real.mul_self_sqrt hg0, hn] at hb
    exact (hb.trans (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num)) hg0)).trans hεg
  have hr : |ricciTensor h x N N - ricciTensor g x N N| ≤ 1440 * ε * ‖c‖ ^ 2 := by
    have hb := abs_ricci_difference_bound_of_small_metric_derivatives h g x ε hε hsmall N N
    rw [mul_assoc, Real.mul_self_sqrt hg0] at hb
    norm_num only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
      Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hb
    nlinarith only [hb, hεg]
  have hs : |(metricScalarAt h x - 1) * ‖c‖ ^ 2| ≤ 4323 * ε * ‖c‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖c‖)]
    exact mul_le_mul_of_nonneg_right
      (abs_scalar_curvature_restricted_roundCylinder_sub_one_le U h x ε hε hsmall)
      (sq_nonneg ‖c‖)
  have hR := ricciTensor_restricted_roundCylinder_eq_metric_sub_height U x N N
  change ricciTensor g x N N = _ at hR
  rw [inner_traceNormalizedCurvatureOperatorAt_eq_scalar_sub_two_ricci h x B hB c]
  change |metricScalarAt h x * ‖c‖ ^ 2 - 2 * ricciTensor h x N N -
    (mvfderiv IC (fun y : U => (y : Cyl (E := E)).2) x N) ^ 2| ≤ _
  rcases abs_le.mp hs with ⟨hsL, hsU⟩
  rcases abs_le.mp hm with ⟨hmL, hmU⟩
  rcases abs_le.mp hr with ⟨hrL, hrU⟩
  apply abs_le.mpr
  constructor <;> nlinarith only [hR, hsL, hsU, hmL, hmU, hrL, hrU]

end DifferentialGeometry.Geometry.Curvature
