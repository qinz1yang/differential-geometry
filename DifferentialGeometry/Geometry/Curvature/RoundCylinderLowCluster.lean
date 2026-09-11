import DifferentialGeometry.Geometry.Curvature.RoundCylinderOperatorPerturbation
import DifferentialGeometry.Geometry.Curvature.BivectorDifferential
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Analysis.FiniteDimensional.QuadraticNormBound
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis
open scoped Manifold ContDiff InnerProductSpace
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Cyl := Metric.sphere (0 : E) 1 × ℝ

private theorem restricted_height_gradient_unit
    (U : TopologicalSpace.Opens (Cyl (E := E))) (x : U) :
    ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U).inner x
      (gradFun ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        (fun y : U => (y : Cyl (E := E)).2) x)
      (gradFun ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        (fun y : U => (y : Cyl (E := E)).2) x) = 1 := by
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  have h := gradFun_restrictOpen (roundCylinderMetric (E := E) (n := 2))
    U Prod.snd x mdifferentiableAt_snd
  rw [mfderiv_subtype_val_apply] at h
  have haxis := gradFun_height_eq_cylinderAxis gS (x : Cyl (E := E))
  have hgrad : gradFun ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
      (fun y : U => (y : Cyl (E := E)).2) x =
      cylinderAxis (I := 𝓡 2) (x : Cyl (E := E)) := h.trans haxis
  change (roundCylinderMetric (E := E) (n := 2)).inner (x : Cyl (E := E)) _ _ = 1
  erw [hgrad]
  exact cylinderMetric_axis_unit gS (x : Cyl (E := E))

theorem exists_unit_rankOne_approx_of_roundCylinder_metric_jets
    (U : TopologicalSpace.Opens (Cyl (E := E)))
    (h : SmoothRiemannianMetric IC U) (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k h ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace IC x)) (hB : OrthonormalBasisAt h x B) :
    ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧
      ∀ c : EuclideanSpace ℝ (Fin 3),
        ‖(traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v) c‖ ≤
          7207 * ε * ‖c‖ := by
  let g := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  let F := fun y : U => (y : Cyl (E := E)).2
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  obtain ⟨v, hv, hclose⟩ := exists_unit_bivectorDifferential_approx_of_metricDerivNorm
    g h F x B hB (restricted_height_gradient_unit U x) ε hε (hsmall 0 (by norm_num))
  let T := traceNormalizedCurvatureOperatorAt h x B - InnerProductSpace.rankOne ℝ v v
  have hT : T.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (traceNormalizedCurvatureOperatorAt_isSelfAdjoint h x B)).sub
        (InnerProductSpace.isSymmetric_rankOne_self v)
  have hquad (c : EuclideanSpace ℝ (Fin 3)) : |⟪T c, c⟫_ℝ| ≤ 7207 * ε * ‖c‖ ^ 2 := by
    have hc := abs_traceNormalizedCurvatureOperatorAt_sub_height_sq_le U h x ε hε hsmall B hB c
    have hvq := hclose c
    have he : ⟪T c, c⟫_ℝ =
        (⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ -
          (mvfderiv IC F x (bivectorNormalAt x B c)) ^ 2) +
        ((mvfderiv IC F x (bivectorNormalAt x B c)) ^ 2 - ⟪v, c⟫_ℝ ^ 2) := by
      simp only [T, sub_apply, inner_sub_left,
        InnerProductSpace.rankOne_apply, real_inner_smul_left]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    change |⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ -
      (mvfderiv IC F x (bivectorNormalAt x B c)) ^ 2| ≤ 7205 * ε * ‖c‖ ^ 2 at hc
    linarith only [hc, hvq]
  have hnorm := opNorm_le_of_abs_inner_self_le T hT (7207 * ε) (by positivity) hquad
  refine ⟨v, hv, ?_⟩
  intro c
  exact (T.le_opNorm c).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg c))

end DifferentialGeometry.Geometry.Curvature
