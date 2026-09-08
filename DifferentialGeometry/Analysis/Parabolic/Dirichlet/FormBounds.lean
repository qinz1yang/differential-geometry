import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletFormBounds
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem abs_dirichletMassVariation_le_norm
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    (u v : SmoothScalarDirichlet (g t)) :
    |dirichletMassVariation g t u v| ≤
      (1 / 2) * max B 0 * ‖u‖ * ‖v‖ := by
  let fu : M → ℝ := fun x => |u.toFun x|
  let fv : M → ℝ := fun x => |v.toFun x|
  have hfu : MemLp fu 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    simpa only [fu, Real.norm_eq_abs] using u.memLp_two.norm
  have hfv : MemLp fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    simpa only [fv, Real.norm_eq_abs] using v.memLp_two.norm
  have hprod : Integrable
      (fun x => (1 / 2) * max B 0 * (fu x * fv x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
    have hbase' : Integrable (fun x => fu x * fv x)
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
      change Integrable (fu * fv)
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))
      exact hfu.integrable_mul hfv
    exact hbase'.const_mul _
  have hholder : (∫ x, fu x * fv x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))) ≤
      (eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal *
      (eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal := by
    have h := DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two hfu hfv
    rw [abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))] at h
    exact h
  have hfunorm : (eLpNorm fu 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal ≤ ‖u‖ := by
    rw [show eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) =
      eLpNorm u.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) by
      simpa only [fu, Real.norm_eq_abs] using
        (eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) u.toFun)]
    have hnorm := u.norm_smoothToLp_le
    change ‖u.memLp_two.toLp u.toFun‖ ≤ ‖u‖ at hnorm
    rwa [Lp.norm_toLp] at hnorm
  have hfvnorm : (eLpNorm fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal ≤ ‖v‖ := by
    rw [show eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) =
      eLpNorm v.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) by
      simpa only [fv, Real.norm_eq_abs] using
        (eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) v.toFun)]
    have hnorm := v.norm_smoothToLp_le
    change ‖v.memLp_two.toLp v.toFun‖ ≤ ‖v‖ at hnorm
    rwa [Lp.norm_toLp] at hnorm
  unfold dirichletMassVariation
  calc
    |∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
        (u.toFun x * v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))| ≤
      ∫ x, |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
        (u.toFun x * v.toFun x)|
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 / 2) * max B 0 * (fu x * fv x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hprod
        (Filter.Eventually.of_forall fun x => by
          change |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
              (u.toFun x * v.toFun x)| ≤
            (1 / 2) * max B 0 * (fu x * fv x)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              ((htrace x).trans (le_max_left B 0)) (by norm_num))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = (1 / 2) * max B 0 * (∫ x, fu x * fv x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))) := by
      rw [integral_const_mul]
    _ ≤ (1 / 2) * max B 0 *
        ((eLpNorm fu 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal *
        (eLpNorm fv 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal) :=
      mul_le_mul_of_nonneg_left hholder
        (mul_nonneg (by norm_num) (le_max_right B 0))
    _ ≤ (1 / 2) * max B 0 * (‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hfunorm hfvnorm ENNReal.toReal_nonneg (norm_nonneg u))
        (mul_nonneg (by norm_num) (le_max_right B 0))
    _ = (1 / 2) * max B 0 * ‖u‖ * ‖v‖ := by ring

theorem abs_dirichletMassVariation_le_of_metric_and_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ (g t).inner x v v ∧
        (g t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) (g t) ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    |dirichletMassVariation g t u v| ≤
      (1 / 2) * max B 0 * (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by
  let uh : SmoothScalarDirichlet (g t) := ⟨u.toFun, u.smooth, u.interior_support⟩
  let vh : SmoothScalarDirichlet (g t) := ⟨v.toFun, v.smooth, v.interior_support⟩
  have hsame := abs_dirichletMassVariation_le_norm g t B htrace uh vh
  have hu := norm_smoothScalarDirichlet_le_of_metric_and_volume (g t) hCg hequiv
    Cv hCv0 hCvtop hvol u uh rfl
  have hv := norm_smoothScalarDirichlet_le_of_metric_and_volume (g t) hCg hequiv
    Cv hCv0 hCvtop hvol v vh rfl
  have hA : 0 ≤ Cv.toReal * Cg :=
    mul_nonneg ENNReal.toReal_nonneg (le_trans zero_le_one hCg)
  have hnorm : ‖uh‖ * ‖vh‖ ≤ Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
    calc
      ‖uh‖ * ‖vh‖ ≤ (Real.sqrt (Cv.toReal * Cg) * ‖u‖) *
          (Real.sqrt (Cv.toReal * Cg) * ‖v‖) :=
        mul_le_mul hu hv (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      _ = Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
        rw [show Real.sqrt (Cv.toReal * Cg) * ‖u‖ *
            (Real.sqrt (Cv.toReal * Cg) * ‖v‖) =
          Real.sqrt (Cv.toReal * Cg) ^ 2 * ‖u‖ * ‖v‖ by ring, Real.sq_sqrt hA]
  calc
    |dirichletMassVariation g t u v| =
        |dirichletMassVariation g t uh vh| := by
      rfl
    _ ≤ (1 / 2) * max B 0 * ‖uh‖ * ‖vh‖ := hsame
    _ ≤ (1 / 2) * max B 0 * (Cv.toReal * Cg * ‖u‖ * ‖v‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_max_right B 0))
    _ = (1 / 2) * max B 0 * (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
