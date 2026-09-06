import DifferentialGeometry.Analysis.Integration.L2.Basic
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.Energy
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MetricComparison

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

private def dirichletEnergyRoot
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet h) (x : M) : ℝ :=
  Real.sqrt (h.inner x
    (gradFun (I := I_half n) h u.toFun x)
    (gradFun (I := I_half n) h u.toFun x))

private def rebaseSmoothScalarDirichlet
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) : SmoothScalarDirichlet h where
  toFun := u.toFun
  smooth := u.smooth
  interior_support := u.interior_support

omit [T2Space M] [CompactSpace M] in
@[simp] private lemma rebaseSmoothScalarDirichlet_toFun
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    (rebaseSmoothScalarDirichlet h u).toFun = u.toFun := rfl

private lemma dirichletEnergyRoot_memLp
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet h) :
    MemLp (dirichletEnergyRoot h u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
  have hcont : Continuous (dirichletEnergyRoot h u) :=
    Real.continuous_sqrt.comp
      (WithBoundary.continuous_g_inner_gradFun_gradFun h u.smooth u.smooth)
  let _ : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts
      (I := I_half n) (M := M) h
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [T2Space M] [CompactSpace M] in
private lemma dirichletEnergyRoot_sq
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet h) (x : M) :
    dirichletEnergyRoot h u x ^ 2 = h.inner x
      (gradFun (I := I_half n) h u.toFun x)
      (gradFun (I := I_half n) h u.toFun x) := by
  apply Real.sq_sqrt
  exact SmoothRiemannianMetric_inner_self_nonneg h x _

private lemma dirichletEnergyRoot_eLpNorm_toReal_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet h) :
    (eLpNorm (dirichletEnergyRoot h u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal ≤ ‖u‖ := by
  let hu := dirichletEnergyRoot_memLp h u
  let U := hu.toLp (dirichletEnergyRoot h u)
  have hUsq : ‖U‖ ^ 2 = dirichletEnergy h u u := by
    have hinner := real_inner_self_eq_norm_sq U
    rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at hinner
    have hae : (fun x : M =>
        @inner ℝ _ _ ((U : Lp ℝ 2 _) x) ((U : Lp ℝ 2 _) x)) =ᵐ[
          riemannianVolumeMeasure (I := I_half n) (M := M) h]
        (fun x => dirichletEnergyRoot h u x ^ 2) := by
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx]
      rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs]
      change |Real.sqrt _| ^ 2 = Real.sqrt _ ^ 2
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [integral_congr_ae hae] at hinner
    rw [show (fun x => dirichletEnergyRoot h u x ^ 2) = fun x =>
        h.inner x (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x) from
      funext (dirichletEnergyRoot_sq h u)] at hinner
    exact hinner.symm
  have hdecomp : ‖u‖ ^ 2 = dirichletMass h u u + dirichletEnergy h u u := by
    rw [u.norm_sq_eq_inner_self]
    rfl
  have henergy : dirichletEnergy h u u ≤ ‖u‖ ^ 2 := by
    have hmass := dirichletMass_self_nonneg h u
    linarith
  have hU : ‖U‖ ≤ ‖u‖ := by
    exact (abs_le_of_sq_le_sq' (hUsq.trans_le henergy) (norm_nonneg _)).2
  have hUnorm : ‖U‖ = (eLpNorm (dirichletEnergyRoot h u) 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal :=
    Lp.norm_toLp _ hu
  rw [hUnorm] at hU
  exact hU

private lemma dirichletScalar_eLpNorm_toReal_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet h) :
    (eLpNorm u.toFun 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal ≤ ‖u‖ := by
  have hnorm := u.norm_smoothToLp_le
  change ‖u.memLp_two.toLp u.toFun‖ ≤ ‖u‖ at hnorm
  rwa [Lp.norm_toLp] at hnorm

theorem abs_dirichletMass_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet h) :
    |dirichletMass h u v| ≤ ‖u‖ * ‖v‖ := by
  unfold dirichletMass
  exact (DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two
    u.memLp_two v.memLp_two).trans
      (mul_le_mul (dirichletScalar_eLpNorm_toReal_le_norm h u)
        (dirichletScalar_eLpNorm_toReal_le_norm h v)
        ENNReal.toReal_nonneg (norm_nonneg u))

theorem abs_dirichletEnergy_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (u v : SmoothScalarDirichlet h) :
    |dirichletEnergy h u v| ≤ ‖u‖ * ‖v‖ := by
  let fu := dirichletEnergyRoot h u
  let fv := dirichletEnergyRoot h v
  have hfu := dirichletEnergyRoot_memLp h u
  have hfv := dirichletEnergyRoot_memLp h v
  have hprod : Integrable (fun x => fu x * fv x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
    change Integrable (fu * fv)
      (riemannianVolumeMeasure (I := I_half n) (M := M) h)
    exact hfu.integrable_mul hfv
  have hholder : (∫ x, fu x * fv x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)) ≤
      (eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal *
      (eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal := by
    have h := DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two hfu hfv
    rw [abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h
    exact h
  unfold dirichletEnergy
  calc
    |∫ x, h.inner x (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h v.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)| ≤
        ∫ x, |h.inner x (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h v.toFun x)|
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, fu x * fv x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hprod (Filter.Eventually.of_forall fun x =>
          DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
            (I := I_half n) (M := M) h x _ _)
    _ ≤ (eLpNorm fu 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal *
        (eLpNorm fv 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal := hholder
    _ ≤ ‖u‖ * ‖v‖ :=
      mul_le_mul (dirichletEnergyRoot_eLpNorm_toReal_le_norm h u)
        (dirichletEnergyRoot_eLpNorm_toReal_le_norm h v)
        ENNReal.toReal_nonneg (norm_nonneg u)

theorem abs_dirichletDrift_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    (u v : SmoothScalarDirichlet h) :
    |dirichletDrift h X u v| ≤ Real.sqrt (max B 0) * ‖u‖ * ‖v‖ := by
  let fu := dirichletEnergyRoot h u
  let fv : M → ℝ := fun x => |v.toFun x|
  have hfu := dirichletEnergyRoot_memLp h u
  have hfv : MemLp fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
    simpa only [fv, Real.norm_eq_abs] using v.memLp_two.norm
  have hprod : Integrable (fun x => Real.sqrt (max B 0) * (fu x * fv x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
    have hbase' : Integrable (fun x => fu x * fv x)
        (riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
      change Integrable (fu * fv)
        (riemannianVolumeMeasure (I := I_half n) (M := M) h)
      exact hfu.integrable_mul hfv
    exact hbase'.const_mul _
  have hholder : (∫ x, fu x * fv x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)) ≤
      (eLpNorm fu 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal *
      (eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal := by
    have h := DifferentialGeometry.Integral.L2.abs_integral_mul_le_eLpNorm_two hfu hfv
    rw [abs_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))] at h
    exact h
  have hfvnorm : (eLpNorm fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal ≤ ‖v‖ := by
    rw [show eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h) =
      eLpNorm v.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) h) by
      simpa only [fv, Real.norm_eq_abs] using
        (eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) h) v.toFun)]
    exact dirichletScalar_eLpNorm_toReal_le_norm h v
  unfold dirichletDrift
  calc
    |∫ x, h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)| ≤
      ∫ x, |h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x|
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, Real.sqrt (max B 0) * (fu x * fv x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hprod
        (Filter.Eventually.of_forall fun x => by
          change |h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) *
              v.toFun x| ≤ Real.sqrt (max B 0) * (fu x * fv x)
          rw [abs_mul]
          have hmetric :=
            DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
              (I := I_half n) (M := M) h x (X x)
                (gradFun (I := I_half n) h u.toFun x)
          have hroot : Real.sqrt (h.inner x (X x) (X x)) ≤ Real.sqrt (max B 0) := by
            apply Real.sqrt_le_sqrt
            exact (hX x).trans (le_max_left B 0)
          exact (mul_le_mul_of_nonneg_right
            (hmetric.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)))
            (abs_nonneg _)).trans_eq (by
              simp only [fu, fv, dirichletEnergyRoot]
              ring))
    _ = Real.sqrt (max B 0) * (∫ x, fu x * fv x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) h)) := by
      rw [integral_const_mul]
    _ ≤ Real.sqrt (max B 0) *
        ((eLpNorm fu 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal *
        (eLpNorm fv 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) h)).toReal) :=
      mul_le_mul_of_nonneg_left hholder (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (max B 0) * (‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (dirichletEnergyRoot_eLpNorm_toReal_le_norm h u) hfvnorm
          ENNReal.toReal_nonneg (norm_nonneg u)) (Real.sqrt_nonneg _)
    _ = Real.sqrt (max B 0) * ‖u‖ * ‖v‖ := by ring

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
    exact dirichletScalar_eLpNorm_toReal_le_norm (g t) u
  have hfvnorm : (eLpNorm fv 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) (g t))).toReal ≤ ‖v‖ := by
    rw [show eLpNorm fv 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) =
      eLpNorm v.toFun 2
        (riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) by
      simpa only [fv, Real.norm_eq_abs] using
        (eLpNorm_norm (p := 2)
          (μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)) v.toFun)]
    exact dirichletScalar_eLpNorm_toReal_le_norm (g t) v
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

theorem abs_dirichletWeakForm_le_norm
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    (u v : SmoothScalarDirichlet h) :
    |dirichletWeakForm h X a u v| ≤
      (1 + Real.sqrt (max B 0) + |a|) * ‖u‖ * ‖v‖ := by
  have henergy := abs_dirichletEnergy_le_norm h u v
  have hdrift := abs_dirichletDrift_le_norm h X B hX u v
  have hmass := abs_dirichletMass_le_norm h u v
  unfold dirichletWeakForm
  calc
    |-dirichletEnergy h u v + dirichletDrift h X u v -
        a * dirichletMass h u v| ≤
      |dirichletEnergy h u v| + |dirichletDrift h X u v| +
        |a| * |dirichletMass h u v| := by
      calc
        _ ≤ |-dirichletEnergy h u v + dirichletDrift h X u v| +
            |a * dirichletMass h u v| := abs_sub _ _
        _ ≤ (|-dirichletEnergy h u v| + |dirichletDrift h X u v|) +
            |a * dirichletMass h u v| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg, abs_mul]
    _ ≤ ‖u‖ * ‖v‖ + Real.sqrt (max B 0) * ‖u‖ * ‖v‖ +
        |a| * (‖u‖ * ‖v‖) := by
      gcongr
    _ = (1 + Real.sqrt (max B 0) + |a|) * ‖u‖ * ‖v‖ := by ring

private lemma norm_rebaseSmoothScalarDirichlet_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u : SmoothScalarDirichlet q) :
    ‖rebaseSmoothScalarDirichlet h u‖ ≤
      Real.sqrt (Cv.toReal * Cg) * ‖u‖ := by
  let uh := rebaseSmoothScalarDirichlet h u
  have hmass := dirichletMass_self_le_of_volume h Cv hCv0 hCvtop hvol u
  have hsymm : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * h.inner x v v ≤ q.inner x v v ∧
        q.inner x v v ≤ Cg * h.inner x v v := by
    intro x
    exact DifferentialGeometry.Tensor0SBundle.metric_equiv_symm
      (I := I_half n) q h x hCg (hequiv x)
  have henergy := dirichletEnergy_self_le_of_metric_and_volume
    (q := h) q hCg hsymm Cv hCv0 hCvtop hvol uh
  have hmass' : dirichletMass h uh uh ≤ Cv.toReal * dirichletMass q u u := by
    simpa only [uh, rebaseSmoothScalarDirichlet, dirichletMass] using hmass
  have henergy' : dirichletEnergy h uh uh ≤
      Cv.toReal * Cg * dirichletEnergy q u u := by
    simpa only [uh, rebaseSmoothScalarDirichlet, dirichletEnergy] using henergy
  have hhdecomp : ‖uh‖ ^ 2 = dirichletMass h uh uh + dirichletEnergy h uh uh := by
    rw [uh.norm_sq_eq_inner_self]
    rfl
  have hqdecomp : ‖u‖ ^ 2 = dirichletMass q u u + dirichletEnergy q u u := by
    rw [u.norm_sq_eq_inner_self]
    rfl
  have hA : 0 ≤ Cv.toReal * Cg :=
    mul_nonneg ENNReal.toReal_nonneg (le_trans zero_le_one hCg)
  have hsq : ‖uh‖ ^ 2 ≤ Cv.toReal * Cg * ‖u‖ ^ 2 := by
    calc
      ‖uh‖ ^ 2 = dirichletMass h uh uh + dirichletEnergy h uh uh := hhdecomp
      _ ≤ Cv.toReal * dirichletMass q u u +
          Cv.toReal * Cg * dirichletEnergy q u u := add_le_add hmass' henergy'
      _ ≤ Cv.toReal * Cg *
          (dirichletMass q u u + dirichletEnergy q u u) := by
        have hmass0 := dirichletMass_self_nonneg q u
        have hmassle : dirichletMass q u u ≤ Cg * dirichletMass q u u := by
          calc
            dirichletMass q u u = 1 * dirichletMass q u u := by ring
            _ ≤ Cg * dirichletMass q u u :=
              mul_le_mul_of_nonneg_right hCg hmass0
        calc
          Cv.toReal * dirichletMass q u u +
              Cv.toReal * Cg * dirichletEnergy q u u ≤
            Cv.toReal * (Cg * dirichletMass q u u) +
              Cv.toReal * Cg * dirichletEnergy q u u :=
            add_le_add
              (mul_le_mul_of_nonneg_left hmassle ENNReal.toReal_nonneg) le_rfl
          _ = Cv.toReal * Cg *
              (dirichletMass q u u + dirichletEnergy q u u) := by ring
      _ = Cv.toReal * Cg * ‖u‖ ^ 2 := by rw [hqdecomp]
  have hrhs : 0 ≤ Real.sqrt (Cv.toReal * Cg) * ‖u‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (abs_le_of_sq_le_sq' ?_ hrhs).2
  calc
    ‖uh‖ ^ 2 ≤ Cv.toReal * Cg * ‖u‖ ^ 2 := hsq
    _ = (Real.sqrt (Cv.toReal * Cg) * ‖u‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA]

private lemma norm_rebaseSmoothScalarDirichlet_mul_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    ‖rebaseSmoothScalarDirichlet h u‖ * ‖rebaseSmoothScalarDirichlet h v‖ ≤
      Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
  have hu := norm_rebaseSmoothScalarDirichlet_le h hCg hequiv
    Cv hCv0 hCvtop hvol u
  have hv := norm_rebaseSmoothScalarDirichlet_le h hCg hequiv
    Cv hCv0 hCvtop hvol v
  have hA : 0 ≤ Cv.toReal * Cg :=
    mul_nonneg ENNReal.toReal_nonneg (le_trans zero_le_one hCg)
  calc
    ‖rebaseSmoothScalarDirichlet h u‖ * ‖rebaseSmoothScalarDirichlet h v‖ ≤
        (Real.sqrt (Cv.toReal * Cg) * ‖u‖) *
          (Real.sqrt (Cv.toReal * Cg) * ‖v‖) :=
      mul_le_mul hu hv (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
      rw [show Real.sqrt (Cv.toReal * Cg) * ‖u‖ *
          (Real.sqrt (Cv.toReal * Cg) * ‖v‖) =
        Real.sqrt (Cv.toReal * Cg) ^ 2 * ‖u‖ * ‖v‖ by ring,
        Real.sq_sqrt hA]

theorem abs_dirichletMass_le_of_metric_and_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    |dirichletMass h u v| ≤ Cv.toReal * Cg * ‖u‖ * ‖v‖ := by
  let uh := rebaseSmoothScalarDirichlet h u
  let vh := rebaseSmoothScalarDirichlet h v
  have hsame := abs_dirichletMass_le_norm h uh vh
  have hnorm := norm_rebaseSmoothScalarDirichlet_mul_le h hCg hequiv
    Cv hCv0 hCvtop hvol u v
  simpa only [uh, vh, rebaseSmoothScalarDirichlet, dirichletMass] using
    hsame.trans hnorm

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
  let uh := rebaseSmoothScalarDirichlet (g t) u
  let vh := rebaseSmoothScalarDirichlet (g t) v
  have hsame := abs_dirichletMassVariation_le_norm g t B htrace uh vh
  have hnorm := norm_rebaseSmoothScalarDirichlet_mul_le (g t) hCg hequiv
    Cv hCv0 hCvtop hvol u v
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

theorem abs_dirichletWeakForm_le_of_metric_and_volume
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a B : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ B)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ x : M, ∀ v : TangentSpace (I_half n) x,
      Cg⁻¹ * q.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I_half n) (M := M) h ≤
      Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (u v : SmoothScalarDirichlet q) :
    |dirichletWeakForm h X a u v| ≤
      (1 + Real.sqrt (max B 0) + |a|) * (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by
  let uh := rebaseSmoothScalarDirichlet h u
  let vh := rebaseSmoothScalarDirichlet h v
  have hsame := abs_dirichletWeakForm_le_norm h X a B hX uh vh
  have hnorm := norm_rebaseSmoothScalarDirichlet_mul_le h hCg hequiv
    Cv hCv0 hCvtop hvol u v
  calc
    |dirichletWeakForm h X a u v| = |dirichletWeakForm h X a uh vh| := by
      rfl
    _ ≤ (1 + Real.sqrt (max B 0) + |a|) * ‖uh‖ * ‖vh‖ := hsame
    _ ≤ (1 + Real.sqrt (max B 0) + |a|) *
        (Cv.toReal * Cg * ‖u‖ * ‖v‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hnorm
        (add_nonneg
          (add_nonneg zero_le_one (Real.sqrt_nonneg (max B 0))) (abs_nonneg a))
    _ = (1 + Real.sqrt (max B 0) + |a|) *
        (Cv.toReal * Cg) * ‖u‖ * ‖v‖ := by ring

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
