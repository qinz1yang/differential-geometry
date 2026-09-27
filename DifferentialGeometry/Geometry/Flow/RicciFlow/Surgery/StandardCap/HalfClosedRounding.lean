import DifferentialGeometry.Geometry.Metric.HalfClosedNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CurvatureRounding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RoundingJets
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev cylinder := roundCylinderMetric (E := E3) (n := 2)
private abbrev D (A : ℝ) := (univ : Set S2) ×ˢ Ioc (-A) 0
private theorem factor_smooth : ContMDiff IC 𝓘(ℝ) ∞
    (fun q : S2 × ℝ => conformalFactor q.2) :=
  contDiff_conformalFactor.contMDiff.comp contMDiff_snd
private theorem interior_subset (A : ℝ) : (roundingCollar A : Set (S2 × ℝ)) ⊆ D A :=
  fun _q hq => ⟨mem_univ _, hq.1, hq.2.le⟩

def roundingMetricOn {A : ℝ} (h : SmoothRiemannianMetricOn (I := IC) (D A)) :
    SmoothRiemannianMetricOn (I := IC) (D A) :=
  h.conformal (fun q : S2 × ℝ => conformalFactor q.2) factor_smooth.contMDiffOn

@[simp] theorem roundingMetricOn_inner {A : ℝ}
    (h : SmoothRiemannianMetricOn (I := IC) (D A)) (q : S2 × ℝ)
    (v w : TangentSpace IC q) :
    (roundingMetricOn h).inner q v w = Real.exp (2 * conformalFactor q.2) * h.inner q v w := rfl

theorem roundingMetricOn_restrictOpen {A : ℝ}
    (h : SmoothRiemannianMetricOn (I := IC) (D A)) :
    (roundingMetricOn h).restrictOpen (roundingCollar A) (interior_subset A) =
      roundingMetric A (h.restrictOpen (roundingCollar A) (interior_subset A)) := by
  exact h.conformal_restrictOpen (fun q : S2 × ℝ => conformalFactor q.2)
    factor_smooth.contMDiffOn (roundingCollar A) (interior_subset A)

theorem halfClosedCovDeriv_roundingMetricOn_eq_at_height_zero {A : ℝ}
    (h : SmoothRiemannianMetricOn (I := IC) (D A))
    (gRef : SmoothRiemannianMetric IC (S2 × ℝ))
    (q : S2 × ℝ) (hq : q ∈ D A) (hz : q.2 = 0) (m : ℕ) :
    (roundingMetricOn h).halfClosedCovDeriv gRef m q hq =
      h.halfClosedCovDeriv gRef m q hq := by
  obtain ⟨U, hqU, _, k, hk⟩ :=
    exists_local_metric_extension_of_halfClosed_cylinder_section
      h.inner h.contMDiffOn h.symm h.pos q hq
  let F : U → ℝ := fun y => conformalFactor (y : S2 × ℝ).2
  have hF : ContMDiff IC 𝓘(ℝ) ∞ F :=
    factor_smooth.comp (contMDiff_subtype_val (I := IC) (U := U))
  let kt := conformalMetricOfContDiff k F hF
  have hkt : ∀ y : U, (y : S2 × ℝ) ∈ D A → ∀ v w : TangentSpace IC y,
      kt.inner y v w = (roundingMetricOn h).inner (y : S2 × ℝ) v w := by
    intro y hy v w
    exact (conformalMetricOfContDiff_inner k F hF y v w).trans
      ((congrArg (fun a : ℝ => Real.exp (2 * F y) * a) (hk y hy v w)).trans
        (roundingMetricOn_inner h (y : S2 × ℝ) v w).symm)
  rw [(roundingMetricOn h).halfClosedCovDeriv_eq_local gRef U kt hkt m q hq hqU,
    h.halfClosedCovDeriv_eq_local gRef U k hk m q hq hqU]
  exact metricCovDeriv_conformalFactor_eq_at_height_zero U k (gRef.restrictOpen U)
    ⟨q, hqU⟩ hz m

theorem halfClosedDerivENormSup_eq_roundingCollar {A : ℝ}
    (h : SmoothRiemannianMetricOn (I := IC) (D A)) (p : ℕ) :
    h.halfClosedDerivENormSup cylinder cylinder p =
      metricDerivENormSupOn univ p
        (h.restrictOpen (roundingCollar A) (interior_subset A))
        (roundingReference A) (roundingReference A) := by
  apply h.halfClosedDerivENormSup_eq_interior cylinder cylinder p (roundingCollar A)
  ext q
  change q.2 ∈ Ioo (-A) 0 ↔ q.1 ∈ (univ : Set S2) ∧ q.2 ∈ Ioo (-A) 0
  simp only [mem_univ, true_and]

theorem exists_conformal_rounding :
    ∃ εrd crd A : ℝ, 0 < εrd ∧ 0 < crd ∧ 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ q : S2 × ℝ, q.2 ∈ Ico (-2 * A) 0 → ∀ u v : E3,
        metric.inner (conformalChart q : E3) u u *
          metric.inner (conformalChart q : E3) v v -
          (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0 →
        0 < sectionalCurvature metric (conformalChart q : E3) u v) ∧
      (∀ z ∈ Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            εrd * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < εrd ∧
      ∀ h : SmoothRiemannianMetricOn (I := IC) (D A),
        h.halfClosedDerivENormSup cylinder cylinder 2 < ENNReal.ofReal εrd →
        let g := h.restrictOpen (roundingCollar A) (interior_subset A)
        let gRound := (roundingMetricOn h).restrictOpen (roundingCollar A) (interior_subset A)
        (∀ x : roundingCollar A,
          metricScalarAt g x + crd * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) ≤
              metricScalarAt gRound x ∧
            2 * leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) +
                crd * (-deriv (deriv conformalFactor) (x : S2 × ℝ).2) ≤
              2 * leastCurvatureOperatorEigenvalueAt gRound x
                (metricAlgebraicCurvatureTensorAt gRound x)) ∧
          ∀ (gRef : SmoothRiemannianMetric IC (S2 × ℝ))
            (q : S2 × ℝ) (hq : q ∈ D A), q.2 = 0 → ∀ m : ℕ,
            (roundingMetricOn h).halfClosedCovDeriv gRef m q hq =
              h.halfClosedCovDeriv gRef m q hq := by
  obtain ⟨A, hA, hAsmall, hplanes, hprofile, hnorm, hgain⟩ :=
    exists_curvature_rounding_collar (η := (1 / 100000000 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨1 / 100000000, 1 / 2, A, by norm_num, by norm_num,
    hA, hAsmall, hplanes, hprofile, hnorm, ?_⟩
  intro h hclose
  have hi : metricDerivENormSupOn univ 2
      (h.restrictOpen (roundingCollar A) (interior_subset A))
      (roundingReference A) (roundingReference A) < ENNReal.ofReal (1 / 100000000 : ℝ) := by
    rw [← halfClosedDerivENormSup_eq_roundingCollar h 2]
    exact hclose
  constructor
  · intro x
    simpa only [roundingMetricOn_restrictOpen, div_eq_mul_inv, mul_comm, one_mul] using
      hgain (h.restrictOpen (roundingCollar A) (interior_subset A)) hi x
  · intro gRef q hq hz m
    exact halfClosedCovDeriv_roundingMetricOn_eq_at_height_zero h gRef q hq hz m

end DifferentialGeometry.PDE.RicciFlow.StandardCap
