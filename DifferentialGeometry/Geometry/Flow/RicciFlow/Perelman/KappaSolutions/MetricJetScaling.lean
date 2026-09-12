import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance metricJetComplete : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance metricJetC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance metricJetC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance metricJetCInfSucc : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

private theorem metricJet_tensorField_scale (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) :
    metricTensorField (I := I) (scaleMetric c hc g) = c • metricTensorField (I := I) g := by
  apply DFunLike.ext
  intro x
  apply Tensor0SBundle.tensor0SSpace_ext
  intro v
  simp only [metricTensorField_apply, scaleMetric_inner,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul]

variable [T2Space M]

private theorem metricJet_step_scale_reference (c : ℝ) (hc : 0 < c)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ)
    (A : Tensor0SField (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) (scaleMetric c hc gRef) a A =
      metricCovDerivStep (I := I) gRef a A := by
  apply DFunLike.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply, lcConn_scaleMetric]

private theorem metricJet_covDeriv_scale_reference (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) g (scaleMetric c hc gRef) a =
      metricCovDeriv (I := I) g gRef a := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [metricCovDeriv_succ, metricCovDeriv_succ, ih, metricJet_step_scale_reference]

private theorem metricJet_covDeriv_scale_metric (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) (scaleMetric c hc g) gRef a =
      c • metricCovDeriv (I := I) g gRef a := by
  induction a with
  | zero => exact metricJet_tensorField_scale c hc g
  | succ a ih =>
      rw [metricCovDeriv_succ, metricCovDeriv_succ, ih, metricCovDerivStep_smul]

theorem metricCovDeriv_scale_all (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) (scaleMetric c hc g) (scaleMetric c hc gRef) a =
      c • metricCovDeriv (I := I) g gRef a := by
  rw [metricJet_covDeriv_scale_reference, metricJet_covDeriv_scale_metric]

theorem metricDiffCovDerivAt_scale_all (c : ℝ) (hc : 0 < c)
    (gk gInf gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    metricDiffCovDerivAt (I := I) a
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x =
      c • metricDiffCovDerivAt (I := I) a gk gInf gRef x := by
  unfold metricDiffCovDerivAt
  rw [metricCovDeriv_scale_all, metricCovDeriv_scale_all]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, smul_sub]

theorem metricDerivNorm_scale_all (c : ℝ) (hc : 0 < c)
    (gk gInf gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    metricDerivNorm (I := I) a
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x =
      Real.sqrt ((c⁻¹) ^ a) * metricDerivNorm (I := I) a gk gInf gRef x := by
  have hweight : (c⁻¹) ^ (a + 2) * c ^ 2 = (c⁻¹) ^ a := by
    calc
      (c⁻¹) ^ (a + 2) * c ^ 2 = (c⁻¹) ^ a * ((c⁻¹ * c) ^ 2) := by
        rw [pow_add, mul_pow]
        ring
      _ = (c⁻¹) ^ a := by rw [inv_mul_cancel₀ hc.ne']; simp only [one_pow, mul_one]
  unfold metricDerivNorm
  rw [metricDiffCovDerivAt_scale_all, normSq0S_scale, normSq0S_smul,
    ← mul_assoc, hweight, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hc.le) a)]

def metricJetScaleLoss (c : ℝ) (p : ℕ) : ℝ :=
  1 + ∑ a ∈ Finset.range (p + 1), Real.sqrt ((c⁻¹) ^ a)

theorem metricJetScaleLoss_pos (c : ℝ) (p : ℕ) : 0 < metricJetScaleLoss c p := by
  dsimp only [metricJetScaleLoss]
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

private theorem metricJet_weight_le_loss (c : ℝ) {a p : ℕ} (ha : a ≤ p) :
    Real.sqrt ((c⁻¹) ^ a) ≤ metricJetScaleLoss c p := by
  have hsum := Finset.single_le_sum
    (fun j (_hj : j ∈ Finset.range (p + 1)) => Real.sqrt_nonneg ((c⁻¹) ^ j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
  dsimp only [metricJetScaleLoss]
  linarith

theorem metricDerivNormSupOn_scale_all_le (c : ℝ) (hc : 0 < c)
    {K : Set M} (hK : IsCompact K) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K p
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) ≤
      metricJetScaleLoss c p * metricDerivNormSupOn (I := I) K p gk gInf gRef := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [metricDerivNormSupOn]
  · obtain ⟨x₀, hx₀⟩ := hne
    unfold metricDerivNormSupOn
    apply csSup_le
    · exact ⟨_, 0, Nat.zero_le p, x₀, hx₀, rfl⟩
    · rintro r ⟨a, hap, x, hx, rfl⟩
      change metricDerivNorm (I := I) a
          (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x ≤
        metricJetScaleLoss c p * metricDerivNormSupOn (I := I) K p gk gInf gRef
      rw [metricDerivNorm_scale_all]
      exact (mul_le_mul_of_nonneg_right (metricJet_weight_le_loss c hap)
        (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (derivNorm_le_sup hK hap gk gInf gRef hx)
          (metricJetScaleLoss_pos c p).le)

theorem metricCPConvOn_scale_all (c : ℝ) (hc : 0 < c)
    {K : Set M} (hK : IsCompact K) (p : ℕ)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCPConvergenceOn (I := I) K p gSeq gInf gRef) :
    MetricCPConvergenceOn (I := I) K p (fun k => scaleMetric c hc (gSeq k))
      (scaleMetric c hc gInf) (scaleMetric c hc gRef) := by
  intro epsilon hepsilon
  let A := metricJetScaleLoss c p
  have hA : 0 < A := metricJetScaleLoss_pos c p
  obtain ⟨k₀, hk₀⟩ := hconv (epsilon / A) (div_pos hepsilon hA)
  refine ⟨k₀, fun k hk => ?_⟩
  calc
    metricDerivNormSupOn (I := I) K p
        (scaleMetric c hc (gSeq k)) (scaleMetric c hc gInf) (scaleMetric c hc gRef) ≤
      A * metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef :=
        metricDerivNormSupOn_scale_all_le c hc hK p (gSeq k) gInf gRef
    _ < A * (epsilon / A) := mul_lt_mul_of_pos_left (hk₀ k hk) hA
    _ = epsilon := by field_simp [hA.ne']

theorem metricCInfConvOnCompacts_scale_all (c : ℝ) (hc : 0 < c)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef) :
    MetricCInfConvergenceOnCompacts (I := I) (fun k => scaleMetric c hc (gSeq k))
      (scaleMetric c hc gInf) (scaleMetric c hc gRef) := by
  intro K hK p
  exact metricCPConvOn_scale_all c hc hK p gSeq gInf gRef (hconv K hK p)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
