import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section MetricReferenceSwap

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricDerivNorm_succ_self_reference
    (A gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    metricDerivNorm (I := I) (a + 1) A gRef gRef x =
      metricCovDerivNorm (I := I) (a + 1) A gRef x := by
  unfold metricDerivNorm metricDiffCovDerivAt metricCovDerivNorm
  rw [covDeriv_self_succ (I := I) gRef a]
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sub_zero,
    Tensor0SBundle.normSq0S_eq_inner]

section ReferenceSwap

variable [IsManifold I 1 M] [IsManifold I 2 M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricDerivNorm_le_of_reference_swap
    {u : Set M} (hu : IsOpen u)
    (A gInf g₁ g₀ : SmoothRiemannianMetric I M) (p : ℕ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * g₀.inner x v v ≤ g₁.inner x v v ∧
        g₁.inner x v v ≤ (1 + eps) * g₀.inner x v v)
    (hcov : ∀ x ∈ u, ∀ q : ℕ, 1 ≤ q → q ≤ p →
      metricDerivNorm (I := I) q g₁ g₀ g₀ x ≤ eps)
    {r : ℕ} (hr0 : 0 < r) (hrp : r ≤ p) {x : M} (hx : x ∈ u) :
    metricDerivNorm (I := I) r A gInf g₁ x ≤
      Real.sqrt ((1 + eps) ^ (2 + r)) *
        (metricDerivNorm (I := I) r A gInf g₀ x +
          eps * metricCovariantDerivativeComparisonConstant (E := E) 2 p *
            ∑ k ∈ Finset.range r, metricDerivNorm (I := I) k A gInf g₀ x) :=
  metric_deriv_norm_change_le (I := I) hu A gInf g₁ g₀ p r eps heps0 heps1
    hequiv hcov x hx hr0 hrp

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricDerivNorm_le_of_reference_swap_of_covDerivNorm
    {u : Set M} (hu : IsOpen u)
    (A gInf g₁ g₀ : SmoothRiemannianMetric I M) (p : ℕ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * g₀.inner x v v ≤ g₁.inner x v v ∧
        g₁.inner x v v ≤ (1 + eps) * g₀.inner x v v)
    (hcov : ∀ x ∈ u, ∀ q : ℕ, 1 ≤ q → q ≤ p →
      metricCovDerivNorm (I := I) q g₁ g₀ x ≤ eps)
    {r : ℕ} (hr0 : 0 < r) (hrp : r ≤ p) {x : M} (hx : x ∈ u) :
    metricDerivNorm (I := I) r A gInf g₁ x ≤
      Real.sqrt ((1 + eps) ^ (2 + r)) *
        (metricDerivNorm (I := I) r A gInf g₀ x +
          eps * metricCovariantDerivativeComparisonConstant (E := E) 2 p *
            ∑ k ∈ Finset.range r, metricDerivNorm (I := I) k A gInf g₀ x) := by
  refine metricDerivNorm_le_of_reference_swap (I := I) hu A gInf g₁ g₀ p
    heps0 heps1 hequiv (fun y hy q hq1 hqp => ?_) hr0 hrp hx
  have hq : q - 1 + 1 = q := Nat.sub_add_cancel hq1
  rw [← hq, metricDerivNorm_succ_self_reference (I := I) g₁ g₀ (q - 1) y, hq]
  exact hcov y hy q hq1 hqp

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricDerivNormSupOn_le_of_reference_swap_of_covDerivNorm
    {K : Set M} (hK : IsCompact K) {u : Set M} (hu : IsOpen u) (hKu : K ⊆ u)
    (A gInf g₁ g₀ : SmoothRiemannianMetric I M) (p : ℕ) {eps c : ℝ}
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) (hc : 0 ≤ c)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * g₀.inner x v v ≤ g₁.inner x v v ∧
        g₁.inner x v v ≤ (1 + eps) * g₀.inner x v v)
    (hcov : ∀ x ∈ u, ∀ q : ℕ, 1 ≤ q → q ≤ p →
      metricCovDerivNorm (I := I) q g₁ g₀ x ≤ eps)
    (hconv : ∀ r : ℕ, r ≤ p → metricDerivNormSupOn (I := I) K r A gInf g₀ ≤ c) :
    metricDerivNormSupOn (I := I) K p A gInf g₁ ≤
      Real.sqrt ((1 + eps) ^ (2 + p)) *
        (1 + eps * metricCovariantDerivativeComparisonConstant (E := E) 2 p *
          ((p : ℝ) + 1)) * c := by
  set D : ℝ := metricCovariantDerivativeComparisonConstant (E := E) 2 p with hD
  have hD0 : 0 ≤ D := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
  have h1eps : (1 : ℝ) ≤ 1 + eps := by linarith
  have hfac1 : (1 : ℝ) ≤ 1 + eps * D * ((p : ℝ) + 1) := by
    have hpp : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
    nlinarith [mul_nonneg heps0 hD0]
  have hbase : (0 : ℝ) ≤ Real.sqrt ((1 + eps) ^ (2 + p)) := Real.sqrt_nonneg _
  refine metricDerivNormSupOn_le_of_forall (I := I) K p A gInf g₁ _
    (mul_nonneg (mul_nonneg hbase (le_trans zero_le_one hfac1)) hc) ?_
  intro a hap x hx
  have hxu : x ∈ u := hKu hx
  have hpoint (r : ℕ) (hrp : r ≤ p) :
      metricDerivNorm (I := I) r A gInf g₀ x ≤ c :=
    le_trans (derivNorm_le_sup (I := I) (a := r) (p := r) hK (le_refl r) A gInf g₀ hx)
      (hconv r hrp)
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have hzero := diffNorm_zero_change (I := I) A gInf g₁ g₀ x h1eps (hequiv x hxu)
    have hsq : Real.sqrt ((1 + eps) ^ 2) = 1 + eps := by
      rw [Real.sqrt_sq (by linarith)]
    rw [hsq] at hzero
    refine le_trans hzero ?_
    have hle : (1 + eps) ≤ Real.sqrt ((1 + eps) ^ (2 + p)) := by
      calc (1 + eps) = Real.sqrt ((1 + eps) ^ 2) :=
            (Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + eps)).symm
        _ ≤ Real.sqrt ((1 + eps) ^ (2 + p)) :=
            Real.sqrt_le_sqrt (pow_le_pow_right₀ h1eps (by omega))
    have h0le : metricDerivNorm (I := I) 0 A gInf g₀ x ≤ c := hpoint 0 (Nat.zero_le p)
    calc (1 + eps) * metricDerivNorm (I := I) 0 A gInf g₀ x
          ≤ (1 + eps) * c := mul_le_mul_of_nonneg_left h0le (by linarith)
      _ ≤ Real.sqrt ((1 + eps) ^ (2 + p)) * c :=
          mul_le_mul_of_nonneg_right hle hc
      _ ≤ Real.sqrt ((1 + eps) ^ (2 + p)) *
            (1 + eps * D * ((p : ℝ) + 1)) * c := by
          have hfac : (1 : ℝ) ≤ 1 + eps * D * ((p : ℝ) + 1) := hfac1
          nlinarith [hbase, hc, mul_nonneg hbase hc, hfac]
  · have hstep := metricDerivNorm_le_of_reference_swap_of_covDerivNorm (I := I)
      (eps := eps) hu A gInf g₁ g₀ p heps0 heps1 hequiv hcov
      (r := a) hpos hap (x := x) hxu
    refine le_trans hstep ?_
    have hsum : ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x ≤
        ((a : ℝ)) * c := by
      have hb : ∀ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x ≤ c :=
        fun k hk => hpoint k (le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hap)
      have h1 := Finset.sum_le_card_nsmul (Finset.range a) _ c hb
      rwa [Finset.card_range, nsmul_eq_mul] at h1
    have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x :=
      Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
    have hap' : (a : ℝ) ≤ (p : ℝ) := by exact_mod_cast hap
    have hbracket :
        metricDerivNorm (I := I) a A gInf g₀ x +
          eps * D * ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x ≤
        (1 + eps * D * ((p : ℝ) + 1)) * c := by
      have h1 : metricDerivNorm (I := I) a A gInf g₀ x ≤ c := hpoint a hap
      have h2 : eps * D * ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x ≤
          eps * D * (((a : ℝ)) * c) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        exact mul_nonneg heps0 hD0
      have h3 : eps * D * (((a : ℝ)) * c) ≤ eps * D * (((p : ℝ) + 1) * c) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg heps0 hD0)
        nlinarith [hc, hap', heps0, hD0]
      nlinarith [h1, h2, h3, hc, heps0, hD0, hbase]
    have hX0 : (0 : ℝ) ≤ metricDerivNorm (I := I) a A gInf g₀ x +
        eps * D * ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg heps0 hD0) hsum0)
    have hfa : Real.sqrt ((1 + eps) ^ (2 + a)) ≤ Real.sqrt ((1 + eps) ^ (2 + p)) :=
      Real.sqrt_le_sqrt (pow_le_pow_right₀ h1eps (by omega))
    calc Real.sqrt ((1 + eps) ^ (2 + a)) *
          (metricDerivNorm (I := I) a A gInf g₀ x +
            eps * D * ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x)
        ≤ Real.sqrt ((1 + eps) ^ (2 + p)) *
          (metricDerivNorm (I := I) a A gInf g₀ x +
            eps * D * ∑ k ∈ Finset.range a, metricDerivNorm (I := I) k A gInf g₀ x) :=
          mul_le_mul_of_nonneg_right hfa hX0
      _ ≤ Real.sqrt ((1 + eps) ^ (2 + p)) *
            ((1 + eps * D * ((p : ℝ) + 1)) * c) :=
          mul_le_mul_of_nonneg_left hbracket hbase
      _ = Real.sqrt ((1 + eps) ^ (2 + p)) *
            (1 + eps * D * ((p : ℝ) + 1)) * c := by ring

end ReferenceSwap

end MetricReferenceSwap

section CanonicalSourceData

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {phi : ℕ → ℕ}

omit [I.Boundaryless] in
theorem exists_metricConvergenceData_canonicalSourceData
    (Ψ : PointedRiemannianConvergenceMaps (I := I) X L phi)
    (hconv : ∀ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k).derivNormSupOn
          (I := I) K p < ε) :
    ∃ C : MetricConvergenceData (I := I) Ψ,
      (∀ k : ℕ, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k) ∧
      (∀ k : ℕ,
        let D := C.domain k
        letI : TopologicalSpace (MetricSourceDomain (I := I) Ψ k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain (I := I) Ψ k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain (I := I) Ψ k) := D.smooth
        D.referenceMetric = D.limitMetric) := by
  classical
  refine ⟨⟨fun k => CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k,
    fun K hK p ε hε => ?_⟩, fun k => rfl, fun k => ?_⟩
  · obtain ⟨k0, hk0⟩ := hconv K hK p ε hε
    obtain ⟨kS, hS⟩ := Ψ.source_subset hK
    refine ⟨max kS k0, fun k hk => ⟨hS k (le_trans (Nat.le_max_left _ _) hk),
      hk0 k (le_trans (Nat.le_max_right _ _) hk)⟩⟩
  · with_unfolding_all
    rfl

end CanonicalSourceData

section SourceReferenceSwap

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {phi : ℕ → ℕ}

namespace MetricSourceData

noncomputable def withReference
    {Ψ : PointedRiemannianConvergenceMaps (I := I) X L phi} {k : ℕ}
    (D : MetricSourceData (I := I) Ψ k)
    (gRef : letI : TopologicalSpace (MetricSourceDomain (I := I) Ψ k) := D.topology
            letI : ChartedSpace H (MetricSourceDomain (I := I) Ψ k) := D.charted
            letI : IsManifold I ∞ (MetricSourceDomain (I := I) Ψ k) := D.smooth
            SmoothRiemannianMetric I (MetricSourceDomain (I := I) Ψ k)) :
    MetricSourceData (I := I) Ψ k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := gRef
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

end MetricSourceData

end SourceReferenceSwap

end CheegerGromovCompactness
end DifferentialGeometry
