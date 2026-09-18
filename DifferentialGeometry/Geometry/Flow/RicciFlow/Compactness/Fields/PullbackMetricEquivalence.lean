import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    {L : ℝ} (hL : 1 ≤ L)
    (hEqInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ∀ t ∈ Icc a b, MetricUniformEquivalentOn (I := I) K R (co.gInf t) L) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn (I := I) K R
        (gSeqExt Φ R bf hsrc htgt (co.φ k) t) (2 * L) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have heps : 0 < (2 * L)⁻¹ :=
    inv_pos.mpr (mul_pos (by norm_num) hLpos)
  have hinv : L⁻¹ = 2 * (2 * L)⁻¹ := by
    rw [mul_inv_rev]
    ring
  obtain ⟨N, hN⟩ := co.convergencePt K hK 0 ((2 * L)⁻¹) heps
  refine ⟨N, ?_⟩
  intro k hk t ht
  refine ⟨by linarith, ?_⟩
  intro x hx v
  have hR : 0 ≤ R.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (R.pos x v hv).le
  have herror :
      |(gSeqExt Φ R bf hsrc htgt (co.φ k) t).inner x v v -
        (co.gInf t).inner x v v| ≤ (2 * L)⁻¹ * R.inner x v v := by
    have hbound := metricDifference_abs_le
      (gSeqExt Φ R bf hsrc htgt (co.φ k) t) (co.gInf t) R x v v
    rw [mul_assoc, Real.mul_self_sqrt hR] at hbound
    exact hbound.trans
      (mul_le_mul_of_nonneg_right (hN k hk t ht 0 le_rfl x hx).le hR)
  obtain ⟨hlower, hupper⟩ := (hEqInf t ht).2 x hx v
  have herrorNonneg := (abs_nonneg _).trans herror
  obtain ⟨herrorLower, herrorUpper⟩ := abs_le.mp herror
  rw [hinv] at hlower
  constructor <;> linarith

end DifferentialGeometry.CheegerGromovCompactness
