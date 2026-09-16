import DifferentialGeometry.Analysis.ODE.Gronwall.Backward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance terminalCovEvolutionComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

theorem metric_covariant_derivative_bound_from_terminal_value_of_evolution
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) {c b : ℝ}
    (gRef : SmoothRiemannianMetric I M) (U : Set M) (hU : IsOpen U)
    (N : ℕ) (hN : 1 ≤ N) (Bmax : ℝ) (hBmax : 1 ≤ Bmax)
    (hequiv : ∀ i, ∀ t ∈ Icc c b, MetricUniformEquivalentOn U gRef (gSeq i t) Bmax)
    (Cg : ℕ → ℝ)
    (hprev : ∀ r : ℕ, 1 ≤ r → r < N → ∀ i, ∀ t ∈ Icc c b, ∀ x ∈ U,
      metricCovDerivNorm r (gSeq i t) gRef x ≤ Cg r)
    (KShi : ℝ) (hKShi : 0 ≤ KShi)
    (hShi : MovingShiBoundOn U c b gSeq N KShi)
    (A : ℝ) (hA : 0 ≤ A)
    (hinit : ∀ i, ∀ x ∈ U, metricCovDerivNorm N (gSeq i b) gRef x ≤ A)
    (hcont : ∀ i, ∀ x ∈ U,
      ContinuousOn (fun t => metricCovDerivNorm N (gSeq i t) gRef x) (Icc c b))
    (hev : ∀ i, ∀ x ∈ U, ∀ s ∈ Ioo c b,
      ∀ v : Fin (N + 2) → TangentSpace I x,
        HasDerivAt (fun r => metricCovDeriv (gSeq i r) gRef N x v)
          (((-2 : ℝ) • nablaRicReal gSeq gRef N i s x) v) s) :
    ∀ i, ∀ t ∈ Icc c b, ∀ x ∈ U,
      metricCovDerivNorm N (gSeq i t) gRef x ≤
        metricCovOrderEvolutionConstant
          (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).slope
          (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).offset (b - c) A := by
  let C := (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).slope
  let B := (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).offset
  have hCB := ricCoeffs_nonneg (Module.finrank ℝ E) N Bmax Cg KShi hBmax hKShi
  have hric := ric_bound_field_on (I := I) hU N hN Bmax hBmax hequiv
    Cg hprev KShi hKShi hShi
  intro i t ht x hx
  let u := fun s => metricCovDerivNorm N (gSeq i s) gRef x ^ 2
  have hu : ContinuousOn u (Icc c b) := by
    exact (hcont i x hx).pow 2
  have hα : 0 < metricCovOrderEvolutionAlpha C := by
    unfold metricCovOrderEvolutionAlpha
    nlinarith [sq_nonneg C]
  have hβ : 0 ≤ metricCovOrderEvolutionBeta B := by
    unfold metricCovOrderEvolutionBeta
    positivity
  have hd : ∀ s ∈ Ioo c b, ∃ d, HasDerivAt u d s ∧
      -(metricCovOrderEvolutionAlpha C * u s + metricCovOrderEvolutionBeta B) ≤ d := by
    intro s hs
    have hnorm := normsq_evolution_of_comp (I := I) (K := U)
      (β := s) (ψ := s) (gSeq := gSeq)
      (fun j y hy r hr v => by
        have hrs : r = s := le_antisymm hr.2 hr.1
        subst r
        exact hev j y hy s hs v)
    obtain ⟨d, hd, hb⟩ := hnorm i x hx s ⟨le_rfl, le_rfl⟩
    refine ⟨d, hd, ?_⟩
    have hq := hric i s (Ioo_subset_Icc_self hs) x hx
    let q := Real.sqrt (normSq0S gRef x (N + 2)
      (nablaRicReal gSeq gRef N i s x))
    let y := metricCovDerivNorm N (gSeq i s) gRef x
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    have hqle : q ≤ C * y + B := hq
    have hqsq : q ^ 2 ≤ (C * y + B) ^ 2 :=
      (sq_le_sq₀ hq0 (add_nonneg (mul_nonneg hCB.1 hy0) hCB.2)).mpr hqle
    have hYoung : (C * y + B) ^ 2 ≤ 2 * (C * y) ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (C * y - B)]
    have hbd : -(y ^ 2 + (2 * q) ^ 2) ≤ d := by
      have hh := neg_abs_le d
      change |d| ≤ y ^ 2 + (2 * q) ^ 2 at hb
      linarith
    change -((1 + 8 * C ^ 2) * y ^ 2 + (8 * B ^ 2 + 1)) ≤ d
    nlinarith [hqsq, hYoung]
  have hh := DifferentialGeometry.Analysis.affine_bound_backward_closed u (α := metricCovOrderEvolutionAlpha C)
    (β := metricCovOrderEvolutionBeta B) hα hβ hu (sq_nonneg _) hd t ht
  have hinitSq : u b ≤ A ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hA).mpr (hinit i x hx)
  have hsq := hh.trans (mul_le_mul_of_nonneg_left
    (show u b + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C ≤
      A ^ 2 + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C by linarith)
      (Real.exp_pos _).le)
  change metricCovDerivNorm N (gSeq i t) gRef x ≤
    Real.sqrt (Real.exp (metricCovOrderEvolutionAlpha C * (b - c)) *
      (A ^ 2 + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C))
  exact (Real.le_sqrt (Real.sqrt_nonneg _) (by positivity)).mpr hsq

theorem exists_metric_covariant_derivative_bounds_from_terminal_values_of_evolution
    {c b : ℝ} (gRef : SmoothRiemannianMetric I M) (U : Set M) (hU : IsOpen U)
    (N : ℕ) (Bmax : ℝ) (hBmax : 1 ≤ Bmax)
    (KShi : ℝ) (hKShi : 0 ≤ KShi) (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M),
      (∀ i, ∀ t ∈ Icc c b, MetricUniformEquivalentOn U gRef (gSeq i t) Bmax) →
      MovingShiBoundOn U c b gSeq N KShi →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i b) gRef x ≤ A q) →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U,
        ContinuousOn (fun t => metricCovDerivNorm q (gSeq i t) gRef x) (Icc c b)) →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U, ∀ s ∈ Ioo c b,
        ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt (fun r => metricCovDeriv (gSeq i r) gRef q x v)
            (((-2 : ℝ) • nablaRicReal gSeq gRef q i s x) v) s) →
      ∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ t ∈ Icc c b, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i t) gRef x ≤ C q := by
  let Stable := fun (q : ℕ) (Cq : ℝ) =>
    ∀ (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M),
      (∀ i, ∀ t ∈ Icc c b, MetricUniformEquivalentOn U gRef (gSeq i t) Bmax) →
      MovingShiBoundOn U c b gSeq N KShi →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i b) gRef x ≤ A q) →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U,
        ContinuousOn (fun t => metricCovDerivNorm q (gSeq i t) gRef x) (Icc c b)) →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U, ∀ s ∈ Ioo c b,
        ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt (fun r => metricCovDeriv (gSeq i r) gRef q x v)
            (((-2 : ℝ) • nablaRicReal gSeq gRef q i s x) v) s) →
      ∀ i, ∀ t ∈ Icc c b, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i t) gRef x ≤ Cq
  have hmain : ∀ r : ℕ, 1 ≤ r → r ≤ N → ∃ Cr : ℝ, 0 ≤ Cr ∧ Stable r Cr := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ihr =>
      intro hr1 hrN
      have hex : ∀ q : ℕ, ∃ Cq : ℝ, 1 ≤ q → q < r → Stable q Cq := by
        intro q
        by_cases hq : 1 ≤ q ∧ q < r
        · obtain ⟨Cq, _, hCq⟩ := ihr q hq.2 hq.1 (hq.2.le.trans hrN)
          exact ⟨Cq, fun _ _ => hCq⟩
        · exact ⟨0, fun ha hb => absurd ⟨ha, hb⟩ hq⟩
      choose Cg hCg using hex
      refine ⟨metricCovOrderEvolutionConstant
        (ricTowerCoeffs (Module.finrank ℝ E) r Bmax Cg KShi).slope
        (ricTowerCoeffs (Module.finrank ℝ E) r Bmax Cg KShi).offset (b - c) (A r),
        Real.sqrt_nonneg _, ?_⟩
      intro gSeq hequiv hShi hinit hcont hev
      exact metric_covariant_derivative_bound_from_terminal_value_of_evolution
        gSeq gRef U hU r hr1 Bmax hBmax hequiv Cg
        (fun q hq1 hqr => hCg q hq1 hqr gSeq hequiv hShi hinit hcont hev)
        KShi hKShi (fun q hq => hShi q (hq.trans hrN)) (A r) (hA r)
        (hinit r hr1 hrN) (hcont r hr1 hrN) (hev r hr1 hrN)
  have hex : ∀ q : ℕ, ∃ Cq : ℝ, 0 ≤ Cq ∧ (1 ≤ q → q ≤ N → Stable q Cq) := by
    intro q
    by_cases hq : 1 ≤ q ∧ q ≤ N
    · obtain ⟨Cq, hCq0, hCq⟩ := hmain q hq.1 hq.2
      exact ⟨Cq, hCq0, fun _ _ => hCq⟩
    · exact ⟨0, le_rfl, fun ha hb => absurd ⟨ha, hb⟩ hq⟩
  choose C hC0 hC using hex
  refine ⟨C, hC0, ?_⟩
  intro gSeq hequiv hShi hinit hcont hev q hq1 hqN
  exact hC q hq1 hqN gSeq hequiv hShi hinit hcont hev

end DifferentialGeometry.PDE.RicciFlow
