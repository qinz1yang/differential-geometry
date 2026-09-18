import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TerminalLocalSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TerminalTimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.CurvatureDerivativeBounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_eventually_metric_bounds_from_terminal_values_of_local_solutions
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (D : RealTimeInterval) {a b : ℝ} (hab : a < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ico a b ⊆ D.regular)
    (hsol : ∀ᶠ i in atTop, ∃ S : SolutionOn (I := I) (M := U) D,
      IsSolutionOn S ∧ ∀ t, S.family.metric t = (gSeq i t).restrictOpen U)
    {B : ℝ} (hB : 1 ≤ B)
    (hequiv : ∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn U R (gSeq i t) B)
    (N : ℕ)
    (hcurv : ∀ q : ℕ, q ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNorm q (gSeq i t) x ≤ C)
    (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q)
    (hinit : ∀ᶠ i in atTop, ∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q (gSeq i b) R x ≤ A q) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in atTop,
      (∀ q ≤ N, ∀ t ∈ Icc a b, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i t) R x ≤ C) ∧
      (∀ q ≤ N, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U,
        metricDerivNorm q (gSeq i s) (gSeq i t) R x ≤ L * |s - t|) := by
  classical
  have hcurvAll : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      (q ≤ N → ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ U,
        curvDerivNorm q (gSeq i t) x ≤ C) := by
    intro q
    by_cases hq : q ≤ N
    · obtain ⟨C, hC, hb⟩ := hcurv q hq
      exact ⟨C, hC, fun _ => hb⟩
    · exact ⟨0, le_rfl, fun h => (hq h).elim⟩
  choose Ccurv hCcurv0 hCcurv using hcurvAll
  let K : ℝ := ∑ q ∈ Finset.range (N + 1),
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) * Ccurv q
  have hK : 0 ≤ K := Finset.sum_nonneg fun q _ =>
    mul_nonneg (Real.sqrt_nonneg _) (hCcurv0 q)
  have hcurvTail : ∀ᶠ i in atTop, ∀ q ∈ Finset.range (N + 1),
      ∀ t ∈ Icc a b, ∀ x ∈ U, curvDerivNorm q (gSeq i t) x ≤ Ccurv q := by
    rw [eventually_all_finset]
    exact fun q hq => hCcurv q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
  have hshi : ∀ᶠ i in atTop, MovingShiBoundOn U a b (fun _ t => gSeq i t) N K := by
    filter_upwards [hcurvTail] with i hi
    intro q hq _ t ht x hx
    calc
      _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) *
          curvDerivNorm q (gSeq i t) x :=
        sqrt_normSq0S_ricCovTower_le_curvDerivNorm (gSeq i t) q x
      _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) * Ccurv q :=
        mul_le_mul_of_nonneg_left (hi q (Finset.mem_range.mpr (by omega)) t ht x hx)
          (Real.sqrt_nonneg _)
      _ ≤ K := by
        dsimp only [K]
        exact Finset.single_le_sum
          (fun r _ => mul_nonneg
            (Real.sqrt_nonneg ((Module.finrank ℝ E : ℝ) ^ ((2 + r) + 2))) (hCcurv0 r))
          (show q ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  obtain ⟨Ccov, hCcov0, hCcov⟩ :=
    exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions
      hab R U N B hB K hK A hA
  have hlip : ∀ q : Fin (N + 1), ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M)
        (S : SolutionOn (I := I) (M := U) D),
      IsSolutionOn S → (∀ t, S.family.metric t = (g t).restrictOpen U) →
      (∀ t ∈ Ico a b, MetricUniformEquivalentOn U R (g t) B) →
      (∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ Ico a b, ∀ x ∈ U,
        metricCovDerivNorm r (g t) R x ≤ Ccov r) →
      (∀ ψ ∈ Ico a b, MovingShiBoundOn U a ψ (fun _ t => g t) N K) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U,
        metricDerivNorm q.val (g s) (g t) R x ≤ L * |s - t| := by
    intro q
    obtain ⟨L, hL, hb⟩ := exists_metric_time_lipschitz_constant_of_local_solution
      U R hB N Ccov hK q.val (by omega)
    exact ⟨L, hL, fun g S hS hm => hb g D S hS hm hab hslab hreg⟩
  choose L hL0 hL using hlip
  let Cmax := B * Real.sqrt (Module.finrank ℝ E : ℝ) +
    ∑ q ∈ Finset.range (N + 1), Ccov q
  let Lmax := ∑ q : Fin (N + 1), L q
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hCmax : 0 ≤ Cmax := add_nonneg (mul_nonneg hB0 (Real.sqrt_nonneg _))
    (Finset.sum_nonneg fun q _ => hCcov0 q)
  have hLmax : 0 ≤ Lmax := Finset.sum_nonneg fun q _ => hL0 q
  refine ⟨Cmax, Lmax, hCmax, hLmax, ?_⟩
  filter_upwards [hsol, hequiv, hshi, hinit] with i hi he hiShi hini
  obtain ⟨S, hS, hm⟩ := hi
  have hcovBound := hCcov (fun _ t => gSeq i t) D (fun _ => S)
    (fun _ => hS) (fun _ => hm) hslab hreg (fun _ => he) hiShi
    (fun q hq hqN _ => hini q hq hqN)
  constructor
  · intro q hq t ht x hx
    by_cases hzero : q = 0
    · subst q
      exact (covOrder_zero_le (gSeq i t) R (he t ht) x hx).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun r _ => hCcov0 r))
    · exact (hcovBound q (by omega) hq 0 t ht x hx).trans
        ((Finset.single_le_sum (fun r _ => hCcov0 r)
          (Finset.mem_range.mpr (by omega))).trans
          (le_add_of_nonneg_left (mul_nonneg hB0 (Real.sqrt_nonneg _))))
  · intro q hq s hs t ht x hx
    have hqLip := hL ⟨q, by omega⟩ (gSeq i) S hS hm
      (fun t ht => he t (Ico_subset_Icc_self ht))
      (fun r h1 hr t ht => hcovBound r h1 hr 0 t (Ico_subset_Icc_self ht))
      (fun ψ hψ r hr j t ht => hiShi r hr j t ⟨ht.1, ht.2.trans hψ.2.le⟩)
      s hs t ht x hx
    exact hqLip.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun r _ => hL0 r) (Finset.mem_univ _)) (abs_nonneg _))

end DifferentialGeometry.PDE.RicciFlow
