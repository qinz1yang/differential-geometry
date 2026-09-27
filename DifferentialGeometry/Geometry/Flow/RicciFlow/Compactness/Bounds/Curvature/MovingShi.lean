import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance curvatureJetShiC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance curvatureJetShiC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (N : ℕ) (C : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
      (U : Set M) (a b : ℝ),
      (∀ r ≤ N, ∀ i, ∀ t ∈ Icc a b, ∀ x ∈ U,
        curvDerivNorm (I := I) r (gSeq i t) x ≤ C r) →
      MovingShiBoundOn (I := I) U a b gSeq N K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A : ℕ → ℝ := fun r => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + r) + 2)) *
    max (C r) 0
  have hA (r : ℕ) : 0 ≤ A r := mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)
  refine ⟨∑ r ∈ Finset.range (N + 1), A r, Finset.sum_nonneg (fun r _ => hA r), ?_⟩
  intro gSeq U a b hcurv r hr i t ht x hx
  have hbase :
      CovariantDerivative.ricciSection (I := I) (M := M)
          (leviCivitaConnectionOfMetric (I := I) (gSeq i t))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) (gSeq i t)) =
        metricTraceCovariantFourField (I := I) (M := M) (gSeq i t) (metricRm04 (gSeq i t)) := by
    simpa only [metricRm04, metricCov] using
      (levi_civita_ricci_section_eq_riemann_trace (I := I) (M := M) (gSeq i t))
  have htrace := iterRic_normSq_le (gSeq i t) (metricRm04 (gSeq i t)) r x
  rw [ricCovTower, hbase]
  have hcurv' : Real.sqrt (normSq0S (gSeq i t) x (4 + r)
      (iterCov (gSeq i t) 4 (metricRm04 (gSeq i t)) r x)) ≤ C r := by
    have hh := hcurv r hr i t ht x hx
    dsimp only [curvDerivNorm, curvDerivNormSq] at hh
    rw [curvCovDeriv_normSq_eq] at hh
    exact hh
  have hric : Real.sqrt (normSq0S (I := I) (gSeq i t) x (2 + r)
      (iterCov (gSeq i t) 2
        (metricTraceCovariantFourField (gSeq i t) (metricRm04 (gSeq i t))) r x)) ≤ A r := by
    calc
      _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + r) + 2) *
          normSq0S (I := I) (gSeq i t) x (4 + r)
            (iterCov (gSeq i t) 4 (metricRm04 (gSeq i t)) r x)) :=
        Real.sqrt_le_sqrt htrace
      _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + r) + 2)) *
          Real.sqrt (normSq0S (gSeq i t) x (4 + r)
            (iterCov (gSeq i t) 4 (metricRm04 (gSeq i t)) r x)) := by
        rw [Real.sqrt_mul (by positivity)]
      _ ≤ A r := mul_le_mul_of_nonneg_left
        (hcurv'.trans (le_max_left _ _)) (Real.sqrt_nonneg _)
  exact hric.trans (Finset.single_le_sum (fun j _ => hA j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))

end DifferentialGeometry.PDE.RicciFlow

end
