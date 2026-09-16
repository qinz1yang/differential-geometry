import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

private theorem continuousOn_uncurry_of_time_lipschitz
    {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    {f : ℝ → E → F} {J : Set ℝ} {K : Set E} {C : ℝ}
    (hspace : ∀ t ∈ J, ContinuousOn (f t) K)
    (htime : ∀ s ∈ J, ∀ t ∈ J, ∀ x ∈ K, ‖f s x - f t x‖ ≤ C * |s - t|) :
    ContinuousOn (fun q : ℝ × E => f q.1 q.2) (J ×ˢ K) := by
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ (Real.toNNReal C) hspace
  intro x hx
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, Real.dist_eq]
  exact (htime s hs t ht x hx).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (abs_nonneg _))

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem chartGram_jets_continuousOn_of_metric_time_lipschitz
    (g : ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (J : Set ℝ) (p : M) (r : ℕ) {C : Set E} (hC : IsCompact C)
    (hCt : C ⊆ (extChartAt I p).target)
    {L : ℝ}
    (htime : ∀ s ∈ J, ∀ t ∈ J, ∀ q ≤ r, ∀ x ∈ (extChartAt I p).symm '' C,
      metricDerivNorm q (g s) (g t) R x ≤ L * |s - t|)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
      (chartGramOnE (I := I) (g q.1) p i j) q.2) (J ×ˢ C) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  classical
  let K : Set M := (extChartAt I p).symm '' C
  have hKc : IsCompact K := hC.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) p).mono hCt)
  have hKchart : K ⊆ (chartAt H p).source := by
    rintro y ⟨w, hw, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I p).map_target (hCt hw)
  obtain ⟨B, hB, hjet⟩ := chartJet_sub_le (I := I) R p hKc hKchart r
  apply continuousOn_uncurry_of_time_lipschitz
    (f := fun t y => iteratedFDeriv ℝ r (chartGramOnE (I := I) (g t) p i j) y)
    (J := J) (K := C) (C := B * (r + 1) * L)
  · intro t _ y hy
    exact (((chartGramOnE_contDiffOn (I := I) (g t) p i j).contDiffAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds (hCt hy))).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)).continuousWithinAt
  · intro s hs t ht y hy
    let x := (extChartAt I p).symm y
    have hx : x ∈ K := ⟨y, hy, rfl⟩
    have hxy : extChartAt I p x = y := (extChartAt I p).right_inv (hCt hy)
    have hsum : (∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g s) (g t) R x)
        ≤ (r + 1) * (L * |s - t|) := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (r + 1), L * |s - t| := by
          apply Finset.sum_le_sum
          intro q hq
          exact htime s hs t ht q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) x hx
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hb := (hjet (g s) (g t) x hx i j).trans
      (mul_le_mul_of_nonneg_left hsum hB)
    rw [hxy] at hb
    simpa only [mul_assoc] using hb

end DifferentialGeometry.CheegerGromovCompactness
