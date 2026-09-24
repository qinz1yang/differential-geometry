import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem uniform_chartGram_jets_of_metricDerivNormSupOn {T : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (G : ℕ → T → SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (J : Set T)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J,
        metricDerivNormSupOn (I := I) K r (G n t) (g t) gRef < ε)
    (p : M) {Q : Set E} (hQ : IsCompact Q) (hQt : Q ⊆ (extChartAt I p).target)
    (r : ℕ) (i j : Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ Q,
      ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G n t) p i j) y -
        iteratedFDeriv ℝ r (chartGramOnE (I := I) (g t) p i j) y‖ ≤ ε := by
  classical
  let K : Set M := (extChartAt I p).symm '' Q
  have hK : IsCompact K :=
    hQ.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) p).mono hQt)
  have hKchart : K ⊆ (chartAt H p).source := by
    rintro x ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (hQt hy)
  obtain ⟨C, hC, hjet⟩ := chartJet_sub_le (I := I) gRef p hK hKchart r
  let B : ℝ := C * (r + 1 : ℕ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  intro ε hε
  let δ : ℝ := ε / (B + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N, hN⟩ := hconv K hK r δ hδ
  refine ⟨N, fun n hn t ht y hy => ?_⟩
  let x : M := (extChartAt I p).symm y
  have hx : x ∈ K := ⟨y, hy, rfl⟩
  have hxy : extChartAt I p x = y := (extChartAt I p).right_inv (hQt hy)
  have hsum : (∑ q ∈ Finset.range (r + 1),
      metricDerivNorm (I := I) q (G n t) (g t) gRef x) ≤ (r + 1 : ℕ) * δ := by
    calc
      _ ≤ ∑ _q ∈ Finset.range (r + 1), δ := by
        apply Finset.sum_le_sum
        intro q hq
        exact (derivNorm_le_sup (I := I) hK (by simpa using hq : q ≤ r)
          (G n t) (g t) gRef hx).trans (hN n hn t ht).le
      _ = (r + 1 : ℕ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb := hjet (G n t) (g t) x hx i j
  rw [hxy] at hb
  apply hb.trans
  calc
    _ ≤ C * ((r + 1 : ℕ) * δ) := mul_le_mul_of_nonneg_left hsum hC
    _ = B * δ := by dsimp only [B]; ring
    _ ≤ (B + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = ε := by
      dsimp only [δ]
      rw [mul_div_cancel₀ _ (by positivity : B + 1 ≠ 0)]

end DifferentialGeometry.CheegerGromovCompactness
