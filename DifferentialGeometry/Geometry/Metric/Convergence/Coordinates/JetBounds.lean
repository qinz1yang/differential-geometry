import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Christoffel.Perturbation

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open scoped Manifold ContDiff Topology BigOperators Matrix

open CheegerGromovCompactness Geometry.Curvature Geometry.Operator
open Analysis.Calculus Analysis.Spectral.DeTurckCoefficients
open Integral.DivergenceTheorem Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

private lemma chartGramMatrix_sub_sum_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |(chartGramMatrix (I := I) u α y - chartGramMatrix (I := I) u' α y) p.1 p.2|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C0, hC0, h0⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 0
  let A0 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨A0 * C0, mul_nonneg hA0 hC0, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hsum :
      (∑ q ∈ Finset.range 1, metricDerivNorm (I := I) q u u' gRef y) ≤ S := by
    rw [hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => Real.sqrt_nonneg _)
  have hψ : (extChartAt I α).symm z = y := by
    rw [hz]
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      |chartGramMatrix (I := I) u α y a b - chartGramMatrix (I := I) u' α y a b| ≤
        C0 * S := by
    intro a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have hraw := h0 u u' y hy a b
    have heq : iteratedFDeriv ℝ 0 (f - f') z =
        iteratedFDeriv ℝ 0 f z - iteratedFDeriv ℝ 0 f' z := by
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Pi.sub_apply, map_sub]
    have hbound :
        |f z - f' z| ≤ C0 * S := by
      have hraw' : ‖iteratedFDeriv ℝ 0 f z - iteratedFDeriv ℝ 0 f' z‖ ≤ C0 * S :=
        hraw.trans (mul_le_mul_of_nonneg_left hsum hC0)
      rwa [← heq, norm_iteratedFDeriv_zero, Pi.sub_apply, Real.norm_eq_abs] at hraw'
    simpa only [f, f', chartGramOnE_def, hψ] using hbound
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        |(chartGramMatrix (I := I) u α y - chartGramMatrix (I := I) u' α y) p.1 p.2|)
        ≤ A0 * (C0 * S) := by
          dsimp only [A0]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [Matrix.sub_apply, one_mul] using hentry p.1 p.2
    _ = (A0 * C0) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

private lemma chartGramPartial_sub_sum_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u α p.1 p.2.2)
              (extChartAt I α y) -
            partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' α p.1 p.2.2)
              (extChartAt I α y)|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C1, hC1, h1⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 1
  let B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let A1 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E), B
  have hA1 : 0 ≤ A1 := Finset.sum_nonneg fun _ _ => hB
  refine ⟨A1 * C1, mul_nonneg hA1 hC1, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hsum :
      (∑ q ∈ Finset.range 2, metricDerivNorm (I := I) q u u' gRef y) ≤ S := by
    rw [hS]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => Real.sqrt_nonneg _)
  have hentry : ∀ d a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) d (chartGramOnE (I := I) u α a b) z -
        partialDeriv (E := E) d (chartGramOnE (I := I) u' α a b) z| ≤ C1 * B * S := by
    intro d a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have happ := (iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z).le_opNorm_mul_pow_of_le
        (b := B)
        (m := fun i : Fin 1 => (chartModelBasis E) (![d] i))
        ((pi_norm_le_iff_of_nonneg hB).mpr fun i =>
          Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
            (Finset.mem_univ (![d] i)))
    rw [Real.norm_eq_abs] at happ
    have heval : (iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z)
          ![(chartModelBasis E) d] = partialDeriv (E := E) d f z - partialDeriv (E := E) d f' z := by
      simp only [sub_apply]
      rw [partialDeriv_eq_iteratedFDeriv_one, partialDeriv_eq_iteratedFDeriv_one]
    have hargs : (fun i : Fin 1 => (chartModelBasis E) (![d] i)) =
        ![(chartModelBasis E) d] := by
      funext i
      fin_cases i
      rfl
    rw [hargs, heval, pow_one] at happ
    have hraw := h1 u u' y hy a b
    rw [show chartGramOnE (I := I) u α a b = f from rfl,
      show chartGramOnE (I := I) u' α a b = f' from rfl]
    calc
      |partialDeriv (E := E) d f z - partialDeriv (E := E) d f' z| ≤
          ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f' z‖ * B := happ
      _ ≤ (C1 * S) * B := mul_le_mul_of_nonneg_right
        (hraw.trans (mul_le_mul_of_nonneg_left hsum hC1)) hB
      _ = C1 * B * S := by ring
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u α p.1 p.2.2) z -
        partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' α p.1 p.2.2) z|)
        ≤ A1 * (C1 * S) := by
          dsimp only [A1]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [B, mul_comm, mul_left_comm, mul_assoc] using hentry p.2.1 p.1 p.2.2
    _ = (A1 * C1) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

private lemma chartGramPartial2_sub_sum_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) u α p.2.2.1 p.2.2.2)) (extChartAt I α y) -
            partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) u' α p.2.2.1 p.2.2.2)) (extChartAt I α y)|) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C2, hC2, h2⟩ := chartJet_sub_le (I := I) gRef α hK hKchart 2
  let B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let A2 : ℝ := ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2
  have hA2 : 0 ≤ A2 := Finset.sum_nonneg fun _ _ => sq_nonneg B
  refine ⟨A2 * C2, mul_nonneg hA2 hC2, ?_⟩
  intro u u' y hy
  set z : E := extChartAt I α y with hz
  set S : ℝ := ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y with hS
  have hzint : z ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq, hz]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hKchart hy)
  have hentry : ∀ d c a b : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) d (partialDeriv (E := E) c
          (chartGramOnE (I := I) u α a b)) z -
        partialDeriv (E := E) d (partialDeriv (E := E) c
          (chartGramOnE (I := I) u' α a b)) z| ≤ C2 * B ^ 2 * S := by
    intro d c a b
    let f : E → ℝ := chartGramOnE (I := I) u α a b
    let f' : E → ℝ := chartGramOnE (I := I) u' α a b
    have hf : ContDiffAt ℝ ∞ f z :=
      ((chartGramOnE_contDiffOn (I := I) u α a b).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hzint)
    have hf' : ContDiffAt ℝ ∞ f' z :=
      ((chartGramOnE_contDiffOn (I := I) u' α a b).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hzint)
    have happ := (iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z).le_opNorm_mul_pow_of_le
        (b := B)
        (m := fun i : Fin 2 => (chartModelBasis E) (![d, c] i))
        ((pi_norm_le_iff_of_nonneg hB).mpr fun i =>
          Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
            (Finset.mem_univ (![d, c] i)))
    rw [Real.norm_eq_abs] at happ
    have heval : (iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z)
          ![(chartModelBasis E) d, (chartModelBasis E) c] =
        partialDeriv (E := E) d (partialDeriv (E := E) c f) z -
          partialDeriv (E := E) d (partialDeriv (E := E) c f') z := by
      simp only [sub_apply]
      rw [partialDeriv_partialDeriv_eq_iteratedFDeriv_two f hf d c,
        partialDeriv_partialDeriv_eq_iteratedFDeriv_two f' hf' d c]
    have hargs : (fun i : Fin 2 => (chartModelBasis E) (![d, c] i)) =
        ![(chartModelBasis E) d, (chartModelBasis E) c] := by
      funext i
      fin_cases i <;> rfl
    rw [hargs, heval] at happ
    have hraw := h2 u u' y hy a b
    have hraw' :
        ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z‖ ≤ C2 * S := by
      simpa only [Nat.reduceAdd, hS] using hraw
    rw [show chartGramOnE (I := I) u α a b = f from rfl,
      show chartGramOnE (I := I) u' α a b = f' from rfl]
    calc
      |partialDeriv (E := E) d (partialDeriv (E := E) c f) z -
          partialDeriv (E := E) d (partialDeriv (E := E) c f') z| ≤
          ‖iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 f' z‖ * B ^ 2 := happ
      _ ≤ (C2 * S) * B ^ 2 := mul_le_mul_of_nonneg_right
        hraw' (sq_nonneg B)
      _ = C2 * B ^ 2 * S := by ring
  calc
    (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) p.1
          (partialDeriv (E := E) p.2.1
            (chartGramOnE (I := I) u α p.2.2.1 p.2.2.2)) z -
        partialDeriv (E := E) p.1
          (partialDeriv (E := E) p.2.1
            (chartGramOnE (I := I) u' α p.2.2.1 p.2.2.2)) z|)
        ≤ A2 * (C2 * S) := by
          dsimp only [A2]
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun p _ => by
            simpa only [B, mul_comm, mul_left_comm, mul_assoc] using
              hentry p.1 p.2.1 p.2.2.1 p.2.2.2
    _ = (A2 * C2) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by
      rw [← hS]
      ring

theorem exists_chartMetricJet2DiffSup_le
    (gRef : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      ∀ y ∈ K,
        chartMetricJet2DiffSup (I := I) (M := M) u u' α (extChartAt I α y) ≤
          C * ∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y := by
  classical
  obtain ⟨C0, hC0, h0⟩ := chartGramMatrix_sub_sum_le (I := I) gRef α hK hKchart
  obtain ⟨C1, hC1, h1⟩ := chartGramPartial_sub_sum_le (I := I) gRef α hK hKchart
  obtain ⟨C2, hC2, h2⟩ := chartGramPartial2_sub_sum_le (I := I) gRef α hK hKchart
  refine ⟨C0 + C1 + C2, by positivity, ?_⟩
  intro u u' y hy
  have hψ : (extChartAt I α).symm (extChartAt I α y) = y :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  unfold chartMetricJet2DiffSup chartMetricJet1DiffSup chartGramDiffSup matrixEntryL1
    chartGramPartialDiffSup gramPartialDiffEntry chartGramPartial2DiffSup gramPartial2DiffEntry
  rw [hψ]
  calc
    _ ≤ C0 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) +
        C1 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) +
        C2 * (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) :=
      add_le_add (add_le_add (h0 u u' y hy) (h1 u u' y hy)) (h2 u u' y hy)
    _ = (C0 + C1 + C2) *
        (∑ q ∈ Finset.range 3, metricDerivNorm (I := I) q u u' gRef y) := by ring


end DifferentialGeometry.Tensor.Coordinates
