import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply
  ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply
  ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section TopSeparatedResidualIntegrator

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

theorem boundedFactorGridWindow_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 3), Kt k) * (1 + R ^ 2),
    fun i => mul_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (by positivity), ?_⟩
  intro P hPball i hia
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun k _ => ?_)
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  have hint_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k => (hKt P hPball k).1
  have hint2_k : ∀ k : ℕ,
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
    fun k => (hKt P hPball k).2
  have hmaj_int : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integrable_finset_sum _ (fun k _ => hint_k k)
  have hmono : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) ≤
        ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k := by
    intro x
    rw [Combinatorics.boundedFactorGridWindow]
    exact Finset.sum_le_sum (fun k _ =>
      Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid (b x) (hb x) (i + 1) k)
  refine le_trans (MeasureTheory.integral_mono hint hmaj_int hmono) ?_
  rw [MeasureTheory.integral_finset_sum _ (fun k _ => hint_k k)]
  have hterm : ∀ k ∈ Finset.range (i + 3),
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine le_trans (hint2_k k) ?_
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    by_cases hk2 : k ≤ i + 1
    · have hsub : (∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) ?_
        intro j _ _
        exact sq_nonneg _
      have h1 : Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (hKt_nn k)
      refine le_trans h1 ?_
      have hfactor : (1 : ℝ) ≤ 1 + R ^ 2 := le_add_of_nonneg_right (sq_nonneg R)
      have hproduct : (0 : ℝ) ≤ Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
        mul_nonneg (hKt_nn k) (add_nonneg (by norm_num) hsum_nn)
      calc Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          = 1 * (Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by ring
        _ ≤ (1 + R ^ 2) * (Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right hfactor hproduct
        _ = Kt k * (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
    · have hk_eq : k = i + 2 := by omega
      subst hk_eq
      have hsplit : (∑ j ∈ Finset.range ((i + 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
          (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
        Finset.sum_range_succ _ (i + 2)
      have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤ R ^ 2 := by
        have h := hPball (i + 2) (by omega)
        nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
      rw [hsplit]
      have hcross : (0 : ℝ) ≤ R ^ 2 * ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := mul_nonneg (sq_nonneg R) hsum_nn
      have hbase : 1 + (∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤
          (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        calc 1 + (∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2
            ≤ 1 + (∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) + R ^ 2 :=
              by simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left htop (1 + ∑ j ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          _ ≤ 1 + (∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) + R ^ 2 +
              R ^ 2 * ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := le_add_of_nonneg_right hcross
          _ = (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
      simpa only [add_assoc, mul_assoc] using
        mul_le_mul_of_nonneg_left hbase (hKt_nn (i + 2))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

section NormedBoundedFactorIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem productTerm_integral_tame_le_ordS
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (u : SmoothCcTensor g₀ 0 s)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (u.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
              ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
      ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 s j u) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + j)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
        ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 s i u), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i)
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 s i u), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
              μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))
              ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem cappedTopLayerCell_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {Lam : ℝ} (hLam_nn : 0 ≤ Lam)
    (hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2)
    (Cgn : ℕ → ℝ) (hCgn_nn : ∀ k, 0 ≤ Cgn k)
    (hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)))
    (i n : ℕ) (e : Fin n → ℕ) (hn : n ≤ i + 2)
    (he_sum : ∑ m, e m = i + 2) (he_cap : ∀ m, e m ≤ i + 1)
    (MBv : ℝ) (hMBv1 : 1 ≤ MBv) (hMBv_Lam : Lam ≤ MBv)
    (hMBv_vol : ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ MBv)
    (hMBv_Cgn : ∀ k, k ≤ i → Cgn k ≤ MBv) :
    (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hMBv_nn : 0 ≤ MBv := le_trans zero_le_one hMBv1
  have hLam2_nn : 0 ≤ Lam ^ 2 := sq_nonneg _
  set Wsum : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWsum
  have hWsum1 : 1 ≤ Wsum := by
    rw [hWsum]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  have hWsum_nn : 0 ≤ Wsum := le_trans zero_le_one hWsum1
  set F : M → ℝ := fun x => ∏ m : Fin n,
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) with hF
  have hfac_nn : ∀ (m : Fin n) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
    fun m x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _
  have hfac_cont : ∀ m : Fin n, Continuous (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro m
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (e m) P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 (e m) P) x]
  have hF_int : MeasureTheory.Integrable F μ := by
    have hcp : Continuous F := by
      rw [hF]; exact continuous_finset_prod _ (fun m _ => hfac_cont m)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set high : Finset (Fin n) := Finset.univ.filter (fun m => 3 ≤ e m) with hhigh
  set low : Finset (Fin n) := Finset.univ.filter (fun m => ¬ 3 ≤ e m) with hlow
  have hmem_high : ∀ m : Fin n, m ∈ high ↔ 3 ≤ e m := fun m => by
    rw [hhigh, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hmem_low : ∀ m : Fin n, m ∈ low ↔ ¬ 3 ≤ e m := fun m => by
    rw [hlow, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hlowbnd : ∀ (x : M),
      (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Lam ^ (2 * low.card) := by
    intro x
    calc (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ low, Lam ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
          intro m hm
          have hem : e m ≤ 2 := by
            have := (hmem_low m).mp hm; omega
          exact hΛsup_low (e m) hem x
      _ = Lam ^ (2 * low.card) := by rw [Finset.prod_const, ← pow_mul, Nat.mul_comm]
  by_cases hne : high.Nonempty
  · have hcard_pos : 0 < high.card := Finset.Nonempty.card_pos hne
    set i₀ : ℕ := ∑ m ∈ high, (e m - 2) with hi₀
    have hge3 : ∀ m ∈ high, 3 ≤ e m := fun m hm => (hmem_high m).mp hm
    have hn'_le : high.card ≤ i₀ := by
      rw [hi₀, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro m hm; have := hge3 m hm; omega
    have hi₀_ge1 : 1 ≤ i₀ := le_trans hcard_pos hn'_le
    have heq_sum : (∑ m ∈ high, e m) = i₀ + 2 * high.card := by
      have h1 : (∑ m ∈ high, e m) = ∑ m ∈ high, ((e m - 2) + 2) :=
        Finset.sum_congr rfl (fun m hm => by have := hge3 m hm; omega)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← hi₀,
        Nat.mul_comm]
    have hsum_high_le : (∑ m ∈ high, e m) ≤ i + 2 := by
      calc (∑ m ∈ high, e m) ≤ ∑ m : Fin n, e m :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = i + 2 := he_sum
    have hi₀_bound : 2 + i₀ ≤ i + 1 := by
      rcases Nat.lt_or_ge high.card 2 with h1 | h2
      · have hcard1 : high.card = 1 := by omega
        obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hcard1
        have hsingle : (∑ m ∈ high, e m) = e m₀ := by rw [hm₀, Finset.sum_singleton]
        have hcap0 : e m₀ ≤ i + 1 := he_cap m₀
        omega
      · omega
    set ι : Fin high.card → {m // m ∈ high} := fun m' => (Finset.equivFin high).symm m' with hι
    set e' : Fin high.card → ℕ := fun m' => e ((ι m' : Fin n)) - 2 with he'
    have hge3' : ∀ m' : Fin high.card, 3 ≤ e ((ι m' : Fin n)) :=
      fun m' => hge3 _ (ι m').2
    have he'_sum : (∑ m', e' m') = i₀ := by
      rw [hi₀, ← Finset.sum_coe_sort high (fun m => e m - 2)]
      exact Equiv.sum_comp (Finset.equivFin high).symm (fun m : {m // m ∈ high} => e ↑m - 2)
    have hcongr_local : ∀ (x : M) (n₁ n₂ : ℕ), n₁ = n₂ →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₁) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₁ P).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₂) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₂ P).toSection x) := by
      intro x n₁ n₂ h; subst h; rfl
    have hcellprod : ∀ x : M,
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        ∏ m' : Fin high.card,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + e' m') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) (e' m')
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) := by
      intro x
      rw [← Finset.prod_coe_sort high (fun m =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)),
        ← Equiv.prod_comp (Finset.equivFin high).symm
          (fun m : {m // m ∈ high} =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e ↑m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e ↑m) P).toSection x))]
      refine Finset.prod_congr rfl (fun m' _ => ?_)
      symm
      rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 (e' m') P x]
      exact hcongr_local x (2 + e' m') (e ((ι m' : Fin n))) (by
        have := hge3' m'; simp only [he']; omega)
    have hΛsup_v2 : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
      hΛsup_low 2 (le_refl 2)
    have htmpl := productTerm_integral_tame_le_ordS (I := I) (M := M) g₀ (2 + 2)
      (iteratedCovGrad (I := I) g₀ 0 2 2 P)
      (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)))
      i₀ hi₀_ge1 hLam_nn hΛsup_v2 (le_refl _) (hCgn_nn i₀) (hGNv i₀ hi₀_ge1)
      high.card hn'_le e' he'_sum
    have hhigh_int : MeasureTheory.Integrable
        (fun x => ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
      have hcp : Continuous (fun x => ∏ m ∈ high,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
        continuous_finset_prod _ (fun m _ => hfac_cont m)
      exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hnorm_int : ∀ (s' : ℕ) (w : Integral.L2.SmoothCcTensor g₀ 0 s'),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s' x (w.toSection x) ∂μ) = ‖w‖ ^ 2 := by
      intro s' w
      rw [SmoothCcTensor.norm_def w, hμ]
      exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 s'
        (w.toSection)).symm
    have hhigh_le : (∫ x, ∏ m ∈ high,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ) ≤
        (i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcellprod)]
      exact htmpl.2
    have hRsq_le : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 ≤ Wsum := by
      have e1 : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ :=
        (hnorm_int ((2 + 2) + i₀) (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
      have e2 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ) =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 i₀ P x
      have e3 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 :=
        hnorm_int (2 + (2 + i₀)) (iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P)
      have hmem : 2 + i₀ ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
      have hle_sum : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
      rw [e1, e2, e3, hWsum]; linarith
    have hRsq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := sq_nonneg _
    have hmax_nn : 0 ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans hLam_nn (le_max_left _ _)
    have hmax1 : (1 : ℝ) ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans (le_max_right (Cgn i₀) 1) (le_max_right Lam _)
    have hmax_le : max Lam (max (Cgn i₀) 1) ≤ MBv := by
      apply max_le hMBv_Lam
      apply max_le (hMBv_Cgn i₀ (by omega)) hMBv1
    have hlowcard_le : low.card ≤ i + 2 :=
      le_trans (Finset.card_filter_le _ _) (le_trans (by simp) hn)
    have hLampow_nn : 0 ≤ Lam ^ (2 * low.card) := pow_nonneg hLam_nn _
    have hsplit : ∀ x : M, F x =
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
        (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hF, hhigh, hlow]
      exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 3 ≤ e m)
        (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * low.card) *
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hsplit x]
      have hhnn : 0 ≤ ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hfac_nn m x)
      calc (∏ m ∈ high, _) * (∏ m ∈ low, _)
          ≤ (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) * Lam ^ (2 * low.card) :=
            mul_le_mul_of_nonneg_left (hlowbnd x) hhnn
        _ = Lam ^ (2 * low.card) * (∏ m ∈ high, _) := by ring
    have hfinal : (∫ x, F x ∂μ) ≤ Lam ^ (2 * low.card) *
        ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ x, Lam ^ (2 * low.card) *
              (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ∂μ :=
            MeasureTheory.integral_mono hF_int (hhigh_int.const_mul _) hFbnd
        _ = Lam ^ (2 * low.card) * ∫ x, ∏ m ∈ high,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Lam ^ (2 * low.card) *
              ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
                  (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hhigh_le hLampow_nn
    refine le_trans hfinal ?_
    have hLL : Lam ^ (2 * low.card) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hMM : (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) ≤ MBv ^ (7 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hmax_nn hmax_le _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hi₀R : (i₀ : ℝ) ≤ (i : ℝ) + 2 := by
      have : i₀ ≤ i + 2 := by omega
      exact_mod_cast le_trans this (by norm_num)
    have hpowsum : MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2)) = MBv ^ (9 * (i + 2)) := by
      rw [← pow_add]; congr 1; ring
    calc Lam ^ (2 * low.card) *
          ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2)
        ≤ MBv ^ (2 * (i + 2)) *
            (((i : ℝ) + 2) * MBv ^ (7 * (i + 2)) * Wsum) := by
          apply mul_le_mul hLL _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul hi₀R hMM (by positivity) (by positivity)) hRsq_le
            hRsq_nn (by positivity)
      _ = ((i : ℝ) + 2) * (MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2))) * Wsum := by ring
      _ = ((i : ℝ) + 2) * MBv ^ (9 * (i + 2)) * Wsum := by rw [hpowsum]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hallow : ∀ m : Fin n, e m ≤ 2 := by
      intro m
      by_contra h
      have hm3 : 3 ≤ e m := by omega
      have hmem : m ∈ high := (hmem_high m).mpr hm3
      rw [hne] at hmem
      exact absurd hmem (by simp)
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * n) := by
      intro x
      rw [hF]
      calc (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ ∏ _m : Fin n, Lam ^ 2 := by
            apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
            intro m _; exact hΛsup_low (e m) (hallow m) x
        _ = Lam ^ (2 * n) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm]
    have hvol_int : (∫ x, F x ∂μ) ≤ Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ _x, Lam ^ (2 * n) ∂μ :=
            MeasureTheory.integral_mono hF_int (MeasureTheory.integrable_const _) hFbnd
        _ = Lam ^ (2 * n) * ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
            rw [MeasureTheory.integral_const, smul_eq_mul, hμ,
              MeasureTheory.measureReal_def, mul_comm]
    refine le_trans hvol_int ?_
    have hLampow_nn : 0 ≤ Lam ^ (2 * n) := pow_nonneg hLam_nn _
    have hLn : Lam ^ (2 * n) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hbase : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (2 * (i + 2)) * MBv := by
      apply mul_le_mul hLn hMBv_vol ENNReal.toReal_nonneg (pow_nonneg hMBv_nn _)
    have hpow_le : MBv ^ (2 * (i + 2)) * MBv ≤ MBv ^ (9 * (i + 2)) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hMBv1 (by omega)
    have hfinal2 : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (9 * (i + 2)) := le_trans hbase hpow_le
    calc Lam ^ (2 * n) *
          ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
        ≤ MBv ^ (9 * (i + 2)) := hfinal2
      _ = 1 * (MBv ^ (9 * (i + 2)) * 1) := by ring
      _ ≤ ((i : ℝ) + 2) * (MBv ^ (9 * (i + 2)) * Wsum) := by
          apply mul_le_mul (by have := Nat.cast_nonneg (α := ℝ) i; linarith) _
            (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left hWsum1 (by positivity)
      _ = (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) * Wsum := by ring

theorem boundedFactorGrid_cappedTopLayer_integral_flat
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGrid
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.Analysis.Spectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact
        (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose_spec.1
    · exact le_refl 0
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  set MB : ℕ → ℝ := fun i => 1 + vol + Lam + ∑ k ∈ Finset.range (i + 1), Cgn k with hMBdef
  have hsumCgn_nn : ∀ i, 0 ≤ ∑ k ∈ Finset.range (i + 1), Cgn k :=
    fun i => Finset.sum_nonneg (fun k _ => hCgn_nn k)
  have hMB1 : ∀ i, 1 ≤ MB i := by
    intro i; rw [hMBdef]
    have := hsumCgn_nn i; linarith
  have hMB_nn : ∀ i, 0 ≤ MB i := fun i => le_trans zero_le_one (hMB1 i)
  have hMB_Lam : ∀ i, Lam ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_vol : ∀ i, vol ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_Cgn : ∀ i k, k ≤ i → Cgn k ≤ MB i := by
    intro i k hk
    rw [hMBdef]
    have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle : Cgn k ≤ ∑ k' ∈ Finset.range (i + 1), Cgn k' :=
      Finset.single_le_sum (fun k' _ => hCgn_nn k') hmem
    linarith
  set gcount : ℕ → ℝ := fun i =>
    ∑ n ∈ Finset.range (i + 2 + 1), ((Finset.Nat.antidiagonalTuple n (i + 2)).card : ℝ)
    with hgcount
  have hgcount_nn : ∀ i, 0 ≤ gcount i :=
    fun i => Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  refine ⟨fun i => gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))),
    fun i => mul_nonneg (hgcount_nn i)
      (mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)), ?_⟩
  intro P hPball i
  have hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
    intro m hm x
    have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
        _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤
        ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) := by
      have hmmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum
        (f := fun m' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x))
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m') x _) hmmem
    have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hchain : ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) ≤ Lam ^ 2 := by
      refine le_trans (hCemb P x) ?_
      rw [hLam2]
      calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
    exact le_trans hsingle hchain
  have hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
    hΛsup_low 2 (le_refl 2)
  have hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)) := by
    intro i₀ hi₀ j hj0 hji
    have hGNspec :=
      (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose_spec.2
    have hb := hGNspec (iteratedCovGrad (I := I) g₀ 0 2 2 P) Lam hLam_nn hΛsup_v2 j hj0 hji
    have hchoose :
      (Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose = Cgn i₀ := by
      rw [hCgn]; simp only [dif_pos hi₀]
    rw [hchoose] at hb
    have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 ((2 + 2) + i₀)
        (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀ (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
    rw [hnorm] at hb
    exact hb
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hcell_cont : ∀ (n : ℕ) (e : Fin n → ℕ),
      Continuous (fun x => ∏ m : Fin n, b x (e m)) := by
    intro n e
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hcell_int : ∀ (n : ℕ) (e : Fin n → ℕ),
      MeasureTheory.Integrable (fun x => ∏ m : Fin n, b x (e m))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun n e => (hcell_cont n e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrid_cont : Continuous (fun x =>
      Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) := by
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hgrid_int : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hgrid_int, ?_⟩
  have hPT : ∀ n ∈ Finset.range (i + 2 + 1),
      ∀ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
      (∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro n hn e he
    have hnle : n ≤ i + 2 := by have := Finset.mem_range.mp hn; omega
    have he_sum : ∑ m, e m = i + 2 :=
      Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp he).1
    have he_cap : ∀ m, e m ≤ i + 1 := (Finset.mem_filter.mp he).2
    exact cappedTopLayerCell_integral_le (I := I) (M := M) g₀ P hLam_nn hΛsup_low
      Cgn hCgn_nn hGNv i n e hnle he_sum he_cap (MB i) (hMB1 i) (hMB_Lam i)
      (hMB_vol i) (fun k hk => hMB_Cgn i k hk)
  have hgrid_eq : (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have h1 : (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) =
        (fun x => ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            ∏ m : Fin n, b x (e m)) := rfl
    rw [h1, MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n _
      rw [MeasureTheory.integral_finset_sum]
      intro e _; exact hcell_int n e
    · intro n _
      apply MeasureTheory.integrable_finset_sum
      intro e _; exact hcell_int n e
  rw [hgrid_eq]
  have hKcell_nn : (0 : ℝ) ≤ ((i : ℝ) + 2) * MB i ^ (9 * (i + 2)) :=
    mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)
  have hWsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  have hsum_le :
      (∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro e he
    exact hPT n hn e he
  have hsum_const :
      (∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) =
        (∑ n ∈ Finset.range (i + 2 + 1),
          (((Finset.Nat.antidiagonalTuple n (i + 2)).filter
            (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcount :
      (∑ n ∈ Finset.range (i + 2 + 1),
        (((Finset.Nat.antidiagonalTuple n (i + 2)).filter
          (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) ≤ gcount i := by
    rw [hgcount]
    apply Finset.sum_le_sum
    intro n _
    exact_mod_cast Finset.card_filter_le _ _
  have hsum_counted :
      (∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ n ∈ Finset.range (i + 2 + 1),
          (((Finset.Nat.antidiagonalTuple n (i + 2)).filter
            (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
    le_trans hsum_le (le_of_eq hsum_const)
  have hscaled :
      (∑ n ∈ Finset.range (i + 2 + 1),
        (((Finset.Nat.antidiagonalTuple n (i + 2)).filter
          (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) ≤
        gcount i *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
    mul_le_mul_of_nonneg_right hcount (mul_nonneg hKcell_nn hWsum_nn)
  have htotal := le_trans hsum_counted hscaled
  simpa only [mul_assoc] using htotal

theorem boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨Kc, hKc_nn, hKc⟩ := boundedFactorGrid_cappedTopLayer_integral_flat
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 2), Kt k) + Kc i,
    fun i => add_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (hKc_nn i), ?_⟩
  intro P hPball i
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hbfg_cont : ∀ (K k : ℕ),
      Continuous (fun x => Combinatorics.boundedFactorGrid (b x) K k) := by
    intro K k
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hbfg_int : ∀ (K k : ℕ), MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) K k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun K k => (hbfg_cont K k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow]
    exact continuous_finset_sum _ (fun k _ => hbfg_cont (i + 1) k)
  have hWint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hWint, ?_⟩
  have hInt_eq : (∫ x, Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hEq : (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) =
        (fun x => ∑ k ∈ Finset.range (i + 3),
          Combinatorics.boundedFactorGrid (b x) (i + 1) k) := rfl
    rw [hEq, MeasureTheory.integral_finset_sum _ (fun k _ => hbfg_int (i + 1) k),
      Finset.sum_range_succ]
  rw [hInt_eq]
  have hlayer_le : ∀ k ∈ Finset.range (i + 2),
      (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hAint : MeasureTheory.Integrable
        (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := (hKt P hPball k).1
    have hAbound : (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := (hKt P hPball k).2
    calc (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          MeasureTheory.integral_mono (hbfg_int (i + 1) k) hAint
            (fun x => Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid
              (b x) (hb x) (i + 1) k)
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hAbound
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
          have hsub : (∑ j ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
              ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)
            intro m hm
            rw [Finset.mem_range] at hm ⊢
            omega
          linarith
  have hleaf := (hKc P hPball i).2
  calc (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ (∑ k ∈ Finset.range (i + 2), Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
        add_le_add (Finset.sum_le_sum hlayer_le) hleaf
    _ = ((∑ k ∈ Finset.range (i + 2), Kt k) + Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        rw [← Finset.sum_mul, ← add_mul]

end NormedBoundedFactorIntegral

theorem boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  obtain ⟨Kflat, hKflat_nn, hK⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kflat, hKflat_nn, 0, le_refl 0, ?_⟩
  intro P hPball i
  obtain ⟨hint, hbound⟩ := hK P hPball i
  refine ⟨hint, ?_⟩
  rw [show (0 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 = 0 by ring, add_zero]
  exact hbound

theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hia
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i hia
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

section TopSeparatedKoszulExport

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_raisedKoszul_pointwise_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) :=
  rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x



omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem grid_prod_int_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
              μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))
              ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5


end TopSeparatedKoszulExport

end TopSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry
