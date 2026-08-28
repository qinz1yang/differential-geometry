import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualWindow

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopOrderSeparatedResidualIntegrator



theorem atgGridIntRs
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ r s)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                      ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                        ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ r s k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ r s k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Λ₀ (max (Cgn k) 1)) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_max_right Λ₀ _))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hK_nn : ∀ k, 0 ≤ (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol := by
    intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, hK_nn, ?_⟩
  intro P hsup i
  have hone_le : (1 : ℝ) ≤ 1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
    linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)]
  by_cases hi0 : i = 0
  · subst hi0
    have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid0]; exact MeasureTheory.integrable_const 1
    · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol]
      calc vol ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) * 1 := by
            rw [mul_one]
            exact le_add_of_nonneg_left
              (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
        _ ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) *
            (1 + ‖iteratedCovGrad (I := I) g₀ r s 0 P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hone_le (hK_nn 0)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ r s i hi1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < i →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
                ((iteratedCovGrad (I := I) g₀ r s j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
          Cgn i * Λ₀ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
            ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
      intro j hj0 hji
      have hb := hGNspec P Λ₀ hΛ₀0 hsup j hj0 hji
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ r s i hi1).choose = Cgn i := by
        rw [hCgn]; simp only [dif_pos hi1]
      rw [hchoose] at hb
      have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i P).toFun = ‖iteratedCovGrad (I := I) g₀ r s i P‖ :=
        (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ r s i P)).symm
      rw [hnorm] at hb
      exact hb
    have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
        MeasureTheory.Integrable (fun x => ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
                ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
      intro n hn e he
      have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := grid_prod_int_le (I := I) (M := M) g₀ P
        (norm_nonneg (iteratedCovGrad (I := I) g₀ r s i P)) i hi1 hΛ₀0 hsup
        (le_refl _) (hCgn_nn i) hGNP n hn_le e hsum_e
      refine ⟨hres.1, ?_⟩
      refine le_trans hres.2 (le_of_eq ?_)
      simp only [hGfun]
    have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      apply MeasureTheory.integrable_finsetSum
      intro n hn
      apply MeasureTheory.integrable_finsetSum
      intro e he
      exact (hPT n hn e he).1
    refine ⟨hgrid_int, ?_⟩
    rw [MeasureTheory.integral_finsetSum _
      (fun n hn => MeasureTheory.integrable_finsetSum _ (fun e he => (hPT n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (i + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
              ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      intro n hn
      exact MeasureTheory.integral_finsetSum _ (fun e he => (hPT n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + e m) x
            ((iteratedCovGrad (I := I) g₀ r s (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro e he
      exact (hPT n hn e he).2
    have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 =
        (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
          (Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hle1 ?_
    rw [heq2]
    have hcard_nn : 0 ≤ ∑ n ∈ Finset.range (i + 1),
        ((Finset.Nat.antidiagonalTuple n i).card : ℝ) :=
      Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
    calc (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2)
        = ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2 := by ring
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcard_nn (hGfun_nn i))
          linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)]
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i + vol) * (1 + ‖iteratedCovGrad (I := I) g₀ r s i P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_
            (by linarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i P‖)])
          linarith

theorem antidiagonalTupleGrid_integral_radiusFree
    (g₀ : SmoothRiemannianMetric I M) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) :=
  atgGridIntRs (I := I) (M := M) g₀ 0 2 hΛ₀0

theorem bfGridWinIntRs
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Klow : ℕ → ℝ, (∀ i, 0 ≤ Klow i) ∧ ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧
      ∀ (P : SmoothCcTensor g₀ r s)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
                  ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
                    ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Klow i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) +
                Ktop i * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2 := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := atgGridIntRs (I := I) (M := M) g₀ r s hΛ₀0
  refine ⟨fun i => ∑ k ∈ Finset.range (i + 3), Kt k,
    fun i => Finset.sum_nonneg (fun k _ => hKt_nn k),
    fun i => Kt (i + 2), fun i => hKt_nn (i + 2), ?_⟩
  intro P hsup i
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
    ((iteratedCovGrad (I := I) g₀ r s l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r (s + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ r s l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ r s l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r (s + l) x
        ((iteratedCovGrad (I := I) g₀ r s l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ r s l P) x]
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGrid]
    refine continuous_finsetSum _ (fun k _ => ?_)
    refine continuous_finsetSum _ (fun n _ => ?_)
    refine continuous_finsetSum _ (fun e _ => ?_)
    exact continuous_finsetProd _ (fun m _ => hcont (e m))
  have hint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  have hint_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k => (hKt P hsup k).1
  have hint2_k : ∀ k : ℕ,
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) :=
    fun k => (hKt P hsup k).2
  have hmaj_int : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integrable_finsetSum _ (fun k _ => hint_k k)
  have hmono : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) ≤
        ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k := by
    intro x
    rw [Combinatorics.boundedFactorGridWindow]
    exact Finset.sum_le_sum (fun k _ =>
      Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid (b x) (hb x) (i + 1) k)
  refine le_trans (MeasureTheory.integral_mono hint hmaj_int hmono) ?_
  rw [MeasureTheory.integral_finsetSum _ (fun k _ => hint_k k)]
  have hstep1 : (∑ k ∈ Finset.range (i + 3),
        ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (i + 3), Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) :=
    Finset.sum_le_sum (fun k _ => hint2_k k)
  refine le_trans hstep1 ?_
  change (∑ k ∈ Finset.range (i + 3),
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)) ≤
      (∑ k ∈ Finset.range (i + 3), Kt k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) +
        Kt (i + 2) * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2
  have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hLHS : (∑ k ∈ Finset.range (i + 3),
        Kt k * (1 + ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)) =
      (∑ k ∈ Finset.range (i + 3), Kt k) +
        ∑ k ∈ Finset.range (i + 3),
          Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hLHS]
  have hjsplit : (∑ k ∈ Finset.range (i + 3),
        Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) =
      (∑ k ∈ Finset.range (i + 2),
          Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) +
        Kt (i + 2) * ‖iteratedCovGrad (I := I) g₀ r s (i + 2) P‖ ^ 2 := by
    rw [show i + 3 = (i + 2) + 1 from rfl, Finset.sum_range_succ]
  rw [hjsplit]
  have hlow : (∑ k ∈ Finset.range (i + 2),
        Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2) ≤
      (∑ k ∈ Finset.range (i + 3), Kt k) *
        ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
    calc (∑ k ∈ Finset.range (i + 2),
            Kt k * ‖iteratedCovGrad (I := I) g₀ r s k P‖ ^ 2)
        ≤ ∑ k ∈ Finset.range (i + 2),
            Kt k * ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          apply Finset.sum_le_sum; intro k hk
          refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
          exact Finset.single_le_sum
            (f := fun j => ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2)
            (fun j _ => sq_nonneg _) hk
      _ = (∑ k ∈ Finset.range (i + 2), Kt k) *
            ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ (∑ k ∈ Finset.range (i + 3), Kt k) *
            ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hS_nn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hKt_nn k)
          intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
  have hexp : (∑ k ∈ Finset.range (i + 3), Kt k) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2) =
      (∑ k ∈ Finset.range (i + 3), Kt k) +
        (∑ k ∈ Finset.range (i + 3), Kt k) *
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ r s j P‖ ^ 2 := by
    ring
  linarith [hlow, hexp]

theorem boundedFactorGridWindow_integral_radiusFree_topOrderSeparated
    (g₀ : SmoothRiemannianMetric I M) {Λ₀ : ℝ} (hΛ₀0 : 0 ≤ Λ₀) :
    ∃ Klow : ℕ → ℝ, (∀ i, 0 ≤ Klow i) ∧ ∃ Ktop : ℕ → ℝ, (∀ i, 0 ≤ Ktop i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        (_hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ₀ ^ 2)
        (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Klow i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Ktop i * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
  bfGridWinIntRs (I := I) (M := M) g₀ 0 2 hΛ₀0

end TopOrderSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry

end
