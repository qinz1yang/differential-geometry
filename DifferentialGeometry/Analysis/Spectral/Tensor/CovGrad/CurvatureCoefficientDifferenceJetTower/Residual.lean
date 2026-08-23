import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Envelope

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
      nlinarith [hKt_nn k, sq_nonneg R, hsum_nn,
        mul_nonneg (hKt_nn k) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hsum_nn)]
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
      nlinarith [hKt_nn (i + 2), hsum_nn, sq_nonneg R,
        mul_nonneg (hKt_nn (i + 2)) hsum_nn,
        mul_nonneg (mul_nonneg (hKt_nn (i + 2)) (sq_nonneg R)) hsum_nn]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

end TopOrderSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry

end
