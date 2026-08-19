import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.ResidualFlat
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Residual

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

end TopOrderSeparatedResidualIntegrator

end Spectral
end Analysis
end DifferentialGeometry

end
