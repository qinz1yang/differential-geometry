import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.SummandLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.Bounds.PointwiseLipschitz
import DifferentialGeometry.Geometry.Curvature.Coordinates.Ricci.Perturbation
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem chartLie_abs_le
    (g gBase : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E)
    {Q₀ Q₁ V DV : ℝ}
    (hQ₀ : 0 ≤ Q₀) (hQ₁ : 0 ≤ Q₁) (hV : 0 ≤ V) (hDV : 0 ≤ DV)
    (hgram : ∀ a c : Fin (Module.finrank ℝ E),
      |chartGramOnE (I := I) g α a c y| ≤ Q₀)
    (hdgram : ∀ m a c : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g α a c) y| ≤ Q₁)
    (hvf : ∀ k : Fin (Module.finrank ℝ E),
      |chartDeTurckVFComp (I := I) g gBase α k y| ≤ V)
    (hdvf : ∀ m k : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartDeTurckVFComp (I := I) g gBase α k) y| ≤ DV) :
    |chartLieDeTurckComp (I := I) g gBase α i j y| ≤
      (Module.finrank ℝ E : ℝ) * (V * Q₁ + 2 * Q₀ * DV) := by
  classical
  have hsum_prod : ∀ (A B : Fin (Module.finrank ℝ E) → ℝ)
      (CA CB : ℝ), 0 ≤ CA → 0 ≤ CB →
      (∀ k, |A k| ≤ CA) → (∀ k, |B k| ≤ CB) →
      |∑ k, A k * B k| ≤ (Module.finrank ℝ E : ℝ) * (CA * CB) := by
    intro A B CA CB hCA hCB hA hB
    calc
      |∑ k, A k * B k| ≤ ∑ k, |A k * B k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin (Module.finrank ℝ E), CA * CB := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hA k) (hB k) (abs_nonneg _) hCA
      _ = (Module.finrank ℝ E : ℝ) * (CA * CB) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hfirst := hsum_prod
    (fun k => chartDeTurckVFComp (I := I) g gBase α k y)
    (fun k => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
    V Q₁ hV hQ₁ hvf (fun k => hdgram k i j)
  have hsecond := hsum_prod
    (fun k => chartGramOnE (I := I) g α k j y)
    (fun k => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
      (chartDeTurckVFComp (I := I) g gBase α k) y)
    Q₀ DV hQ₀ hDV (fun k => hgram k j) (fun k => hdvf i k)
  have hthird := hsum_prod
    (fun k => chartGramOnE (I := I) g α i k y)
    (fun k => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
      (chartDeTurckVFComp (I := I) g gBase α k) y)
    Q₀ DV hQ₀ hDV (fun k => hgram i k) (fun k => hdvf j k)
  rw [chartLieDeTurckComp_def]
  calc
    |(∑ k : Fin (Module.finrank ℝ E),
        chartDeTurckVFComp (I := I) g gBase α k y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (chartDeTurckVFComp (I := I) g gBase α k) y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
            (chartDeTurckVFComp (I := I) g gBase α k) y)|
        ≤ |(∑ k : Fin (Module.finrank ℝ E),
              chartDeTurckVFComp (I := I) g gBase α k y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y) +
            (∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α k j y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                  (chartDeTurckVFComp (I := I) g gBase α k) y)| +
          |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α i k y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                  (chartDeTurckVFComp (I := I) g gBase α k) y| := abs_add_le _ _
    _ ≤ (|(∑ k : Fin (Module.finrank ℝ E),
              chartDeTurckVFComp (I := I) g gBase α k y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)| +
            |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α k j y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                  (chartDeTurckVFComp (I := I) g gBase α k) y|) +
          |∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) g α i k y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                  (chartDeTurckVFComp (I := I) g gBase α k) y| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ ((Module.finrank ℝ E : ℝ) * (V * Q₁) +
          (Module.finrank ℝ E : ℝ) * (Q₀ * DV)) +
        (Module.finrank ℝ E : ℝ) * (Q₀ * DV) :=
          add_le_add (add_le_add hfirst hsecond) hthird
    _ = (Module.finrank ℝ E : ℝ) * (V * Q₁ + 2 * Q₀ * DV) := by ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartRHS_abs_le
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E)
    {CRic CLie : ℝ}
    (hRic : |chartRicciTensor (I := I) g α i j y| ≤ CRic)
    (hLie : |chartLieDeTurckComp (I := I) g gBase α i j y| ≤ CLie) :
    |chartDeTurckRHSComp (I := I) gBase g α i j y| ≤ 2 * CRic + CLie := by
  rw [chartDeTurckRHSComp_def]
  calc
    |(-2 : ℝ) * chartRicciTensor (I := I) g α i j y +
        chartLieDeTurckComp (I := I) g gBase α i j y|
        ≤ |(-2 : ℝ) * chartRicciTensor (I := I) g α i j y| +
          |chartLieDeTurckComp (I := I) g gBase α i j y| := abs_add_le _ _
    _ ≤ 2 * CRic + CLie := by
      apply add_le_add
      · rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left hRic (by norm_num)
      · exact hLie

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
