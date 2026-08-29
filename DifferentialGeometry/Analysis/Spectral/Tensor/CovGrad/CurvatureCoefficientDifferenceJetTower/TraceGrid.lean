import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace

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

namespace CurvatureCoefficientDifferenceJetTower

theorem exists_riemannianFiberNormSq_iteratedCovGrad_pairTraceOp_diff_grid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CΔ : ℕ → ℝ, (∀ j, 0 ≤ CΔ j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) ≤
          CΔ j * ∑ l ∈ Finset.range (j + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨c2, hc2_nn, hc2⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  obtain ⟨c4, hc4_nn, hc4⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : 0 ≤ dim := Nat.cast_nonneg _
  set CDS : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j + 1), CD l with hCDS_def
  have hCDS_nn : ∀ j, 0 ≤ CDS j := by
    intro j
    rw [hCDS_def]
    exact Finset.sum_nonneg fun l _ => hCD_nn l
  have hCDS_mono : ∀ {j j' : ℕ}, j ≤ j' → CDS j ≤ CDS j' := by
    intro j j' hj
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) (fun l _ _ => hCD_nn l)
  have hCD_le_CDS : ∀ {l j : ℕ}, l ≤ j → CD l ≤ CDS j := by
    intro l j hl
    exact Finset.single_le_sum (f := fun l' => CD l') (fun l' _ => hCD_nn l')
      (Finset.mem_range.mpr (by omega))
  clear_value CDS
  set K2 : ℕ → ℝ := fun m => operatorFieldApplicationGdiag (E := E) m * c2 * dim ^ (2 + 1) * CDS m with hK2_def
  set K4 : ℕ → ℝ := fun m => operatorFieldApplicationGdiag (E := E) m * c4 * dim ^ (4 + 1) * CDS m with hK4_def
  have hK2_nn : ∀ m, 0 ≤ K2 m := by
    intro m
    rw [hK2_def]
    have := operatorFieldApplicationGdiag_nonneg (E := E) m
    have := hCDS_nn m
    positivity
  have hK4_nn : ∀ m, 0 ≤ K4 m := by
    intro m
    rw [hK4_def]
    have := operatorFieldApplicationGdiag_nonneg (E := E) m
    have := hCDS_nn m
    positivity
  have hK2val : ∀ m, K2 m = operatorFieldApplicationGdiag (E := E) m * c2 * dim ^ (2 + 1) * CDS m := fun m => by
    rw [hK2_def]
  have hK4val : ∀ m, K4 m = operatorFieldApplicationGdiag (E := E) m * c4 * dim ^ (4 + 1) * CDS m := fun m => by
    rw [hK4_def]
  clear_value K2 K4
  refine ⟨fun j => 2 * (operatorFieldApplicationGdiag (E := E) j *
      ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
        K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) +
    2 * (operatorFieldApplicationGdiag (E := E) j *
      ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
        c2 * K4 l * gridSumPairCount (m + 1) (l + 1)),
    fun j => by
      have h1 : 0 ≤ ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1) :=
        Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
          mul_nonneg (mul_nonneg (hK2_nn m) (by
            have := hK4_nn l
            linarith)) (gridSumPairCount_nonneg _ _)
      have h2 : 0 ≤ ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1) :=
        Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
          mul_nonneg (mul_nonneg hc2_nn (hK4_nn l)) (gridSumPairCount_nonneg _ _)
      have h3 := operatorFieldApplicationGdiag_nonneg (E := E) j
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  have hGg_nn : ∀ m, 0 ≤ ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l :=
    fun m => Finset.sum_nonneg fun l _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hGg_one : ∀ m : ℕ, (1 : ℝ) ≤ ∑ l ∈ Finset.range (m + 1),
      Combinatorics.antidiagonalTupleGrid b l := by
    intro m
    calc (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
          (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l :=
          Finset.single_le_sum
            (f := fun l => Combinatorics.antidiagonalTupleGrid b l)
            (fun l _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb l)
            (Finset.mem_range.mpr (by omega))
  have hQjets : ∀ (ss : ℕ) (cS : ℝ), 0 ≤ cS →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ss y
        ((cometricDoubleTraceField (I := I) g₀ ss).toSection y) ≤ cS) →
      ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + m) x
          ((iteratedCovGrad (I := I) g₀ (ss + 2) ss m
            (ccOperatorFieldComp (I := I) (M := M) g₀ (ss + 2) (ss + 2) ss
              (cometricDoubleTraceField (I := I) g₀ ss)
              (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) ≤
        (operatorFieldApplicationGdiag (E := E) m * cS * dim ^ (ss + 1) * CDS m) *
          ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
    intro ss cS hcS_nn hcS m
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ m (ss + 2) (ss + 2) ss
      (cometricDoubleTraceField (I := I) g₀ ss)
      (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) x) ?_
    have hphi : ∀ m' ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + m') x
            ((iteratedCovGrad (I := I) g₀ (ss + 2) ss m'
              (cometricDoubleTraceField (I := I) g₀ ss)).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - m'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) ≤
        (if m' = 0 then
          cS * ∑ l ∈ Finset.range (m + 1),
            dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l)
        else 0) := by
      intro m' hm'
      match m' with
      | 0 =>
          rw [if_pos rfl]
          have hphi0 : riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + 0) x
              ((iteratedCovGrad (I := I) g₀ (ss + 2) ss 0
                (cometricDoubleTraceField (I := I) g₀ ss)).toSection x) ≤ cS := by
            rw [iteratedCovGrad_zero]
            exact hcS x
          have hSI : ∀ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) ≤
              dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
            intro l _
            refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
              (I := I) (M := M) g₀ (ss + 1) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) l x) ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact hCD g₁ T htie hδ_le hδ0 hbound l x
          have hsum_le : (∑ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x)) ≤
              ∑ l ∈ Finset.range (m + 1),
                dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
            refine le_trans (Finset.sum_le_sum hSI) ?_
            exact le_of_eq (by norm_num)
          have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) :=
            Finset.sum_nonneg fun l _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x _
          exact mul_le_mul hphi0 hsum_le hsum_nn hcS_nn
      | (m'' + 1) =>
          rw [if_neg (by omega)]
          rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ (ss + 2) ss
            (cometricDoubleTraceField (I := I) g₀ ss)
            (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ ss) m'']
          rw [show ((0 : SmoothCcTensor g₀ (ss + 2) (ss + (m'' + 1))).toSection x) =
              (0 : TensorRSSpace (ss + 2) (ss + (m'' + 1)) I x) from by
            rw [SmoothCcTensor.toSection_zero]; rfl]
          rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (ss + 2) (ss + (m'' + 1)) x]
          rw [zero_mul]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hphi)
      (operatorFieldApplicationGdiag_nonneg (E := E) m)) ?_
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    have hinner : (∑ l ∈ Finset.range (m + 1),
        dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l)) ≤
        dim ^ (ss + 1) * CDS m *
          ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl_le : l ≤ m := by
        rw [Finset.mem_range] at hl; omega
      have hgrid_nn := Combinatorics.antidiagonalTupleGrid_nonneg b hb l
      have hCDl := hCD_le_CDS hl_le
      have hd : (0 : ℝ) ≤ dim ^ (ss + 1) := by positivity
      have hkey : CD l * Combinatorics.antidiagonalTupleGrid b l ≤
          CDS m * Combinatorics.antidiagonalTupleGrid b l :=
        mul_le_mul_of_nonneg_right hCDl hgrid_nn
      nlinarith [hkey, hd]
    calc operatorFieldApplicationGdiag (E := E) m *
          (cS * ∑ l ∈ Finset.range (m + 1),
            dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l))
        ≤ operatorFieldApplicationGdiag (E := E) m *
            (cS * (dim ^ (ss + 1) * CDS m *
              ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l)) := by
          refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) m)
          exact mul_le_mul_of_nonneg_left hinner hcS_nn
      _ = (operatorFieldApplicationGdiag (E := E) m * cS * dim ^ (ss + 1) * CDS m) *
            ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
          ring
  set Ggrid : ℕ → ℝ := fun m => ∑ l ∈ Finset.range (m + 1),
    Combinatorics.antidiagonalTupleGrid b l with hGgrid_def
  have hGgrid_nn : ∀ m, 0 ≤ Ggrid m := fun m => hGg_nn m
  have hGgrid_one : ∀ m, (1 : ℝ) ≤ Ggrid m := fun m => hGg_one m
  have hGgrid_pair : ∀ {m l : ℕ}, m + l ≤ j →
      Ggrid m * Ggrid l ≤ gridSumPairCount (m + 1) (l + 1) * Ggrid j := by
    intro m l hml
    have h := gridSum_mul_gridSum_le b hb (m + 1) (l + 1) (j + 1) (by omega)
    exact h
  have hQ2jets := hQjets 2 c2 hc2_nn hc2
  have hQ4jets := hQjets 4 c4 hc4_nn hc4
  have hPhi2jets : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 4 2 m
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ c2 * Ggrid m := by
    intro m
    match m with
    | 0 =>
        rw [iteratedCovGrad_zero]
        refine le_trans (hc2 x) ?_
        nlinarith [hGgrid_one 0, hc2_nn]
    | (m' + 1) =>
        rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) m']
        rw [show ((0 : SmoothCcTensor g₀ 4 (2 + (m' + 1))).toSection x) =
            (0 : TensorRSSpace 4 (2 + (m' + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (2 + (m' + 1)) x]
        exact mul_nonneg hc2_nn (hGgrid_nn (m' + 1))
  have hP4jets : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 6 4 l
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (2 * K4 l + 2 * c4) * Ggrid l := by
    intro l
    have hsec : (iteratedCovGrad (I := I) g₀ 6 4 l
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x =
        (iteratedCovGrad (I := I) g₀ 6 4 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x +
        (iteratedCovGrad (I := I) g₀ 6 4 l
          (cometricDoubleTraceField (I := I) g₀ 4)).toSection x := by
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
      rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 6 (4 + l) x _ _) ?_
    have h1 := hQ4jets l
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 6 4 l
          (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) ≤ c4 * Ggrid l := by
      match l with
      | 0 =>
          rw [iteratedCovGrad_zero]
          refine le_trans (hc4 x) ?_
          nlinarith [hGgrid_one 0, hc4_nn]
      | (l' + 1) =>
          rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 4) l']
          rw [show ((0 : SmoothCcTensor g₀ 6 (4 + (l' + 1))).toSection x) =
              (0 : TensorRSSpace 6 (4 + (l' + 1)) I x) from by
            rw [SmoothCcTensor.toSection_zero]; rfl]
          rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 6 (4 + (l' + 1)) x]
          exact mul_nonneg hc4_nn (hGgrid_nn (l' + 1))
    rw [hK4val l]
    linarith [h1, h2]
  have hDelta : pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
          (cometricDoubleTraceField (I := I) g₀ 4)
          (slotInsertEndoCc (I := I) (M := M) g₀ 5
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))) := by
    rw [show pairTraceOp (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) from rfl]
    rw [pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 2]
    rw [operatorFieldComposition_add_left_cc (I := I) (M := M) g₀ 6 4 2]
    conv_lhs =>
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
    rw [operatorFieldComposition_add_right (I := I) (M := M) g₀ 6 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)]
    rw [pairTraceOp_self_eq (I := I) (M := M) g₀]
    rw [phiDtPair]
    conv_rhs =>
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
    rw [operatorFieldComposition_add_right (I := I) (M := M) g₀ 6 4 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))]
    abel
  rw [hDelta]
  have hsplitsec : (iteratedCovGrad (I := I) g₀ 6 2 j
      (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
          (cometricDoubleTraceField (I := I) g₀ 4)
          (slotInsertEndoCc (I := I) (M := M) g₀ 5
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))))).toSection x =
      (iteratedCovGrad (I := I) g₀ 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x +
      (iteratedCovGrad (I := I) g₀ 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))))).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsplitsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 6 (2 + j) x _ _) ?_
  have hterm1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) j *
        ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 6 4 2
      (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
      (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) x) ?_
    have hcell : ∀ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
        (∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
      intro m hm
      have hm_le : m ≤ j := by
        rw [Finset.mem_range] at hm; omega
      have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 4 2 m
            (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
              (cometricDoubleTraceField (I := I) g₀ 2)
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) ≤
          K2 m * Ggrid m := by
        rw [hK2val m]
        exact hQ2jets m
      have hA2 : (∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
          ∑ l ∈ Finset.range (j + 1 - m), (2 * K4 l + 2 * c4) * Ggrid l :=
        Finset.sum_le_sum fun l _ => hP4jets l
      have hnn1 : 0 ≤ ∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
      have hK2G_nn : 0 ≤ K2 m * Ggrid m := mul_nonneg (hK2_nn m) (hGgrid_nn m)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
          ≤ (K2 m * Ggrid m) *
            ∑ l ∈ Finset.range (j + 1 - m), (2 * K4 l + 2 * c4) * Ggrid l :=
            mul_le_mul hA1 hA2 hnn1 hK2G_nn
        _ = ∑ l ∈ Finset.range (j + 1 - m),
              (K2 m * (2 * K4 l + 2 * c4)) * (Ggrid m * Ggrid l) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
        _ ≤ ∑ l ∈ Finset.range (j + 1 - m),
              (K2 m * (2 * K4 l + 2 * c4)) * (gridSumPairCount (m + 1) (l + 1) * Ggrid j) := by
            refine Finset.sum_le_sum fun l hl => ?_
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · refine hGgrid_pair ?_
              rw [Finset.mem_range] at hl
              omega
            · have := hK2_nn m
              have := hK4_nn l
              positivity
        _ = (∑ l ∈ Finset.range (j + 1 - m),
              K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
    calc operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 4 2 m
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
                    (cometricDoubleTraceField (I := I) g₀ 2)
                    (slotInsertEndoCc (I := I) (M := M) g₀ 3
                      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - m),
                riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 6 4 l
                    (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
        ≤ operatorFieldApplicationGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1),
              (∑ l ∈ Finset.range (j + 1 - m),
                K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (operatorFieldApplicationGdiag_nonneg (E := E) j)
      _ = (operatorFieldApplicationGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
              K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
          rw [← Finset.sum_mul]
          ring
  have hterm2 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))))).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) j *
        ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 6 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
        (cometricDoubleTraceField (I := I) g₀ 4)
        (slotInsertEndoCc (I := I) (M := M) g₀ 5
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))) x) ?_
    have hcell : ∀ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
                  (cometricDoubleTraceField (I := I) g₀ 4)
                  (slotInsertEndoCc (I := I) (M := M) g₀ 5
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) ≤
        (∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
      intro m hm
      have hm_le : m ≤ j := by
        rw [Finset.mem_range] at hm; omega
      have hA1 := hPhi2jets m
      have hA2 : (∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (slotInsertEndoCc (I := I) (M := M) g₀ 5
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x)) ≤
          ∑ l ∈ Finset.range (j + 1 - m), K4 l * Ggrid l := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [hK4val l]
        exact hQ4jets l
      have hnn1 : 0 ≤ ∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (slotInsertEndoCc (I := I) (M := M) g₀ 5
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
      have hc2G_nn : 0 ≤ c2 * Ggrid m := mul_nonneg hc2_nn (hGgrid_nn m)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
                  (cometricDoubleTraceField (I := I) g₀ 4)
                  (slotInsertEndoCc (I := I) (M := M) g₀ 5
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x)
          ≤ (c2 * Ggrid m) * ∑ l ∈ Finset.range (j + 1 - m), K4 l * Ggrid l :=
            mul_le_mul hA1 hA2 hnn1 hc2G_nn
        _ = ∑ l ∈ Finset.range (j + 1 - m), (c2 * K4 l) * (Ggrid m * Ggrid l) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
        _ ≤ ∑ l ∈ Finset.range (j + 1 - m),
              (c2 * K4 l) * (gridSumPairCount (m + 1) (l + 1) * Ggrid j) := by
            refine Finset.sum_le_sum fun l hl => ?_
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · refine hGgrid_pair ?_
              rw [Finset.mem_range] at hl
              omega
            · have := hK4_nn l
              positivity
        _ = (∑ l ∈ Finset.range (j + 1 - m),
              c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
    calc operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 4 2 m
                  (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - m),
                riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 6 4 l
                    (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
                      (cometricDoubleTraceField (I := I) g₀ 4)
                      (slotInsertEndoCc (I := I) (M := M) g₀ 5
                        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x)
        ≤ operatorFieldApplicationGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1),
              (∑ l ∈ Finset.range (j + 1 - m),
                c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (operatorFieldApplicationGdiag_nonneg (E := E) j)
      _ = (operatorFieldApplicationGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
              c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
          rw [← Finset.sum_mul]
          ring
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
            (ccOperatorFieldComp (I := I) (M := M) g₀ 4 4 2
              (cometricDoubleTraceField (I := I) g₀ 2)
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))
            (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 6 6 4
              (cometricDoubleTraceField (I := I) g₀ 4)
              (slotInsertEndoCc (I := I) (M := M) g₀ 5
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))))).toSection x)
      ≤ 2 * ((operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j) +
        2 * ((operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j) := by
        linarith [hterm1, hterm2]
    _ = (2 * (operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) +
        2 * (operatorFieldApplicationGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            c2 * K4 l * gridSumPairCount (m + 1) (l + 1))) * Ggrid j := by
        ring

omit [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_iteratedCovGrad_WBform_le (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by
  have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 6 l
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
  rw [heq1]
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtend (I := I) (M := M) g₀ 0 4 X)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 X) l x
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x)) :=
        mul_le_mul_of_nonneg_left
          (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 X l x) hfr
    _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by ring

end CurvatureCoefficientDifferenceJetTower

private lemma tracegrid_add_tail
    (x a b A B : ℝ)
    (hx : x ≤ 2 * a + 2 * b) (ha : a ≤ A) (hb : b ≤ B) :
    (2 : ℝ) ^ 2 * x ≤ (2 : ℝ) ^ 2 * (2 * A + 2 * B) := by
  have hsum : x ≤ 2 * A + 2 * B :=
    hx.trans (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
      (mul_le_mul_of_nonneg_left hb (by norm_num)))
  exact mul_le_mul_of_nonneg_left hsum (sq_nonneg 2)

theorem riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            (∑ n ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - j),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) := by
  classical
  obtain ⟨CΔ, hCΔ_nn, hCΔ⟩ := exists_riemannianFiberNormSq_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (phiDtPair (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (phiDtPair (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : 0 ≤ dim := Nat.cast_nonneg _
  refine ⟨fun i => 8 * (cB i * (dim * dim)) +
      8 * (operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2),
    fun i => by
      have h1 := hcB0 i
      have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), CΔ j :=
        Finset.sum_nonneg fun j _ => hCΔ_nn j
      have h3 := operatorFieldApplicationGdiag_nonneg (E := E) i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set L01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hL01_def
  set Ldiff : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hLdiff_def
  set Lterm : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x) with hLterm_def
  have hLterm_nn : ∀ l, 0 ≤ Lterm l := by
    intro l
    rw [hLterm_def]
    exact add_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
  set RHS : ℝ := ∑ j ∈ Finset.range (i + 1),
    Combinatorics.antidiagonalTupleGrid b j * ∑ l ∈ Finset.range (i + 1 - j), Lterm l
    with hRHS_def
  have hRHS_cell_nn : ∀ j, 0 ≤ Combinatorics.antidiagonalTupleGrid b j *
      ∑ l ∈ Finset.range (i + 1 - j), Lterm l := fun j =>
    mul_nonneg (Combinatorics.antidiagonalTupleGrid_nonneg b hb j)
      (Finset.sum_nonneg fun l _ => hLterm_nn l)
  have hRHS_nn : 0 ≤ RHS := by
    rw [hRHS_def]
    exact Finset.sum_nonneg fun j _ => hRHS_cell_nn j
  have hgoal_eq : (∑ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
      ∑ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x))) = RHS := rfl
  rw [hgoal_eq]
  clear_value RHS
  have hdecomp : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))) := by
    rw [riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₁]
    rw [riemannMixedCoeff_eq_pairTrace_L01 (I := I) (M := M) g₀ g₁]
    rw [← smul_sub]
    congr 1
    rw [operatorFieldComposition_sub_left_cc (I := I) (M := M) g₀ 2 6 2]
    have hWsub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff) =
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) := by
      rw [hLdiff_def]
      rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) =
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) -
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) from by
        rw [show ∀ Y : SmoothCcTensor g₀ 0 4,
            slotExtendIter (I := I) (M := M) g₀ 0 4 2 Y =
            slotExtend (I := I) (M := M) g₀ 1 5
              (slotExtend (I := I) (M := M) g₀ 0 4 Y) from fun Y => rfl]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 0 4]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 1 5]
        rfl]
      rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 sigmaE0]
    rw [hWsub]
    rw [operatorFieldComposition_sub_right_cc (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)]
    abel
  rw [hdecomp]
  have hsmulsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) := by
    rw [iteratedCovGrad_smul_b, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add]
    rfl
  rw [hsmulsec, riemannianFiberNormSq_smul_b]
  have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
      (cB i * (dim * dim)) * RHS := by
    rw [pairTraceOp_self_eq (I := I) (M := M) g₀]
    rw [iteratedCovGrad_operatorFieldComposition_parallel (I := I) (M := M) g₀ 2 6 2
      (phiDtPair (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) _ i]
    have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
            ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
              (phiDtPair (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x) := by
      rw [operatorFieldComposition_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x _ _
    refine le_trans hcomp ?_
    have h1 := hcBb i x
    have h2 := riemannianFiberNormSq_iteratedCovGrad_WBform_le (I := I) (M := M) g₀ Ldiff i x
    rw [← hdim_def] at h2
    have hLd_le_RHS : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ RHS := by
      rw [hRHS_def]
      have hcell0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤
          Combinatorics.antidiagonalTupleGrid b 0 * ∑ l ∈ Finset.range (i + 1 - 0), Lterm l := by
        rw [Combinatorics.antidiagonalTupleGrid_zero, one_mul]
        have hLi : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ Lterm i := by
          rw [hLterm_def]
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i L01).toSection x)
          linarith
        refine le_trans hLi ?_
        exact Finset.single_le_sum (f := fun l => Lterm l) (fun l _ => hLterm_nn l)
          (Finset.mem_range.mpr (by omega))
      refine le_trans hcell0 ?_
      exact Finset.single_le_sum
        (f := fun j => Combinatorics.antidiagonalTupleGrid b j *
          ∑ l ∈ Finset.range (i + 1 - j), Lterm l)
        (fun j _ => hRHS_cell_nn j) (Finset.mem_range.mpr (by omega))
    have hWB_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
    have hLd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
        ≤ cB i * ((dim * dim) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)) := by
          simpa only [mul_assoc] using mul_le_mul h1 h2 hWB_nn (hcB0 i)
      _ ≤ cB i * ((dim * dim) * RHS) := by
          have hdd : (0 : ℝ) ≤ dim * dim := by positivity
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left hLd_le_RHS (mul_nonneg (hcB0 i) hdd))
      _ = (cB i * (dim * dim)) * RHS := by ring
  have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) * RHS := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 2 6 2
      (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) x) ?_
    have hL11 : ∀ l : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ 2 * Lterm l := by
      intro l
      have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x := by
        rw [show riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ = L01 + Ldiff from by
          rw [hL01_def, hLdiff_def]
          abel]
        rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
      rw [hLterm_def]
      ring_nf
      rfl
    have hcell : ∀ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) ≤
        (CΔ j * (dim * dim) * 2) * RHS := by
      intro j hj
      have hj_le : j ≤ i := by
        rw [Finset.mem_range] at hj
        omega
      have hA1 := hCΔ g₁ T htie hδ_le hδ0 hbound j x
      have hA2 : (∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_WBform_le (I := I) (M := M) g₀
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) l x) ?_
        exact mul_le_mul_of_nonneg_left (hL11 l) (by positivity)
      have hA1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (pairTraceOp (I := I) (M := M) g₀ g₁ -
            pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x)
      have hA2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
      have hgrid_nn : 0 ≤ CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l' :=
        mul_nonneg (hCΔ_nn j) (Finset.sum_nonneg fun l' _ =>
          Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
      have hkey : (CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l') *
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) ≤
          (CΔ j * (dim * dim) * 2) * RHS := by
        have hexpand : (∑ l' ∈ Finset.range (j + 1),
            Combinatorics.antidiagonalTupleGrid b l') *
            (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤ RHS := by
          rw [Finset.sum_mul]
          rw [hRHS_def]
          have hstep : ∀ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l' *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤
              Combinatorics.antidiagonalTupleGrid b l' *
                ∑ l ∈ Finset.range (i + 1 - l'), Lterm l := by
            intro l' hl'
            refine mul_le_mul_of_nonneg_left ?_
              (Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr ?_) (fun l _ _ => hLterm_nn l)
            rw [Finset.mem_range] at hl'
            omega
          refine le_trans (Finset.sum_le_sum hstep) ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro j' _ _
          exact hRHS_cell_nn j'
        calc (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
              ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l)
            = (CΔ j * (dim * dim) * 2) *
              ((∑ l' ∈ Finset.range (j + 1), Combinatorics.antidiagonalTupleGrid b l') *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l)) := by
              have hfac : (∑ l ∈ Finset.range (i + 1 - j),
                  (dim * dim) * (2 * Lterm l)) =
                  (dim * dim * 2) * ∑ l ∈ Finset.range (i + 1 - j), Lterm l := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun l _ => by ring
              rw [hfac]
              ring
          _ ≤ (CΔ j * (dim * dim) * 2) * RHS := by
              refine mul_le_mul_of_nonneg_left hexpand ?_
              have := hCΔ_nn j
              positivity
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
          ≤ (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
            ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) :=
            mul_le_mul hA1 hA2 hA2_nn hgrid_nn
        _ ≤ (CΔ j * (dim * dim) * 2) * RHS := hkey
    calc operatorFieldApplicationGdiag (E := E) i *
          ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 6 2 j
                  (pairTraceOp (I := I) (M := M) g₀ g₁ -
                    pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - j),
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
                  ((iteratedCovGrad (I := I) g₀ 2 6 l
                    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
        ≤ operatorFieldApplicationGdiag (E := E) i *
            ∑ j ∈ Finset.range (i + 1), (CΔ j * (dim * dim) * 2) * RHS :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (operatorFieldApplicationGdiag_nonneg (E := E) i)
      _ = (operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) *
            RHS := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
      ≤ (2 : ℝ) ^ 2 * (2 * ((operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2) * RHS) + 2 * ((cB i * (dim * dim)) * RHS)) := by
        have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x)
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
        exact tracegrid_add_tail _ _ _ _ _ hadd hT1 hT2
    _ ≤ (8 * (cB i * (dim * dim)) +
          8 * (operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2)) * RHS := by
        have hEq : (2 : ℝ) ^ 2 *
              (2 * ((operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
                  (dim * dim) * 2) * RHS) +
                2 * ((cB i * (dim * dim)) * RHS)) =
            (8 * (cB i * (dim * dim)) +
              8 * (operatorFieldApplicationGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
                (dim * dim) * 2)) * RHS := by
          ring
        rw [hEq]

theorem riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => CB i * CA i, fun i => mul_nonneg (hCB_nn i) (hCA_nn i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  refine le_trans (hCB g₁ i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCA g₁ T htie hδ_le hδ0 hbound i x) (hCB_nn i)

end Spectral
end Analysis
end DifferentialGeometry

end
