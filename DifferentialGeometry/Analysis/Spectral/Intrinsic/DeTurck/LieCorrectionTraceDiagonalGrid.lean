import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTraceFibreIdentities
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerAppCcRSProductGridRankLeftBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

/-!
# Pointwise diagonal-grid bounds for moving trace operators

This file controls the covariant jets of the moving cometric double trace,
with arbitrary passenger rank, by the antidiagonal metric-jet grid.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Pointwise product-grid control of a moving rank-`(p + 2, p)` trace. -/
theorem lc0Tr_pointwise_antidiagonalGrid_le
    (p : ℕ) (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin (p + 2))) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) p i
              (lc0Tr (I := I) (M := M) g₀ g₁ p σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) k := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndo_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  let Φ : SmoothCcTensor g₀ (p + 2) p := cometricDoubleTraceField (I := I) g₀ p
  have hS_ex : ∀ m : ℕ, ∃ S : ℝ, 0 ≤ S ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
        ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) ≤ S :=
    fun m => exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ (p + 2) (p + m)
      (iteratedCovGrad (I := I) g₀ (p + 2) p m Φ)
  choose S hS_nn hS using hS_ex
  let fr : ℝ := Module.finrank ℝ E
  let CQ : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i *
    ∑ m ∈ Finset.range (i + 1),
      S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l
  let C : ℕ → ℝ := fun i => 2 * CQ i + 2 * S i
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCQ : ∀ i, 0 ≤ CQ i := by
    intro i
    exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun m _ => mul_nonneg (hS_nn m)
        (Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hfr (p + 1)) (hCD_nn l)))
  refine ⟨C, fun i => by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by norm_num) (hCQ i))
      (mul_nonneg (by norm_num) (hS_nn i)), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound σ i x
  let b : ℕ → ℝ := fun j =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
  let G : ℝ := ∑ k ∈ Finset.range (i + 1),
    Combinatorics.antidiagonalTupleGrid b k
  have hb : ∀ j, 0 ≤ b j := fun j =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hG_nn : 0 ≤ G := Finset.sum_nonneg fun k _ =>
    Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hG_one : (1 : ℝ) ≤ G := by
    calc
      (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
        (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ G := Finset.single_le_sum
        (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
        (Finset.mem_range.mpr (by omega))
  let W : SmoothCcTensor g₀ (p + 2) (p + 2) :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (p + 1)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁)
  have hW : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) ≤
        fr ^ (p + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
    intro l
    refine le_trans
      (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g₀ (p + 1)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hfr (p + 1))
    simpa only [b, Combinatorics.antidiagonalTupleGrid] using
      hCD g₁ P htie hδ_le hδ_nonneg hbound l x
  have hgrid_le : ∀ l, l < i + 1 →
      Combinatorics.antidiagonalTupleGrid b l ≤ G := by
    intro l hl
    exact Finset.single_le_sum
      (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
      (Finset.mem_range.mpr hl)
  have hcell : ∀ m ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) ≤
      (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G := by
    intro m hm
    have hmle : m ≤ i := by
      have := Finset.mem_range.mp hm
      omega
    have hsumW : (∑ l ∈ Finset.range (i + 1 - m),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - m),
          (fr ^ (p + 1) * CD l) * G := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hli : l < i + 1 := by
        have := Finset.mem_range.mp hl
        omega
      calc
        _ ≤ fr ^ (p + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := hW l
        _ ≤ fr ^ (p + 1) * (CD l * G) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hgrid_le l hli) (hCD_nn l))
            (pow_nonneg hfr (p + 1))
        _ = (fr ^ (p + 1) * CD l) * G := by ring
    have hsumW_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - m),
        riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x _
    calc
      _ ≤ S m * ∑ l ∈ Finset.range (i + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x) :=
        mul_le_mul_of_nonneg_right (hS m x) hsumW_nn
      _ ≤ S m * ∑ l ∈ Finset.range (i + 1 - m),
          (fr ^ (p + 1) * CD l) * G :=
        mul_le_mul_of_nonneg_left hsumW (hS_nn m)
      _ = (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G := by
        rw [← Finset.sum_mul]
        ring
  have hQ :
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p i
            (ccOperatorFieldComp (I := I) (M := M) g₀ (p + 2) (p + 2) p Φ W)).toSection x) ≤
        CQ i * G := by
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i (p + 2) (p + 2) p Φ W x) ?_
    calc
      diagonalGridGrowthFactor (E := E) i * ∑ m ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + m) x
              ((iteratedCovGrad (I := I) g₀ (p + 2) p m Φ).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - m),
              riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) ((p + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (p + 2) (p + 2) l W).toSection x)
          ≤ diagonalGridGrowthFactor (E := E) i * ∑ m ∈ Finset.range (i + 1),
              (S m * ∑ l ∈ Finset.range (i + 1 - m), fr ^ (p + 1) * CD l) * G :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
          (appCcGdiag_nonneg (E := E) i)
      _ = CQ i * G := by
        dsimp only [CQ]
        rw [← Finset.sum_mul]
        ring
  have hfixed :
      riemannianFiberNormSq (I := I) (M := M) g₀ (p + 2) (p + i) x
          ((iteratedCovGrad (I := I) g₀ (p + 2) p i Φ).toSection x) ≤
        S i * G :=
    (hS i x).trans (by nlinarith [hS_nn i, hG_one])
  rw [lc0Tr, riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq
    (I := I) (M := M) g₀ (p + 2) p
      (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ i x]
  rw [show lc0PureDT (I := I) (M := M) g₀ g₁ p =
      pureTrace (I := I) (M := M) g₀ g₁ p from rfl]
  rw [pureTrace_split (I := I) (M := M) g₀ g₁ p,
    iteratedCovGrad_add, SmoothCcTensor.toSection_add]
  refine le_trans
    (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (p + 2) (p + i) x _ _) ?_
  change 2 * _ + 2 * _ ≤ C i * G
  have hQ' := mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 2)
  have hfixed' := mul_le_mul_of_nonneg_left hfixed (by norm_num : (0 : ℝ) ≤ 2)
  change _ ≤ (2 * CQ i + 2 * S i) * G
  calc
    _ ≤ 2 * (CQ i * G) + 2 * (S i * G) := add_le_add hQ' hfixed'
    _ = (2 * CQ i + 2 * S i) * G := by ring

/-- Rank-two specialization of `lc0Tr_pointwise_antidiagonalGrid_le`. -/
theorem lc0Tr_two_pointwise_antidiagonalGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (lc0Tr (I := I) (M := M) g₀ g₁ 2 σ)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) k := by
  simpa only [Nat.reduceAdd] using
    lc0Tr_pointwise_antidiagonalGrid_le (I := I) (M := M) 2 g₀ hδ₀

end DifferentialGeometry.Analysis.Spectral

end
