import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Coefficients.ConnectionInsertionFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.FirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.CovariantDerivativeTerm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.EndomorphismTermBounds

noncomputable section


open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endoSlotZero_sub_h2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g s (A - B) =
      endoSlotZeroCcTensor (I := I) (M := M) g s A -
        endoSlotZeroCcTensor (I := I) (M := M) g s B := by
  change slotInsertEndoCc (I := I) (M := M) g s (A - B) =
    slotInsertEndoCc (I := I) (M := M) g s A -
      slotInsertEndoCc (I := I) (M := M) g s B
  exact slotInsertEndoCc_sub (I := I) (M := M) g s A B

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [SigmaCompactSpace M] in
private theorem lieCorrectionZeroKappa_eq_metricConnectionDifferenceLoweredCoefficient
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB =
      metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ gB := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieCorrectionZeroPureDT_eq_pureTrace_local
    (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ) :
    lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ p =
      pureTrace (I := I) (M := M) g₀ g₁ p := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem h2Jet_smul
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (a : ℝ) (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (a • W)‖ ^ 2) =
      a ^ 2 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private theorem lowJetSq_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (W : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  exact Finset.sum_nonneg fun q _ => sq_nonneg _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem gBound_mono
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hδδ' : δ ≤ δ')
    (hb : gFibreOpBound (I := I) (M := M) g h δ) :
    gFibreOpBound (I := I) (M := M) g h δ' := by
  intro x v w
  refine (hb x v w).trans ?_
  have hnn : 0 ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) =
        δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by ring
    _ ≤ δ' * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
      mul_le_mul_of_nonneg_right hδδ' hnn
    _ = δ' * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

private theorem hs3_of_jet3
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (T : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ D * A := by
  obtain ⟨C, hC, hhs⟩ := hs_le_jet (I := I) (M := M) g 2 3
  let D : ℝ := 2 * C
  refine ⟨D, mul_nonneg (by norm_num) hC, ?_⟩
  intro T A hA hTA
  let J : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hJ2 : J ^ 2 ≤ 4 * covariantJetNormSq (I := I) (M := M) g 3 T := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
    simpa only [J, Finset.card_range, Nat.cast_ofNat, covariantJetNormSq,
      Nat.reduceAdd] using h
  have hJ2A : J ^ 2 ≤ 4 * A ^ 2 :=
    hJ2.trans (mul_le_mul_of_nonneg_left hTA (by norm_num))
  have hJ : J ≤ 2 * A := by
    nlinarith
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ C * J := by
      have hhsT := hhs T
      rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num] at hhsT
      simpa only [J, Nat.reduceAdd] using hhsT
    _ ≤ C * (2 * A) := mul_le_mul_of_nonneg_left hJ hC
    _ = D * A := by simp only [D]; ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem h2Jet_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((2 : ℝ) • W)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real,
    norm_smul, Real.norm_eq_abs]
  norm_num
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem h2Jet_sum2
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) := by
    intro j hj
    rw [iteratedCovGrad_add]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s j W)
      (iteratedCovGrad (I := I) g r s j Z)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg
      (‖iteratedCovGrad (I := I) g r s j W‖ -
        ‖iteratedCovGrad (I := I) g r s j Z‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 2 * (A ^ 2 + B ^ 2) := by gcongr

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem h2Jet_sub
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W - Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hZneg : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (-Z)‖ ^ 2) ≤ B ^ 2 := by
    simpa only [iteratedCovGrad_neg, norm_neg] using hZ
  simpa only [sub_eq_add_neg] using
    h2Jet_sum2 (I := I) (M := M) g r s n W (-Z) A B hW hZneg

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem h2Jet_sum4
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W X Y Z : SmoothCcTensor g r s) (A B C D : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hX : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2) ≤ B ^ 2)
    (hY : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2) ≤ C ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ D ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((W + X) + (Y + Z))‖ ^ 2) ≤
      4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
  let AB : ℝ := Real.sqrt (2 * (A ^ 2 + B ^ 2))
  let CD : ℝ := Real.sqrt (2 * (C ^ 2 + D ^ 2))
  have hAB0 : 0 ≤ 2 * (A ^ 2 + B ^ 2) := by positivity
  have hCD0 : 0 ≤ 2 * (C ^ 2 + D ^ 2) := by positivity
  have hAB := h2Jet_sum2 (I := I) (M := M)
    g r s n W X A B hW hX
  have hCD := h2Jet_sum2 (I := I) (M := M)
    g r s n Y Z C D hY hZ
  have hsum := h2Jet_sum2 (I := I) (M := M)
    g r s n (W + X) (Y + Z) AB CD
    (by simpa only [AB, Real.sq_sqrt hAB0] using hAB)
    (by simpa only [CD, Real.sq_sqrt hCD0] using hCD)
  have hABsq : AB ^ 2 = 2 * (A ^ 2 + B ^ 2) := by
    simpa only [AB] using Real.sq_sqrt hAB0
  have hCDsq : CD ^ 2 = 2 * (C ^ 2 + D ^ 2) := by
    simpa only [CD] using Real.sq_sqrt hCD0
  calc
    _ ≤ 2 * (AB ^ 2 + CD ^ 2) := hsum
    _ = 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
      rw [hABsq, hCDsq]
      ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private theorem topNorm_le
    (g : SmoothRiemannianMetric I M) {P : SmoothCcTensor g 0 2} {A : ℝ}
    (hA : 0 ≤ A)
    (hP : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2) :
    ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A := by
  have hmem : 3 ∈ Finset.range 4 := by norm_num
  have hsingle : ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ^ 2 ≤ A ^ 2 :=
    (Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem).trans hP
  nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 3 P)]


theorem exists_deTurckLieConnectionDifferenceDerivativeCoefficient_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gB -
              deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ := bdCovDerivTermDiff_pointwise_gridWindow (I := I) (M := M) g₀ gB hδ₀
  obtain ⟨B0, B1, hB0, hB1, hgrid⟩ :=
    h2_grid_tame (I := I) (M := M) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  apply hgrid P
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)
    R A hR hA hP2 (topNorm_le (I := I) (M := M) g₀ hA hP3)
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGridWindow,
    Combinatorics.antidiagonalTupleGrid] using
      hpt g₁ P htie hδ_le hδ_nonneg hbound i x


theorem exists_deTurckLieCovariantDerivativeInsertion_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gB -
              deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ := bdEndoTermDiff_pointwise_gridWindow (I := I) (M := M) g₀ gB hδ₀
  obtain ⟨B0, B1, hB0, hB1, hgrid⟩ :=
    h2_grid_tame (I := I) (M := M) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  apply hgrid P
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)
    R A hR hA hP2 (topNorm_le (I := I) (M := M) g₀ hA hP3)
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGridWindow,
    Combinatorics.antidiagonalTupleGrid] using
      hpt g₁ P htie hδ_le hδ_nonneg hbound i x


theorem exists_lieCorrectionZeroInsertion_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gB -
              lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htr⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨CO, hCO, hoprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨BC0, BC1, hBC0, hBC1, hc⟩ :=
    connLow_tame (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨CA, hCA, haprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 0 1 2
  let Fix : SmoothCcTensor g₀ 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₀
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2
  let AF : ℝ := Real.sqrt SF
  let sn : ℝ := Real.sqrt (4 * (Module.finrank ℝ E : ℝ))
  let BO : ℝ → ℝ := fun R => CO * Bt R * AF
  let B0 : ℝ → ℝ := fun R => sn * (CA * BC0 R * BO R)
  let B1 : ℝ → ℝ := fun R => sn * (CA * BC1 R * BO R)
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hsn : 0 ≤ sn := Real.sqrt_nonneg _
  have hsnsq : sn ^ 2 = 4 * (Module.finrank ℝ E : ℝ) := by
    simpa only [sn] using
      Real.sq_sqrt (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hAF
  refine ⟨B0, B1,
    fun R hR => mul_nonneg hsn
      (mul_nonneg (mul_nonneg hCA (hBC0 R hR)) (hBO R hR)),
    fun R hR => mul_nonneg hsn
      (mul_nonneg (mul_nonneg hCA (hBC1 R hR)) (hBO R hR)), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP
  let BA : ℝ := CA * (BC0 R + BC1 R * A) * BO R
  have hBCaff : 0 ≤ BC0 R + BC1 R * A :=
    add_nonneg (hBC0 R hR) (mul_nonneg (hBC1 R hR) hA)
  have hBA : 0 ≤ BA :=
    mul_nonneg (mul_nonneg hCA hBCaff) (hBO R hR)
  let Tr : SmoothCcTensor g₀ 3 1 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let OD : SmoothCcTensor g₀ 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ -
      deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr, lieCorrectionZeroTr, reindexedPureTrace,
      lieCorrectionZeroPureDT_eq_pureTrace_local] using
      htr g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP2
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ AF ^ 2 := by
    change SF ≤ AF ^ 2
    rw [show AF ^ 2 = SF by simp only [AF, Real.sq_sqrt hSF]]
  have hODform :
      OD = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 Tr Fix := by
    simpa only [OD, Tr, Fix] using
      deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g₀ g₁ g₀ gB
  have hOD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hODform]
    simpa only [BO] using
      hoprod Tr Fix (Bt R) AF (hBt R hR) hAF hTr hFix
  have hCAjet : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (BC0 R + BC1 R * A) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_connectionDifferenceRaisedEndomorphism_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ i,
          ← norm_iteratedCovGrad_connectionDifferenceLoweredCc_eq_connectionDifferenceSection
            (I := I) (M := M) g₀ g₁ i]
      _ ≤ (BC0 R + BC1 R * A) ^ 2 :=
        hc g₁ P htie hδ_le hδ_nonneg hbound R A hR hA hP2 hP
  let AD : SmoothCcTensor g₀ 0 2 :=
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ -
      deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB
  have hADform :
      AD = ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2
        (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD := by
    dsimp only [AD, OD]
    unfold deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference
    rw [← operatorFieldComposition_zero_eq_operatorFieldApply, ← operatorFieldComposition_zero_eq_operatorFieldApply,
      ← ccOperatorFieldComp_sub_right]
  have hAD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤ BA ^ 2 := by
    rw [hADform]
    simpa only [BA] using
      haprod (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁) OD
        (BC0 R + BC1 R * A) (BO R) hBCaff (hBO R hR) hCAjet hOD
  let SD : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ gB)
  have hraise_sub :
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ -
            deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) =
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀) -
          cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply tensorRSSpace_ext 1 1 x
    intro om
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply]
    simp only [cometricRaiseSlot0Field_toSection]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply]
    rfl
  have hSDform :
      SD = cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [SD, AD, endoDiffSection]
    rw [slotInsertEndoCc_sub, connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise,
      connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise, ← hraise_sub]
  have hSD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) ≤ BA ^ 2 := by
    rw [hSDform]
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ BA ^ 2 := hAD
  have hraw :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gB -
            lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [SD] using
          normSq_iteratedCovGrad_lieCorrectionZeroInsertionDiff_le
            (I := I) (M := M) g₀ g₁ gB i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) * BA ^ 2 :=
      mul_le_mul_of_nonneg_left hSD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B0 R + B1 R * A) ^ 2 := by
      rw [← hsnsq]
      simp only [B0, B1, BA]
      ring

private noncomputable def bgKappa
    (g₀ g₁ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB -
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀

private noncomputable def bgAmixHalf
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (bgKappa (I := I) (M := M) g₀ g₁ gB))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀)))))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotIter_sub
    (g₀ : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g₀ r s) :
    slotExtendIter (I := I) (M := M) g₀ r s w (A - B) =
      slotExtendIter (I := I) (M := M) g₀ r s w A -
        slotExtendIter (I := I) (M := M) g₀ r s w B := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g₀ (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g₀ r s w (A - B)) = _
      rw [ih, slotExtend_sub]
      rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem amixHalf_bg
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB σ -
        lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ σ =
      bgAmixHalf (I := I) (M := M) g₀ g₁ gB σ := by
  unfold lieCorrectionZeroMixedConnectionHalfExpansion bgAmixHalf bgKappa
  rw [lieCorrectionZeroKappa_eq_metricConnectionDifferenceLoweredCoefficient,
    lieCorrectionZeroKappa_eq_metricConnectionDifferenceLoweredCoefficient,
    ← operatorFieldComposition_sub_right, ← operatorFieldComposition_sub_right,
    ← operatorFieldComposition_sub_left, ← slotIter_sub]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem bgAmix_eq
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
        lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀ =
      (2 : ℝ) •
        (bgAmixHalf (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
          bgAmixHalf (I := I) (M := M) g₀ g₁ gB
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) := by
  rw [lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ gB,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g₀ g₁ g₀]
  have h0 := amixHalf_bg (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have h1 := amixHalf_bg (I := I) (M := M) g₀ g₁ gB
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  simp only [lieCorrectionZeroMixedConnectionExpansion]
  rw [show
      (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) -
        (2 : ℝ) •
          (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)) =
        (2 : ℝ) •
          ((lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀ lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) +
            (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ gB
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) -
              lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g₀ g₁ g₀
                (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))) by module,
    h0, h1]


private theorem amixHalf_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (bgAmixHalf (I := I) (M := M) g₀ g₁ gB σ)‖ ^ 2) ≤
          (B R * A) ^ 2 := by
  classical
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Bt3, hBt3, htr3⟩ := trace_h2 (I := I) (M := M) 3 hDim g₀ hδ₀
  obtain ⟨Bt4, hBt4, htr4⟩ := trace_h2 (I := I) (M := M) 4 hDim g₀ hδ₀
  obtain ⟨BK, hBK, hkd⟩ := kappaDiff_h2 (I := I) (M := M) hDim g₀ gB
  obtain ⟨Cq, hCq, hqprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 2 5 3
  obtain ⟨Cn, hCn, hnprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 2 3 6
  obtain ⟨Cm, hCm, hmprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 2 6 4
  obtain ⟨Co, hCo, hoprod⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let B : ℝ → ℝ := fun R =>
    Co * Bt2 R *
      (Cm * Bt4 R * (Cn * (sf 3 * BK R) * (Cq * Bt3 R * (sf 2 * 4))))
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w => Real.sqrt_nonneg _
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR))
      (mul_nonneg (mul_nonneg hCm (hBt4 R hR))
        (mul_nonneg (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR)))
          (mul_nonneg (mul_nonneg hCq (hBt3 R hR))
            (mul_nonneg (hsf 2) (by norm_num)))))
  refine ⟨B, hB, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound σ R A hR hA hP2 hP
  let Qb : ℝ := Cq * Bt3 R * (sf 2 * (4 * A))
  let Nb : ℝ := Cn * (sf 3 * BK R) * Qb
  let Mb : ℝ := Cm * Bt4 R * Nb
  let Ob : ℝ := Co * Bt2 R * Mb
  have hQb : 0 ≤ Qb :=
    mul_nonneg (mul_nonneg hCq (hBt3 R hR))
      (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA))
  have hNb : 0 ≤ Nb :=
    mul_nonneg (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR))) hQb
  have hMb : 0 ≤ Mb := mul_nonneg (mul_nonneg hCm (hBt4 R hR)) hNb
  let KD : SmoothCcTensor g₀ 0 3 :=
    bgKappa (I := I) (M := M) g₀ g₁ gB
  let K0 : SmoothCcTensor g₀ 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀
  let KDs : SmoothCcTensor g₀ 3 6 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 3 KD
  let K0s : SmoothCcTensor g₀ 2 5 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 2 K0
  let T2 : SmoothCcTensor g₀ 4 2 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 2 σ
  let T3 : SmoothCcTensor g₀ 5 3 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T4 : SmoothCcTensor g₀ 6 4 :=
    reindexedPureTrace (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let Qf : SmoothCcTensor g₀ 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3 T3 K0s
  let Nf : SmoothCcTensor g₀ 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6 KDs Qf
  let Mid : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 T4 Nf
  have hKD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i KD‖ ^ 2) ≤ (BK R) ^ 2 := by
    have hraw := hkd g₁ P htie R hR hP2
    have hneg : KD =
        -(lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ -
          lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB) := by
      simp only [KD, bgKappa]
      exact (neg_sub _ _).symm
    rw [hneg]
    simpa only [iteratedCovGrad_neg, norm_neg] using hraw
  have hK0 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K0‖ ^ 2) ≤ (4 * A) ^ 2 := by
    simpa only [K0] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie A hP
  have hKDs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 6 i KDs‖ ^ 2) ≤
        (sf 3 * BK R) ^ 2 := by
    simpa only [KDs, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 3 KD (BK R) hKD
  have hK0s : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 5 i K0s‖ ^ 2) ≤
        (sf 2 * (4 * A)) ^ 2 := by
    simpa only [K0s, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 2 K0 (4 * A) hK0
  have hT2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2, lieCorrectionZeroTr, reindexedPureTrace,
      lieCorrectionZeroPureDT_eq_pureTrace_local] using
      htr2 g₁ P htie hδ_le hδ_nonneg hbound
      σ R hR hP2
  have hT3 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 5 3 i T3‖ ^ 2) ≤ (Bt3 R) ^ 2 := by
    simpa only [T3, lieCorrectionZeroTr, reindexedPureTrace,
      lieCorrectionZeroPureDT_eq_pureTrace_local] using
      htr3 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour R hR hP2
  have hT4 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 6 4 i T4‖ ^ 2) ≤ (Bt4 R) ^ 2 := by
    simpa only [T4, lieCorrectionZeroTr, reindexedPureTrace,
      lieCorrectionZeroPureDT_eq_pureTrace_local] using
      htr4 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne R hR hP2
  have hQf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Qf‖ ^ 2) ≤ Qb ^ 2 := by
    simpa only [Qf, Qb] using hqprod T3 K0s (Bt3 R) (sf 2 * (4 * A))
      (hBt3 R hR) (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA))
      hT3 hK0s
  have hNf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 6 i Nf‖ ^ 2) ≤ Nb ^ 2 := by
    simpa only [Nf, Nb] using hnprod KDs Qf (sf 3 * BK R) Qb
      (mul_nonneg (hsf 3) (hBK R hR)) hQb hKDs hQf
  have hMid : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Mid‖ ^ 2) ≤ Mb ^ 2 := by
    simpa only [Mid, Mb] using hmprod T4 Nf (Bt4 R) Nb
      (hBt4 R hR) hNb hT4 hNf
  have hform : bgAmixHalf (I := I) (M := M) g₀ g₁ gB σ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Mid := rfl
  rw [hform]
  calc
    _ ≤ Ob ^ 2 := by
      simpa only [Ob] using hoprod T2 Mid (Bt2 R) Mb
        (hBt2 R hR) hMb hT2 hMid
    _ = (B R * A) ^ 2 := by
      simp only [Ob, Mb, Nb, Qb, B]
      ring


theorem exists_lieCorrectionZeroMixedConnection_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
              lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B, hB, hhalf⟩ :=
    amixHalf_tame (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨fun _ => 0, fun R => 4 * B R, fun R _ => le_rfl,
    fun R hR => mul_nonneg (by norm_num) (hB R hR), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP
  have h0 := hhalf g₁ P htie hδ_le hδ_nonneg hbound
    lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne R A hR hA hP2 hP
  have h1 := hhalf g₁ P htie hδ_le hδ_nonneg hbound
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) R A hR hA hP2 hP
  have hsum := h2Jet_sum2 (I := I) (M := M) g₀ 2 2 3
    (bgAmixHalf (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
    (bgAmixHalf (I := I) (M := M) g₀ g₁ gB
      (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
    (B R * A) (B R * A) h0 h1
  rw [bgAmix_eq (I := I) (M := M) g₀ g₁ gB, h2Jet_two]
  calc
    4 * (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (bgAmixHalf (I := I) (M := M) g₀ g₁ gB lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
            bgAmixHalf (I := I) (M := M) g₀ g₁ gB
              (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))‖ ^ 2) ≤
        4 * (2 * ((B R * A) ^ 2 + (B R * A) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (0 + 4 * B R * A) ^ 2 := by ring

private noncomputable def bgCorrFam
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
      g₀ gB T hδ hδZ s -
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
      g₀ g₀ T hδ hδZ s

omit [SigmaCompactSpace M] in
private theorem bgCorr_eq
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) :
    bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s =
      let g₁ := metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s
      ((deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g₀) +
        (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)) +
      ((lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀) +
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)) := by
  simp only [bgCorrFam, RicciDeTurckLowOrder.pathIntegrand]
  rw [← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField,
    ← deTurckLieConnectionDifferenceDerivCoeffField_add_deTurckLieCovariantDerivativeInsertionField,
    lieCorrectionZero_decomp, lieCorrectionZero_decomp]
  abel


private theorem bgCorrFam_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨Ba0, Ba1, hBa0, hBa1, hDla⟩ :=
    exists_deTurckLieConnectionDifferenceDerivativeCoefficient_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bb0, Bb1, hBb0, hBb1, hDlb⟩ :=
    exists_deTurckLieCovariantDerivativeInsertion_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bi0, Bi1, hBi0, hBi1, hIns⟩ :=
    exists_lieCorrectionZeroInsertion_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bm0, Bm1, hBm0, hBm1, hMix⟩ :=
    exists_lieCorrectionZeroMixedConnection_backgroundDifference_covariantJetNormSq_two_tame_bound (I := I) (M := M) hDim g₀ gB hδ₀
  let S0 : ℝ → ℝ := fun R => Ba0 R + Bb0 R + Bi0 R + Bm0 R
  let S1 : ℝ → ℝ := fun R => Ba1 R + Bb1 R + Bi1 R + Bm1 R
  let B0 : ℝ → ℝ := fun R => 4 * S0 R
  let B1 : ℝ → ℝ := fun R => 4 * S1 R
  have hS0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S0 R := by
    intro R hR
    exact add_nonneg (add_nonneg (add_nonneg (hBa0 R hR) (hBb0 R hR))
      (hBi0 R hR)) (hBm0 R hR)
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := by
    intro R hR
    exact add_nonneg (add_nonneg (add_nonneg (hBa1 R hR) (hBb1 R hR))
      (hBi1 R hR)) (hBm1 R hR)
  refine ⟨B0, B1,
    fun R hR => mul_nonneg (by norm_num) (hS0 R hR),
    fun R hR => mul_nonneg (by norm_num) (hS1 R hR), ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3 s hs
  let P : SmoothCcTensor g₀ 0 2 :=
    convexPerturbation (I := I) g₀ T 0 s
  let g₁ : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using metricPerturbationPath_inner_of_mem
      (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  have hPbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T 0 hδ hδZ hs.1 hs.2
    have hscalar : (1 - s) * δ + s * δ = δ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPs : P = s • T := by
    simp only [P, convexPerturbation, smul_zero, zero_add]
  have hPjet : ∀ n : ℕ, ∀ D : ℝ,
      (∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ D ^ 2 →
      (∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ D ^ 2 := by
    intro n D hD
    rw [hPs, h2Jet_smul]
    calc
      s ^ 2 * (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤
          1 * (∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hs2
          (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ ≤ D ^ 2 := by simpa only [one_mul] using hD
  have hP2 := hPjet 3 R hT2
  have hP3 := hPjet 4 A hT3
  let V : ℝ := S0 R + S1 R * A
  have hV : 0 ≤ V :=
    add_nonneg (hS0 R hR) (mul_nonneg (hS1 R hR) hA)
  have harm : ∀ b0 b1 : ℝ, 0 ≤ b0 → 0 ≤ b1 →
      b0 ≤ S0 R → b1 ≤ S1 R → (b0 + b1 * A) ^ 2 ≤ V ^ 2 := by
    intro b0 b1 hb0 hb1 h0 h1
    refine pow_le_pow_left₀
      (add_nonneg hb0 (mul_nonneg hb1 hA)) ?_ 2
    exact add_le_add h0 (mul_le_mul_of_nonneg_right h1 hA)
  have hDa : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
      V ^ 2 :=
    (hDla g₁ P htie hδ_le hδ_nonneg hPbound R A hR hA hP2 hP3).trans
      (harm _ _ (hBa0 R hR) (hBa1 R hR)
        (by simp only [S0]; linarith [hBb0 R hR, hBi0 R hR, hBm0 R hR])
        (by simp only [S1]; linarith [hBb1 R hR, hBi1 R hR, hBm1 R hR]))
  have hDb : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
      V ^ 2 :=
    (hDlb g₁ P htie hδ_le hδ_nonneg hPbound R A hR hA hP2 hP3).trans
      (harm _ _ (hBb0 R hR) (hBb1 R hR)
        (by simp only [S0]; linarith [hBa0 R hR, hBi0 R hR, hBm0 R hR])
        (by simp only [S1]; linarith [hBa1 R hR, hBi1 R hR, hBm1 R hR]))
  have hIn : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
      V ^ 2 :=
    (hIns g₁ P htie hδ_le hδ_nonneg hPbound R A hR hA hP2 hP3).trans
      (harm _ _ (hBi0 R hR) (hBi1 R hR)
        (by simp only [S0]; linarith [hBa0 R hR, hBb0 R hR, hBm0 R hR])
        (by simp only [S1]; linarith [hBa1 R hR, hBb1 R hR, hBm1 R hR]))
  have hMx : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
      V ^ 2 :=
    (hMix g₁ P htie hδ_le hδ_nonneg hPbound R A hR hA hP2 hP3).trans
      (harm _ _ (hBm0 R hR) (hBm1 R hR)
        (by simp only [S0]; linarith [hBa0 R hR, hBb0 R hR, hBi0 R hR])
        (by simp only [S1]; linarith [hBa1 R hR, hBb1 R hR, hBi1 R hR]))
  have hsum := h2Jet_sum4 (I := I) (M := M) g₀ 2 2 3
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ g₀)
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀)
    (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ gB -
      lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)
    (lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ gB -
      lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g₀)
    V V V V hDa hDb hIn hMx
  rw [bgCorr_eq]
  dsimp only
  calc
    _ ≤ 4 * (V ^ 2 + V ^ 2 + V ^ 2 + V ^ 2) := by
      simpa only [g₁] using hsum
    _ = (B0 R + B1 R * A) ^ 2 := by
      simp only [B0, B1, V]
      ring

theorem exists_lowOrderPathIntegrand_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                  g₀ gB T hδ hδZ s -
                RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
                  g₀ g₀ T hδ hδZ s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hcorr⟩ :=
    bgCorrFam_tame (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3 s hs
  simpa only [bgCorrFam] using
    hcorr T hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3 s hs


private theorem bgCorrFam_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s)‖ ^ 2) ≤
            (B A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, htame⟩ :=
    bgCorrFam_tame (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨fun A => B0 A + B1 A * A, ?_, ?_⟩
  · intro A hA
    exact add_nonneg (hB0 A hA) (mul_nonneg (hB1 A hA) hA)
  · intro T δ hδ_le hδ_nonneg hδ hδZ A hA hT s hs
    have hT2 : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega))
        (fun j _ _ => sq_nonneg _)).trans hT
    exact htame T hδ_le hδ_nonneg hδ hδZ A A hA hA hT2 hT s hs

private noncomputable def bgCorrInt
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    SmoothCcTensor g₀ 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 2 2
    (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (covariantJetJoint_sub (I := I) (M := M) g₀ _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ))

omit [SigmaCompactSpace M] in
private theorem selfLow_bg_sub
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g₀ gB T hδ_lt hδ hδZ -
        RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g₀ g₀ T hδ_lt hδ hδZ =
      bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hBjoint : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g₀ gB T hδ hδZ) (δ := δ) (δ' := δ) :=
    RicciDeTurckLowOrder.selfLow_joint
      (I := I) (M := M) g₀ gB T hδ hδZ
  have h0joint : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g₀ g₀ T hδ hδZ) (δ := δ) (δ' := δ) :=
    RicciDeTurckLowOrder.selfLow_joint
      (I := I) (M := M) g₀ g₀ T hδ hδZ
  have hDjoint : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g₀ 2
      (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
      (δ := δ) (δ' := δ) := by
    exact covariantJetJoint_sub (I := I) (M := M) g₀ _ _ hBjoint h0joint
  have hBjointRaw := hBjoint
  have h0jointRaw := h0joint
  have hDjointRaw := hDjoint
  rw [linearizedRicciCovariantJetJointSmoothness] at hBjointRaw h0jointRaw hDjointRaw
  have hBcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g₀ 2 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
  have h0cont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g₀ 2 2
      (RicciDeTurckLowOrder.pathIntegrand
        (I := I) (M := M) g₀ g₀ T hδ hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ)
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hBint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((RicciDeTurckLowOrder.pathIntegrand
          (I := I) (M := M) g₀ gB T hδ hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    ((hBcont x).mono hSI).intervalIntegrable
  have h0int : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((RicciDeTurckLowOrder.pathIntegrand
          (I := I) (M := M) g₀ g₀ T hδ hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    ((h0cont x).mono hSI).intervalIntegrable
  have hBmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g₀ 2 2
    (RicciDeTurckLowOrder.pathIntegrand
      (I := I) (M := M) g₀ gB T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI hBjointRaw x
  have h0model := pathIntegralCoeffField_toModel (I := I) (M := M) g₀ 2 2
    (RicciDeTurckLowOrder.pathIntegrand
      (I := I) (M := M) g₀ g₀ T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI h0jointRaw x
  have hDmodel := pathIntegralCoeffField_toModel (I := I) (M := M) g₀ 2 2
    (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI hDjointRaw x
  simp only [RicciDeTurckLowOrder.selfLowInt, bgCorrInt,
    SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [hBmodel, h0model, hDmodel]
  simp only [bgCorrFam, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hBint h0int]

private theorem lowC0_bg_eq
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    (lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ).zeroOrderCoefficient =
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).zeroOrderCoefficient +
        bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ +
        (metricPrincipalDefectCurvCoeff (I := I) g₀ g₀ -
          metricPrincipalDefectCurvCoeff (I := I) g₀ g₀) := by
  have hself := selfLow_bg_sub (I := I) (M := M)
    g₀ gB T hδ_lt hδ hδZ
  rw [RicciDeTurckLowOrder.zeroOrderCoefficient_eq, RicciDeTurckLowOrder.zeroOrderCoefficient_eq]
  rw [sub_eq_iff_eq_add] at hself
  rw [hself]
  abel

private theorem bgCorrInt_h2
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (B : ℝ)
    (hcoeff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s)‖ ^ 2) ≤
        B ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ)‖ ^ 2) ≤
      B ^ 2 := by
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g₀ 2 2 2
    (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (covariantJetJoint_sub (I := I) (M := M) g₀ _ _
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (RicciDeTurckLowOrder.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ))
    hcoeff
  simpa only [bgCorrInt] using hpath


theorem exists_lowOrderPathIntegral_backgroundDifference_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (bgCorrInt (I := I) (M := M) g₀ gB T
              (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨B, hB, hfam⟩ :=
    bgCorrFam_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨B, hB, ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ A hA hT
  apply bgCorrInt_h2 (I := I) (M := M) g₀ gB T
    (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ (B A)
  intro s hs
  exact hfam T hδ_le hδ_nonneg hδ hδZ A hA hT s hs

omit [NeZero (Module.finrank ℝ E)] in
private theorem fixedBackground_h2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (metricPrincipalDefectCurvCoeff (I := I) g₀ g₀ -
            metricPrincipalDefectCurvCoeff (I := I) g₀ g₀)‖ ^ 2) ≤ B ^ 2 := by
  let Q : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (metricPrincipalDefectCurvCoeff (I := I) g₀ g₀ -
        metricPrincipalDefectCurvCoeff (I := I) g₀ g₀)‖ ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨Real.sqrt Q, Real.sqrt_nonneg _, ?_⟩
  rw [Real.sq_sqrt hQ]


private theorem bgCorr_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (bgCorrInt (I := I) (M := M) g₀ gB T
              (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hfam⟩ :=
    bgCorrFam_tame (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3
  apply bgCorrInt_h2 (I := I) (M := M) g₀ gB T
    (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ (B0 R + B1 R * A)
  intro s hs
  exact hfam T hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3 s hs


theorem exists_lowerScaleZeroCoefficient_backgroundDifference_covariantJetNormSq_two_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g₀ 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g₀ 2
            ((lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).zeroOrderCoefficient -
              (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).zeroOrderCoefficient) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hcorr⟩ :=
    bgCorr_tame (I := I) (M := M) hDim g₀ gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨Bf, hBf, hfixed⟩ := fixedBackground_h2 (I := I) (M := M) g₀
  let B0 : ℝ → ℝ := fun R => 2 * (C0 R + Bf)
  let B1 : ℝ → ℝ := fun R => 2 * C1 R
  refine ⟨B0, B1,
    fun R hR => mul_nonneg (by norm_num) (add_nonneg (hC0 R hR) hBf),
    fun R hR => mul_nonneg (by norm_num) (hC1 R hR), ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ R A hR hA hT2 hT3
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let Cb : SmoothCcTensor g₀ 2 2 :=
    bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ
  let F : SmoothCcTensor g₀ 2 2 :=
    metricPrincipalDefectCurvCoeff (I := I) g₀ g₀ -
      metricPrincipalDefectCurvCoeff (I := I) g₀ g₀
  let V : ℝ := C0 R + C1 R * A
  have hV : 0 ≤ V :=
    add_nonneg (hC0 R hR) (mul_nonneg (hC1 R hR) hA)
  have hcorr' : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Cb‖ ^ 2) ≤ V ^ 2 :=
    hcorr T hδ_le hδ_nonneg hδ hδZ R A hR hA
      (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hT2)
      (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hT3)
  have hdiff : (lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
        hδ_lt hδ hδZ).zeroOrderCoefficient -
      (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).zeroOrderCoefficient =
        Cb + F := by
    rw [lowC0_bg_eq (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ]
    simp only [Cb, F]
    abel
  change covariantJetNormSq (I := I) (M := M) g₀ 2
      ((lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ).zeroOrderCoefficient -
        (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).zeroOrderCoefficient) ≤ _
  rw [hdiff]
  have hsum := h2Jet_sum2 (I := I) (M := M) g₀ 2 2 3 Cb F V Bf
    hcorr' hfixed
  have hkey : 2 * (V ^ 2 + Bf ^ 2) ≤ (2 * (V + Bf)) ^ 2 := by
    nlinarith [mul_nonneg hV hBf, sq_nonneg V, sq_nonneg Bf]
  calc
    covariantJetNormSq (I := I) (M := M) g₀ 2 (Cb + F) ≤
        2 * (V ^ 2 + Bf ^ 2) := by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using hsum
    _ ≤ (2 * (V + Bf)) ^ 2 := hkey
    _ = (B0 R + B1 R * A) ^ 2 := by
      simp only [B0, B1, V]
      ring

theorem exists_lowerScaleZeroCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g₀ 2
          (lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).zeroOrderCoefficient ≤
          (B A) ^ 2 := by
  obtain ⟨K, hK, hsame⟩ :=
    exists_lowerScaleAction_coefficient_bound (I := I) (M := M) hDim g₀
  obtain ⟨Bc, hBc, hcorr⟩ :=
    exists_lowOrderPathIntegral_backgroundDifference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g₀ gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨Bf, hBf, hfixed⟩ := fixedBackground_h2 (I := I) (M := M) g₀
  let S : ℝ → ℝ := fun A => Real.sqrt (K * (1 + A ^ 2) ^ 6)
  let Q : ℝ → ℝ := fun A => (S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2
  let B : ℝ → ℝ := fun A => 2 * Real.sqrt (Q A)
  have hSarg : ∀ A : ℝ, 0 ≤ K * (1 + A ^ 2) ^ 6 := by
    intro A
    exact mul_nonneg hK (pow_nonneg (by positivity) 6)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun A hA => mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro T hT δ hδ_le hδ_nonneg hδ hδZ A hA hTA
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let C0 : SmoothCcTensor g₀ 2 2 :=
    (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).zeroOrderCoefficient
  let C1 : SmoothCcTensor g₀ 3 2 :=
    (lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).firstOrderCoefficient
  let Cb : SmoothCcTensor g₀ 2 2 :=
    bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ
  let F : SmoothCcTensor g₀ 2 2 :=
    metricPrincipalDefectCurvCoeff (I := I) g₀ g₀ -
      metricPrincipalDefectCurvCoeff (I := I) g₀ g₀
  have hsameAll := hsame T hT hδ_le hδ_nonneg hδ hδZ
  dsimp only at hsameAll
  have hsame0 : covariantJetNormSq (I := I) (M := M) g₀ 2 C0 ≤
      K * (1 + covariantJetNormSq (I := I) (M := M) g₀ 3 T) ^ 6 := by
    exact (le_add_of_nonneg_right
      (lowJetSq_nonneg (I := I) (M := M) g₀ 2 C1)).trans
      (by simpa only [C0, C1] using hsameAll)
  have hbase : 1 + covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤
      1 + A ^ 2 := by
    linarith
  have hpow : (1 + covariantJetNormSq (I := I) (M := M) g₀ 3 T) ^ 6 ≤
      (1 + A ^ 2) ^ 6 :=
    pow_le_pow_left₀
      (by linarith [lowJetSq_nonneg (I := I) (M := M) g₀ 3 T])
      hbase 6
  have hsameS : covariantJetNormSq (I := I) (M := M) g₀ 2 C0 ≤
      (S A) ^ 2 := by
    calc
      _ ≤ K * (1 + covariantJetNormSq (I := I) (M := M) g₀ 3 T) ^ 6 := hsame0
      _ ≤ K * (1 + A ^ 2) ^ 6 := mul_le_mul_of_nonneg_left hpow hK
      _ = (S A) ^ 2 := by
        symm
        simp only [S, Real.sq_sqrt (hSarg A)]
  have hcorr' : covariantJetNormSq (I := I) (M := M) g₀ 2 Cb ≤
      (Bc A) ^ 2 := by
    simpa only [covariantJetNormSq, Cb] using
      hcorr T hδ_le hδ_nonneg hδ hδZ A hA
        (by simpa only [covariantJetNormSq] using hTA)
  have hfixed' : covariantJetNormSq (I := I) (M := M) g₀ 2 F ≤ Bf ^ 2 := by
    simpa only [covariantJetNormSq, F] using hfixed
  have hzero : covariantJetNormSq (I := I) (M := M) g₀ 2
      (0 : SmoothCcTensor g₀ 2 2) ≤ (0 : ℝ) ^ 2 := by
    have hz := h2Jet_smul (I := I) (M := M) g₀ 2 2 3
      (0 : ℝ) (0 : SmoothCcTensor g₀ 2 2)
    have hz' : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (0 : SmoothCcTensor g₀ 2 2)‖ ^ 2) = 0 := by
      simpa only [zero_smul, pow_two, zero_mul] using hz
    change (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j
        (0 : SmoothCcTensor g₀ 2 2)‖ ^ 2) ≤ (0 : ℝ) ^ 2
    rw [hz']
    norm_num
  have hsum := h2Jet_sum4 (I := I) (M := M) g₀ 2 2 3
    C0 Cb F (0 : SmoothCcTensor g₀ 2 2)
    (S A) (Bc A) Bf 0
    (by simpa only [covariantJetNormSq] using hsameS)
    (by simpa only [covariantJetNormSq] using hcorr')
    (by simpa only [covariantJetNormSq] using hfixed')
    (by simpa only [covariantJetNormSq] using hzero)
  have hsum' : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (C0 + Cb + F)‖ ^ 2) ≤
      4 * ((S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2) := by
    simpa only [add_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] using hsum
  rw [lowC0_bg_eq (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ]
  calc
    _ ≤ 4 * ((S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2) := by
      simpa only [covariantJetNormSq, Nat.reduceAdd, C0, Cb, F] using hsum'
    _ = (B A) ^ 2 := by
      rw [show (S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2 = Q A from rfl]
      symm
      simp only [B, mul_pow, Real.sq_sqrt (hQ A)]
      norm_num

theorem exists_lowerScaleOneCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g₀ 2
          (lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ).firstOrderCoefficient ≤
          (B A) ^ 2 := by
  obtain ⟨D, hD, hhs3⟩ := hs3_of_jet3 (I := I) (M := M) g₀
  obtain ⟨B0, B1, hB0, hB1, hpath⟩ :=
    ricciDeTurckRemainderFirstOrderPathIntegral_h2_tame_bound (I := I) (M := M) hDim g₀ gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun A =>
    B0 (D * A) + B1 (D * A) * (D * A)
  refine ⟨B, ?_, ?_⟩
  · intro A hA
    have hDA : 0 ≤ D * A := mul_nonneg hD hA
    exact add_nonneg (hB0 (D * A) hDA)
      (mul_nonneg (hB1 (D * A) hDA) hDA)
  · intro T hδ hδZ A hA hTA
    have hDA : 0 ≤ D * A := mul_nonneg hD hA
    have hT3 :
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ D * A :=
      hhs3 T A hA hTA
    have hT2 :
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ D * A :=
      (ccToHs_norm_mono (I := I) (M := M) g₀ 2 (by norm_num) T).trans hT3
    have hZ2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ D * A := by
      rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
          (0 : SmoothCcTensor g₀ 0 2) = 0 by
        have hz := ccTensorToHs_smul (I := I) (M := M) g₀ 2 (2 : ℝ)
          (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
        simpa only [zero_smul] using hz]
      simpa only [norm_zero] using hDA
    have hZ3 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ D * A := by
      rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ)
          (0 : SmoothCcTensor g₀ 0 2) = 0 by
        have hz := ccTensorToHs_smul (I := I) (M := M) g₀ 2 (3 : ℝ)
          (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
        simpa only [zero_smul] using hz]
      simpa only [norm_zero] using hDA
    have hraw := hpath T (0 : SmoothCcTensor g₀ 0 2)
      hδ hδZ (D * A) (D * A) hDA hDA hT2 hZ2 hT3 hZ3
    rw [RicciDeTurckLowOrder.firstOrderCoefficient_eq (I := I) (M := M)
      g₀ gB T (by norm_num) hδ hδZ]
    simpa only [covariantJetNormSq, Nat.reduceAdd, B] using hraw

theorem exists_lowerScaleCoefficients_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        let L : LowerScaleActionCoefficients g₀ :=
          lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ
        covariantJetNormSq (I := I) (M := M) g₀ 2 L.zeroOrderCoefficient +
            covariantJetNormSq (I := I) (M := M) g₀ 2 L.firstOrderCoefficient ≤
          (B A) ^ 2 := by
  obtain ⟨B0, hB0, hC0⟩ := exists_lowerScaleZeroCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g₀ gB
  obtain ⟨B1, hB1, hC1⟩ := exists_lowerScaleOneCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g₀ gB
  let Q : ℝ → ℝ := fun A => (B0 A) ^ 2 + (B1 A) ^ 2
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := fun A => add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨B, fun A hA => Real.sqrt_nonneg _, ?_⟩
  intro T hT hδ hδZ A hA hTA
  let L : LowerScaleActionCoefficients g₀ :=
    lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T (by norm_num) hδ hδZ
  have h0 : covariantJetNormSq (I := I) (M := M) g₀ 2 L.zeroOrderCoefficient ≤ (B0 A) ^ 2 := by
    simpa only [L] using
      hC0 T hT (δ := (1 : ℝ) / 3) le_rfl (by norm_num)
        hδ hδZ A hA hTA
  have h1 : covariantJetNormSq (I := I) (M := M) g₀ 2 L.firstOrderCoefficient ≤ (B1 A) ^ 2 := by
    simpa only [L] using hC1 T hδ hδZ A hA hTA
  dsimp only
  calc
    covariantJetNormSq (I := I) (M := M) g₀ 2 L.zeroOrderCoefficient +
        covariantJetNormSq (I := I) (M := M) g₀ 2 L.firstOrderCoefficient ≤
      (B0 A) ^ 2 + (B1 A) ^ 2 := add_le_add h0 h1
    _ = (B A) ^ 2 := by
      symm
      simpa only [B, Q] using Real.sq_sqrt (hQ A)

theorem exists_lowerScaleFirstOrderAction_background_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, ∃ C3 C2 : ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧ 0 ≤ C3 ∧ 0 ≤ C2 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        let L : LowerScaleActionCoefficients g₀ :=
          lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ
        (∀ (W : SmoothCcTensor g₀ 0 2) (D : ℝ), 0 ≤ D →
          covariantJetNormSq (I := I) (M := M) g₀ 3 W ≤ D ^ 2 →
          covariantJetNormSq (I := I) (M := M) g₀ 2
              (L.firstOrderAction (I := I) (M := M) W) ≤
            (C3 * B A * D) ^ 2) ∧
        ∀ (W : SmoothCcTensor g₀ 0 2) (D : ℝ), 0 ≤ D →
          covariantJetNormSq (I := I) (M := M) g₀ 2 W ≤ D ^ 2 →
          covariantJetNormSq (I := I) (M := M) g₀ 1
              (L.firstOrderAction (I := I) (M := M) W) ≤
            (C2 * B A * D) ^ 2 := by
  obtain ⟨B, hB, hcoeff⟩ :=
    exists_lowerScaleCoefficients_covariantJetNormSq_two_bound (I := I) (M := M) hDim g₀ gB
  obtain ⟨C3, hC3, hhigh⟩ := exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g₀
  obtain ⟨C2, hC2, hlow⟩ := exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g₀
  refine ⟨B, C3, C2, hB, hC3, hC2, ?_⟩
  intro T hT hδ hδZ A hA hTA
  let L : LowerScaleActionCoefficients g₀ :=
    lowerScaleActionCoefficients (I := I) (M := M) g₀ gB T (by norm_num) hδ hδZ
  have hL : covariantJetNormSq (I := I) (M := M) g₀ 2 L.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g₀ 2 L.firstOrderCoefficient ≤ (B A) ^ 2 := by
    simpa only [L] using hcoeff T hT hδ hδZ A hA hTA
  have hBA : 0 ≤ B A := hB A hA
  dsimp only
  constructor
  · intro W D hD hW
    exact hhigh L W (B A) D hBA hD hL hW
  · intro W D hD hW
    exact hlow L W (B A) D hBA hD hL hW

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
