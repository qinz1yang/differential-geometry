import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower

/-!
# Low-regularity insertion-difference coefficient

This file bounds the cancellation-preserving background difference of the
two-slot `lieCorr0` insertion coefficient.  The exact refolds in
`LieCorr0LowJet` remove the self-background top derivative before any norm
estimate is taken.  Consequently the complete `H1` bound depends only on the
metric `H2` radius.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem jet_add
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * (a ^ 2 + b ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_add]
    have htri := norm_add_le (iteratedCovGrad (I := I) g r s j A)
      (iteratedCovGrad (I := I) g r s j B)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsquare,
      sq_nonneg (‖iteratedCovGrad (I := I) g r s j A‖ -
        ‖iteratedCovGrad (I := I) g r s j B‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2)) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ 2 * (a ^ 2 + b ^ 2) := by gcongr

private theorem jet_sub
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2) ≤
      2 * (a ^ 2 + b ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_sub]
    have htri := norm_sub_le (iteratedCovGrad (I := I) g r s j A)
      (iteratedCovGrad (I := I) g r s j B)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsquare,
      sq_nonneg (‖iteratedCovGrad (I := I) g r s j A‖ -
        ‖iteratedCovGrad (I := I) g r s j B‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2)) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ 2 * (a ^ 2 + b ^ 2) := by gcongr

private theorem app_h2h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hnorm := happ Φ W A B hA hB hΦ hW
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (appCcRS (I := I) (M := M) g p r c Φ W)] at hsquare
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare

private theorem grid_h1_low
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hK : ∀ k, 0 ≤ K k)
    (hgrid : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 2),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 2), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi2 : i < 2 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 2),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi2)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- The moving-to-frozen connection-difference section has an `H1` bound
from only the metric `H2` jet. -/
theorem connSec_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K, hK, hgrid⟩ := h2_grid_int (I := I) (M := M) hDim g₀
  let Q : ℝ → ℝ := fun R => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 2), K R k
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK R hR k)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  have hgr : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g₀ P k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g₀ P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K R k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P R hR hP k hk
  have hle := grid_h1_low (I := I) (M := M) g₀ P (K R) C
    (hK R hR) hgr hC (connDiffSection (I := I) g₁ g₀) (by
      intro i hi x
      simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
        hpt g₁ P htie hδ_le hδ_nonneg hbound i x)
  change _ ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by
    simp only [B, Real.sq_sqrt (hQ R hR)]]
  exact hle

/-- The lowered-connection background difference is `H2`-controlled by only
the metric `H2` radius. -/
theorem kappaDiff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
              lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B R) ^ 2 := by
  classical
  obtain ⟨BP, hBP, hp⟩ := pbLow_h2 (I := I) (M := M) hDim g₀ gB
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let AF : ℝ := Real.sqrt SF
  let Q : ℝ → ℝ := fun R => 2 * (SF + (BP R) ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg (by norm_num) (add_nonneg hSF (sq_nonneg _))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie R hR hP
  have hfix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2) ≤ AF ^ 2 := by
    change SF ≤ AF ^ 2
    rw [show AF ^ 2 = SF by simp only [AF, Real.sq_sqrt hSF]]
  have hp' := hp P R hR hP
  rw [kappa_diff (I := I) (M := M) g₀ g₁ gB P htie]
  have hle := jet_sub (I := I) (M := M) g₀ 0 3 3
    (connDiffLoweredCc (I := I) g₀ gB)
    (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) AF (BP R) hfix hp'
  change _ ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by
    simp only [B, Real.sq_sqrt (hQ R)]]
  simpa only [Q, AF, Real.sq_sqrt hSF] using hle

private theorem normSq_scaled
    (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ : ℕ)
    (X : SmoothCcTensor g r₁ s₁) (Y : SmoothCcTensor g r₂ s₂)
    (c : ℝ) (hc : 0 ≤ c)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x (X.toSection x) ≤
        c * riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x
          (Y.toSection x)) :
    ‖X‖ ^ 2 ≤ c * ‖Y‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ hpt
  · exact integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r₁ s₁ X
  · exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r₂ s₂ Y).const_mul c

private theorem slotIns_h1
    (g₀ : SmoothRiemannianMetric I M)
    (N : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 N)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0 N)‖ ^ 2 := by
  have hfr : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0 N)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      refine normSq_scaled (I := I) (M := M) g₀ 2 (2 + i) 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1 N))
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0 N))
        (Module.finrank ℝ E : ℝ) hfr ?_
      intro x
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g₀ 1 N i x
      simpa only [pow_one] using h
    _ = _ := by rw [Finset.mul_sum]

/-- The complete insertion background difference has a uniform intrinsic
`H1` bound depending only on the perturbation `H2` radius. -/
theorem insert_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0Insert (I := I) (M := M) g₀ g₁ gB -
              lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B R) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htr⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨BK, hBK, hk⟩ := kappaDiff_h2 (I := I) (M := M) hDim g₀ gB
  obtain ⟨Cvv, hCvv, hvprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨Civ, hCiv, hiprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 3 1
  obtain ⟨BC, hBC, hc⟩ := connSec_h1 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Ccdv, hCcdv, hcdvprod⟩ :=
    app_h2h1 (I := I) (M := M) hDim g₀ 1 2 1
  let sf : ℕ → ℝ := fun w => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let BV : ℝ → ℝ := fun R => Cvv * Bt R * BK R
  let BI : ℝ → ℝ := fun R => Civ * Bt R * (sf 2 * BV R)
  let BD : ℝ → ℝ := fun R => Ccdv * BI R * BC R
  let B : ℝ → ℝ := fun R => 2 * sf 1 * BD R
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w => Real.sqrt_nonneg _
  have hBV : ∀ R : ℝ, 0 ≤ R → 0 ≤ BV R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCvv (hBt R hR)) (hBK R hR)
  have hBI : ∀ R : ℝ, 0 ≤ R → 0 ≤ BI R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCiv (hBt R hR))
      (mul_nonneg (hsf 2) (hBV R hR))
  have hBD : ∀ R : ℝ, 0 ≤ R → 0 ≤ BD R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCcdv (hBI R hR)) (hBC R hR)
  refine ⟨B, fun R hR => mul_nonneg (mul_nonneg (by norm_num) (hsf 1))
    (hBD R hR), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  let T : SmoothCcTensor g₀ 3 1 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let Ti : SmoothCcTensor g₀ 3 1 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm
  let KD : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
      lc0Kappa (I := I) (M := M) g₀ g₁ gB
  let VD : SmoothCcTensor g₀ 0 1 :=
    lc0VFlat (I := I) (M := M) g₀ g₁ g₀ -
      lc0VFlat (I := I) (M := M) g₀ g₁ gB
  let VDs : SmoothCcTensor g₀ 2 3 :=
    slotExtendIter (I := I) (M := M) g₀ 0 1 2 VD
  let ID : SmoothCcTensor g₀ 2 1 :=
    lc0IV (I := I) (M := M) g₀ g₁ g₀ -
      lc0IV (I := I) (M := M) g₀ g₁ gB
  let CD : SmoothCcTensor g₀ 1 1 :=
    lc0CdV (I := I) (M := M) g₀ g₁ g₀ -
      lc0CdV (I := I) (M := M) g₀ g₁ gB
  let ND := lc0NSec (I := I) (M := M) g₀ g₁ gB -
    lc0NSec (I := I) (M := M) g₀ g₁ g₀
  let S : SmoothCcTensor g₀ 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 1 ND
  let SS : SmoothCcTensor g₀ 2 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) S)
      (Equiv.swap (0 : Fin 2) 1)
  have hT : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [T] using htr g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP
  have hTi : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Ti‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Ti] using htr g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0IVPerm R hR hP
  have hKD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i KD‖ ^ 2) ≤ (BK R) ^ 2 := by
    simpa only [KD] using hk g₁ P htie R hR hP
  have hVD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i VD‖ ^ 2) ≤ (BV R) ^ 2 := by
    rw [vflat_diff (I := I) (M := M) g₀ g₁ gB]
    simpa only [T, KD, BV] using
      hvprod T KD (Bt R) (BK R) (hBt R hR) (hBK R hR) hT hKD
  have hVDs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i VDs‖ ^ 2) ≤
        (sf 2 * BV R) ^ 2 := by
    simpa only [VDs] using slotIter_h2b (I := I) (M := M)
      g₀ 0 1 2 VD (BV R) hVD
  have hID : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 1 i ID‖ ^ 2) ≤ (BI R) ^ 2 := by
    rw [iv_diff (I := I) (M := M) g₀ g₁ gB]
    simpa only [Ti, VDs, BI] using
      hiprod Ti VDs (Bt R) (sf 2 * BV R) (hBt R hR)
        (mul_nonneg (hsf 2) (hBV R hR)) hTi hVDs
  have hCsec : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (connDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤ (BC R) ^ 2 :=
    hc g₁ P htie hδ_le hδ_nonneg hbound R hR hP
  have hCD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i CD‖ ^ 2) ≤ (BD R) ^ 2 := by
    rw [cdv_diff (I := I) (M := M) g₀ g₁ gB]
    simpa only [ID, BD] using
      hcdvprod ID (connDiffSection (I := I) g₁ g₀) (BI R) (BC R)
        (hBI R hR) (hBC R hR) hID hCsec
  have hN0 : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0 ND)‖ ^ 2) ≤
        (BD R) ^ 2 := by
    rw [nins_diff (I := I) (M := M) g₀ g₁ gB]
    simpa only [CD] using hCD
  have hSraw : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i S‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) * (BD R) ^ 2 := by
    calc
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0 ND)‖ ^ 2 := by
        simpa only [S] using slotIns_h1 (I := I) (M := M) g₀ ND
      _ ≤ (Module.finrank ℝ E : ℝ) * (BD R) ^ 2 :=
        mul_le_mul_of_nonneg_left hN0 (Nat.cast_nonneg _)
  have hS : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i S‖ ^ 2) ≤
        (sf 1 * BD R) ^ 2 := by
    refine hSraw.trans_eq ?_
    dsimp only [sf]
    rw [mul_pow, Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg _) 1)]
    simp only [pow_one]
  have hSS_eq : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i SS‖ ^ 2) =
      ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i S‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => by
        simpa only [SS] using
          rfns_iteratedCovGrad_rsDomDomCongr_both_eq
            (I := I) (M := M) g₀ 2 2
            (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) S i x)
  have hSS : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i SS‖ ^ 2) ≤
        (sf 1 * BD R) ^ 2 := by
    rw [hSS_eq]
    exact hS
  rw [insert_diff (I := I) (M := M) g₀ g₁ gB]
  change (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (S + SS)‖ ^ 2) ≤ _
  have hout := jet_add (I := I) (M := M) g₀ 2 2 2 S SS
    (sf 1 * BD R) (sf 1 * BD R) hS hSS
  change _ ≤ (B R) ^ 2
  exact hout.trans_eq (by
    dsimp only [B]
    ring)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
