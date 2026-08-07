import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegInsertH1
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Affine low-regularity bounds for the order-zero Ricci--DeTurck coefficient

This file separates the lower `H2` metric radius from the single top `H3`
derivative in the order-zero coefficient estimates.  The cancellation inside
`DLb + lieCorr0` is retained before any norm estimate is taken.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- In dimension three, an `H1` coefficient grid with the order-`i` window
`i + 3` has an affine bound in the unique total-order-three metric grid. -/
theorem h1_grid_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
        (∀ (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 3),
              lowJetGrid (I := I) (M := M) g P k x) →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨K0, hK0, hgrid0⟩ := h2_grid_int (I := I) (M := M) hDim g
  obtain ⟨K3, hK3, hgrid3⟩ := h3_top_grid_int (I := I) (M := M) hDim g
  let L : ℝ → ℕ → ℝ := fun R i ↦
    ∑ k ∈ Finset.range (i + 3), if k = 3 then 0 else K0 R k
  let T : ℝ → ℕ → ℝ := fun R i ↦
    ∑ k ∈ Finset.range (i + 3), if k = 3 then K3 R else 0
  let Q0 : ℝ → ℝ := fun R ↦
    ∑ i ∈ Finset.range 2, C i * L R i
  let Q1 : ℝ → ℝ := fun R ↦
    ∑ i ∈ Finset.range 2, C i * T R i
  let B0 : ℝ → ℝ := fun R ↦ Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R ↦ Real.sqrt (Q1 R)
  have hL : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ L R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : k = 3
      · simp [hk]
      · simp only [if_neg hk]
        exact hK0 R hR k
  have hT : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ T R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : k = 3
      · simp only [hk, if_pos]
        exact hK3 R hR
      · simp [hk]
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i) (hL R hR i)
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i) (hT R hR i)
  refine ⟨B0, B1, fun R _ ↦ Real.sqrt_nonneg _,
    fun R _ ↦ Real.sqrt_nonneg _, ?_⟩
  intro P Φ R A hR hA hP2 htop hΦ
  let Km : ℕ → ℝ := fun k ↦ if k = 3 then K3 R * A ^ 2 else K0 R k
  have hKm : ∀ k, 0 ≤ Km k := by
    intro k
    by_cases hk : k = 3
    · simp only [Km, hk, if_pos]
      exact mul_nonneg (hK3 R hR) (sq_nonneg A)
    · simp only [Km, if_neg hk]
      exact hK0 R hR k
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ Km k := by
    intro k hk
    by_cases hk3 : k = 3
    · subst k
      simpa only [lowJetGrid, Km, if_pos, Nat.reduceAdd] using
        hgrid3 P R A hR hA hP2 htop
    · have hk2 : k ≤ 2 := by omega
      simpa only [lowJetGrid, Km, if_neg hk3] using
        hgrid0 P R hR hP2 k hk2
  have hle := grid_h1_le (I := I) (M := M) g P Km C
    hKm hgr hC Φ hΦ
  have hsplit : ∀ i : ℕ,
      (∑ k ∈ Finset.range (i + 3), Km k) = L R i + T R i * A ^ 2 := by
    intro i
    simp only [L, T]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = 3
    · simp only [Km, hk, if_pos]
      ring
    · simp only [Km, if_neg hk]
      ring
  have hQeq :
      (∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 3), Km k) =
        Q0 R + Q1 R * A ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 2,
          (C i * L R i + (C i * T R i) * A ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hsplit i]
            ring
      _ = (∑ i ∈ Finset.range 2, C i * L R i) +
          ∑ i ∈ Finset.range 2, (C i * T R i) * A ^ 2 := by
            rw [Finset.sum_add_distrib]
      _ = Q0 R + Q1 R * A ^ 2 := by
            simp only [Q0, Q1, Finset.sum_mul]
  rw [hQeq] at hle
  calc
    _ ≤ Q0 R + Q1 R * A ^ 2 := hle
    _ = (B0 R) ^ 2 + (B1 R * A) ^ 2 := by
      simp only [B0, B1, mul_pow, Real.sq_sqrt (hQ0 R hR),
        Real.sq_sqrt (hQ1 R hR)]
    _ ≤ (B0 R + B1 R * A) ^ 2 := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Q0 R))
        (mul_nonneg (Real.sqrt_nonneg (Q1 R)) hA)]

/-- The endpoint spectral `H2` radius controls the lower three-term metric jet
at every point of a convex realization segment. -/
theorem convex_h2_jet (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2) (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
            (C * R) ^ 2 := by
  classical
  obtain ⟨C, hC, hjet⟩ := hsJet_le (I := I) (M := M) g₀ 2 2
  refine ⟨C, hC, ?_⟩
  intro T T' R hR hT hT' s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hpath :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    rw [show convexPerturbation (I := I) g₀ T T' s =
        (1 - s) • T' + s • T from rfl,
      ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
    calc
      ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T' +
          s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
          ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
            ‖s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ :=
            norm_add_le _ _
      _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
            s * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
        add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
          (mul_le_mul_of_nonneg_left hT hs0)
      _ = R := by ring
  have hsum : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T T' s)‖) ≤ C * R := by
    exact (hjet (convexPerturbation (I := I) g₀ T T' s)).trans
      (mul_le_mul_of_nonneg_left hpath hC)
  exact (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun j _ ↦ norm_nonneg
      (iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T T' s)))).trans
    (pow_le_pow_left₀
      (Finset.sum_nonneg fun j _ ↦ norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)))
      hsum 2)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_add
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (X Y : SmoothCcTensor g r s) (a b : ℝ)
    (hX : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2) ≤ a ^ 2)
    (hY : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2) ≤ b ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (X + Y)‖ ^ 2) ≤
      2 * (a ^ 2 + b ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j (X + Y)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j X‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_add]
    have htri := norm_add_le (iteratedCovGrad (I := I) g r s j X)
      (iteratedCovGrad (I := I) g r s j Y)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsquare,
      sq_nonneg (‖iteratedCovGrad (I := I) g r s j X‖ -
        ‖iteratedCovGrad (I := I) g r s j Y‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j X‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2) :=
      Finset.sum_le_sum fun j _ ↦ hper j
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (a ^ 2 + b ^ 2) := by gcongr

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (X : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((2 : ℝ) • X)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_neg_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (X : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((-2 : ℝ) • X)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs]
  ring

private theorem app_h1h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p c j
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := appRS_h1_h2_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hnorm := happ Φ W A B hA hB hΦ hW
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsquare
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare

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
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := appRS_h2_h1_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hnorm := happ Φ W A B hA hB hΦ hW
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsquare
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare

/-- Affine `H1` bound for the order-zero Ricci connection-difference
coefficient. -/
theorem ricci0_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciConnDiffOrder0CoeffField
              (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0Coeff_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨B0, B1, hB0, hB1, hgrid⟩ :=
    h1_grid_tame (I := I) (M := M) (r := 2) (s := 2) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  exact hgrid P
    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
    R A hR hA hP2 htop
    (fun i hi x ↦ hpt g₁ P htie hδ_le hδ_nonneg hbound i x)

/-- Affine `H1` bound for the order-zero `DLa` coefficient. -/
theorem dla_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ :=
    rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨B0, B1, hB0, hB1, hgrid⟩ :=
    h1_grid_tame (I := I) (M := M) (r := 2) (s := 2) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  exact hgrid P
    (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)
    R A hR hA hP2 htop
    (fun i hi x ↦ hpt g₁ P htie hδ_le hδ_nonneg hbound i x)

/-- Affine `H1` bound for the change of fixed DeTurck background in `DLb`. -/
theorem dlbDiff_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
              deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    bdEndoArmDiff_pointwise_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨B0, B1, hB0, hB1, hgrid⟩ :=
    h1_grid_tame (I := I) (M := M) (r := 2) (s := 2) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  have hpt' : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
              deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          lowJetGrid (I := I) (M := M) g₀ P k x := by
    intro i hi x
    let b : ℕ → ℝ := fun l' ↦
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
        ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)
    have hb : ∀ l', 0 ≤ b l' := fun l' ↦
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
    have hwin := Combinatorics.antidiagonalTupleGridWindow_mono b hb
      (show i + 2 ≤ i + 3 by omega)
    have hwin' :
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) ≤
          ∑ k ∈ Finset.range (i + 3),
            lowJetGrid (I := I) (M := M) g₀ P k x := by
      simpa only [b, Combinatorics.antidiagonalTupleGridWindow,
        Combinatorics.antidiagonalTupleGrid, lowJetGrid] using hwin
    exact (hpt g₁ P htie hδ_le hδ_nonneg hbound i x).trans
      (mul_le_mul_of_nonneg_left hwin' (hC i))
  exact hgrid P
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
    R A hR hA hP2 htop hpt'

-- The rank-changing operator composition needs an enlarged local elaboration budget.
/-- The fixed-curvature part of `lieCorr0` is in fact a lower-order `H1`
coefficient; its affine top-order coefficient can be chosen to be zero. -/
theorem riem_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0Riem (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Cp, hCp, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 4 2
  let Fr : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 2 4 j
      (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2
  let Br : ℝ := Real.sqrt Fr
  let B0 : ℝ → ℝ := fun R ↦ Cp * Bt R * Br
  let B1 : ℝ → ℝ := fun _ ↦ 0
  have hFr : 0 ≤ Fr := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hBr : 0 ≤ Br := Real.sqrt_nonneg _
  have hRf : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 4 j
        (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2) ≤ Br ^ 2 := by
    rw [show Br ^ 2 = Fr by simp only [Br, Real.sq_sqrt hFr]]
  refine ⟨B0, B1, fun R hR ↦
    mul_nonneg (mul_nonneg hCp (hBt R hR)) hBr,
    fun R hR ↦ le_rfl, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)‖ ^ 2) ≤
      (Bt R) ^ 2 :=
    htrace g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0RiemPerm2 R hR hP2
  have hApp := happ
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
    (lc0RiemRestField (I := I) (M := M) g₀)
    (Bt R) Br (hBt R hR) hBr hTr hRf
  have hAppJet : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
          (lc0RiemRestField (I := I) (M := M) g₀))‖ ^ 2) ≤
      (B0 R) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
              (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
              (lc0RiemRestField (I := I) (M := M) g₀))‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega))
          (fun i _ _ ↦ sq_nonneg _)
      _ ≤ (Cp * Bt R * Br) ^ 2 := hApp
      _ = (B0 R) ^ 2 := by rfl
  rw [lc0Riem_eq_lc0RiemField (I := I) (M := M) g₀ g₁]
  simpa only [lc0RiemField, B1, zero_mul, add_zero,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real,
    norm_smul, Real.norm_eq_abs,
    abs_neg, abs_one, one_mul] using hAppJet

/-- Affine `H1` bound for the genuine vector--bilinear correction.  Its only
top-order factor is the self-background Koszul tensor. -/
theorem vb_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0VB (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bt1, hBt1, htr1⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Cv, hCv, hvprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨Ci, hCi, hiprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 2 3 1
  obtain ⟨Cn, hCn, hnprod⟩ := app_h1h2
    (I := I) (M := M) hDim g₀ 2 1 4
  obtain ⟨Co, hCo, hoprod⟩ := app_h2h1
    (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w ↦ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Vb : ℝ → ℝ → ℝ := fun R J ↦ Cv * Bt1 R * (4 * J)
  let Ib : ℝ → ℝ → ℝ := fun R J ↦ Ci * Bt1 R * (sf 2 * Vb R J)
  let Nb : ℝ → ℝ → ℝ := fun R J ↦ Cn * (sf 1 * (4 * R)) * Ib R J
  let Ob : ℝ → ℝ → ℝ := fun R J ↦ Co * Bt2 R * Nb R J
  let B0 : ℝ → ℝ := fun R ↦ 2 * Ob R R
  let B1 : ℝ → ℝ := fun R ↦ 2 * Ob R 1
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w ↦ Real.sqrt_nonneg _
  have hVb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Vb R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCv (hBt1 R hR))
      (mul_nonneg (by norm_num) hJ)
  have hIb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Ib R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCi (hBt1 R hR))
      (mul_nonneg (hsf 2) (hVb R hR J hJ))
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Nb R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCn
      (mul_nonneg (hsf 1) (mul_nonneg (by norm_num) hR)))
      (hIb R hR J hJ)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Ob R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR)) (hNb R hR J hJ)
  refine ⟨B0, B1, fun R hR ↦
      mul_nonneg (by norm_num) (hOb R hR R hR),
    fun R hR ↦ mul_nonneg (by norm_num) (hOb R hR 1 zero_le_one), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  have hRA : 0 ≤ R + A := add_nonneg hR hA
  have htop2 : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htop 2
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (R + A) ^ 2 := by
    calc
      _ = (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ]
      _ ≤ R ^ 2 + A ^ 2 := add_le_add hP2 htop2
      _ ≤ (R + A) ^ 2 := by nlinarith [mul_nonneg hR hA]
  let T1 : SmoothCcTensor g₀ 3 1 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let T1i : SmoothCcTensor g₀ 3 1 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 1 lc0IVPerm
  let T2 : SmoothCcTensor g₀ 4 2 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm
  let K : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let Vf : SmoothCcTensor g₀ 0 1 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 T1 K
  let Vs : SmoothCcTensor g₀ 2 3 :=
    slotExtendIter (I := I) (M := M) g₀ 0 1 2 Vf
  let Iv : SmoothCcTensor g₀ 2 1 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1 T1i Vs
  let Ks : SmoothCcTensor g₀ 1 4 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 1 K
  let Inn : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 Ks Iv
  let Out : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2 Inn
  have hT1 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T1‖ ^ 2) ≤ (Bt1 R) ^ 2 := by
    simpa only [T1] using htr1 g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP2
  have hT1i : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T1i‖ ^ 2) ≤ (Bt1 R) ^ 2 := by
    simpa only [T1i] using htr1 g₁ P htie hδ_le hδ_nonneg hbound
      lc0IVPerm R hR hP2
  have hT2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0VBPerm R hR hP2
  have hK2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K‖ ^ 2) ≤ (4 * (R + A)) ^ 2 := by
    simpa only [K] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie (R + A) hRA hP3
  have hK1 : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K‖ ^ 2) ≤ (4 * R) ^ 2 := by
    simpa only [K] using kappaSelf_h1
      (I := I) (M := M) g₀ g₁ P htie R hR hP2
  have hVf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i Vf‖ ^ 2) ≤ (Vb R (R + A)) ^ 2 := by
    simpa only [Vf, Vb] using hvprod T1 K (Bt1 R) (4 * (R + A))
      (hBt1 R hR) (mul_nonneg (by norm_num) hRA) hT1 hK2
  have hVs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Vs‖ ^ 2) ≤
        (sf 2 * Vb R (R + A)) ^ 2 := by
    simpa only [Vs, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 1 2 Vf (Vb R (R + A)) hVf
  have hIv : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 1 i Iv‖ ^ 2) ≤
        (Ib R (R + A)) ^ 2 := by
    simpa only [Iv, Ib] using hiprod T1i Vs (Bt1 R) (sf 2 * Vb R (R + A))
      (hBt1 R hR) (mul_nonneg (hsf 2) (hVb R hR (R + A) hRA)) hT1i hVs
  have hKs : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 4 i Ks‖ ^ 2) ≤
        (sf 1 * (4 * R)) ^ 2 := by
    simpa only [Ks, sf] using slotIter_h1b
      (I := I) (M := M) g₀ 0 3 1 K (4 * R) hK1
  have hInn : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Inn‖ ^ 2) ≤
        (Nb R (R + A)) ^ 2 := by
    simpa only [Inn, Nb] using hnprod Ks Iv (sf 1 * (4 * R)) (Ib R (R + A))
      (mul_nonneg (hsf 1) (mul_nonneg (by norm_num) hR))
      (hIb R hR (R + A) hRA) hKs hIv
  have hOut : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤
        (Ob R (R + A)) ^ 2 := by
    simpa only [Out, Ob] using hoprod T2 Inn (Bt2 R) (Nb R (R + A))
      (hBt2 R hR) (hNb R hR (R + A) hRA) hT2 hInn
  rw [lc0VB_eq_lc0VBField (I := I) (M := M) g₀ g₁]
  have htwo := jet_two (I := I) (M := M) g₀ 2 2 2 Out
  rw [show lc0VBField (I := I) (M := M) g₀ g₁ = (2 : ℝ) • Out by rfl,
    htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤
    (B0 R + B1 R * A) ^ 2
  calc
    _ ≤ 4 * (Ob R (R + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hOut (by norm_num)
    _ = (B0 R + B1 R * A) ^ 2 := by
      dsimp only [B0, B1, Ob, Nb, Ib, Vb]
      ring

/-- Affine `H1` bound for the genuine mixed connection correction.  The
background connection stays in the lower factor and the self-background
Koszul tensor carries the only top derivative. -/
theorem amix_h1_tame
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
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0AMix (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Bt3, hBt3, htr3⟩ := trace_h2 (I := I) (M := M) 3 hDim g₀ hδ₀
  obtain ⟨Bt4, hBt4, htr4⟩ := trace_h2 (I := I) (M := M) 4 hDim g₀ hδ₀
  obtain ⟨BK, hBK, hkbg⟩ := kappaBg_h1 (I := I) (M := M) hDim g₀ gB
  obtain ⟨Cq, hCq, hqprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 2 5 3
  obtain ⟨Cn, hCn, hnprod⟩ := app_h1h2
    (I := I) (M := M) hDim g₀ 2 3 6
  obtain ⟨Cm, hCm, hmprod⟩ := app_h2h1
    (I := I) (M := M) hDim g₀ 2 6 4
  obtain ⟨Co, hCo, hoprod⟩ := app_h2h1
    (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w ↦ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Qb : ℝ → ℝ → ℝ := fun R J ↦ Cq * Bt3 R * (sf 2 * (4 * J))
  let Nb : ℝ → ℝ → ℝ := fun R J ↦ Cn * (sf 3 * BK R) * Qb R J
  let Mb : ℝ → ℝ → ℝ := fun R J ↦ Cm * Bt4 R * Nb R J
  let Ob : ℝ → ℝ → ℝ := fun R J ↦ Co * Bt2 R * Mb R J
  let B0 : ℝ → ℝ := fun R ↦ 4 * Ob R R
  let B1 : ℝ → ℝ := fun R ↦ 4 * Ob R 1
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w ↦ Real.sqrt_nonneg _
  have hQb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Qb R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCq (hBt3 R hR))
      (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hJ))
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Nb R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR)))
      (hQb R hR J hJ)
  have hMb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Mb R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCm (hBt4 R hR)) (hNb R hR J hJ)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ J : ℝ, 0 ≤ J → 0 ≤ Ob R J := by
    intro R hR J hJ
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR)) (hMb R hR J hJ)
  refine ⟨B0, B1, fun R hR ↦
      mul_nonneg (by norm_num) (hOb R hR R hR),
    fun R hR ↦ mul_nonneg (by norm_num) (hOb R hR 1 zero_le_one), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  have hRA : 0 ≤ R + A := add_nonneg hR hA
  have htop2 : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htop 2
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (R + A) ^ 2 := by
    calc
      _ = (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ]
      _ ≤ R ^ 2 + A ^ 2 := add_le_add hP2 htop2
      _ ≤ (R + A) ^ 2 := by nlinarith [mul_nonneg hR hA]
  let T2a : SmoothCcTensor g₀ 4 2 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0AMixPerm2
  let T2b : SmoothCcTensor g₀ 4 2 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 2
      (lc0SwapOutPerm * lieCorr0AMixPerm2)
  let T3 : SmoothCcTensor g₀ 5 3 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ
  let T4 : SmoothCcTensor g₀ 6 4 :=
    lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1
  let K0 : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let KB : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ gB
  let K0s : SmoothCcTensor g₀ 2 5 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 2 K0
  let Q : SmoothCcTensor g₀ 2 3 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3 T3 K0s
  let KBs : SmoothCcTensor g₀ 3 6 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 3 KB
  let N : SmoothCcTensor g₀ 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6 KBs Q
  let Mid : SmoothCcTensor g₀ 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 T4 N
  let Oa : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2a Mid
  let Ob' : SmoothCcTensor g₀ 2 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 T2b Mid
  have hT2a : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2a‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2a] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm2 R hR hP2
  have hT2b : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2b‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2b] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      (lc0SwapOutPerm * lieCorr0AMixPerm2) R hR hP2
  have hT3 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 5 3 i T3‖ ^ 2) ≤ (Bt3 R) ^ 2 := by
    simpa only [T3] using htr3 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPermQ R hR hP2
  have hT4 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 6 4 i T4‖ ^ 2) ≤ (Bt4 R) ^ 2 := by
    simpa only [T4] using htr4 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm1 R hR hP2
  have hK0 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K0‖ ^ 2) ≤ (4 * (R + A)) ^ 2 := by
    simpa only [K0] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie (R + A) hRA hP3
  have hKB : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i KB‖ ^ 2) ≤ (BK R) ^ 2 := by
    simpa only [KB] using hkbg g₁ P htie R hR hP2
  have hK0s : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 5 i K0s‖ ^ 2) ≤
        (sf 2 * (4 * (R + A))) ^ 2 := by
    simpa only [K0s, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 2 K0 (4 * (R + A)) hK0
  have hQ : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Q‖ ^ 2) ≤
        (Qb R (R + A)) ^ 2 := by
    simpa only [Q, Qb] using hqprod T3 K0s (Bt3 R) (sf 2 * (4 * (R + A)))
      (hBt3 R hR) (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hRA)) hT3 hK0s
  have hKBs : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 3 6 i KBs‖ ^ 2) ≤
        (sf 3 * BK R) ^ 2 := by
    simpa only [KBs, sf] using slotIter_h1b
      (I := I) (M := M) g₀ 0 3 3 KB (BK R) hKB
  have hN : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 6 i N‖ ^ 2) ≤
        (Nb R (R + A)) ^ 2 := by
    simpa only [N, Nb] using hnprod KBs Q (sf 3 * BK R) (Qb R (R + A))
      (mul_nonneg (hsf 3) (hBK R hR)) (hQb R hR (R + A) hRA) hKBs hQ
  have hMid : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Mid‖ ^ 2) ≤
        (Mb R (R + A)) ^ 2 := by
    simpa only [Mid, Mb] using hmprod T4 N (Bt4 R) (Nb R (R + A))
      (hBt4 R hR) (hNb R hR (R + A) hRA) hT4 hN
  have hOa : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Oa‖ ^ 2) ≤
        (Ob R (R + A)) ^ 2 := by
    simpa only [Oa, Ob] using hoprod T2a Mid (Bt2 R) (Mb R (R + A))
      (hBt2 R hR) (hMb R hR (R + A) hRA) hT2a hMid
  have hOb' : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Ob'‖ ^ 2) ≤
        (Ob R (R + A)) ^ 2 := by
    simpa only [Ob', Ob] using hoprod T2b Mid (Bt2 R) (Mb R (R + A))
      (hBt2 R hR) (hMb R hR (R + A) hRA) hT2b hMid
  have hsum := jet_add (I := I) (M := M) g₀ 2 2 2 Oa Ob'
    (Ob R (R + A)) (Ob R (R + A)) hOa hOb'
  rw [lc0AMix_eq_lc0AMixField (I := I) (M := M) g₀ g₁ gB]
  have htwo := jet_two (I := I) (M := M) g₀ 2 2 2 (Oa + Ob')
  rw [show lc0AMixField (I := I) (M := M) g₀ g₁ gB =
      (2 : ℝ) • (Oa + Ob') by rfl, htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (Oa + Ob')‖ ^ 2) ≤
    (B0 R + B1 R * A) ^ 2
  calc
    _ ≤ 4 * (2 * ((Ob R (R + A)) ^ 2 + (Ob R (R + A)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B0 R + B1 R * A) ^ 2 := by
      dsimp only [B0, B1, Ob, Mb, Nb, Qb]
      ring

/-- Affine `H1` bound for the cancellation-preserving `DLb + lieCorr0` tail. -/
theorem tail_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_nonneg : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
              lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Bd0, Bd1, hBd0, hBd1, hdlb⟩ :=
    dlbDiff_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀
  obtain ⟨Bi, hBi, hins⟩ :=
    insert_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀
  obtain ⟨Bv0, Bv1, hBv0, hBv1, hvb⟩ :=
    vb_h1_tame (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Ba0, Ba1, hBa0, hBa1, ham⟩ :=
    amix_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀
  obtain ⟨Br0, Br1, hBr0, hBr1, hriem⟩ :=
    riem_h1_tame (I := I) (M := M) hDim g₀ hδ₀
  let S0 : ℝ → ℝ := fun R ↦
    Bd0 R + Bi R + Bv0 R + Ba0 R + Br0 R
  let S1 : ℝ → ℝ := fun R ↦
    Bd1 R + Bv1 R + Ba1 R + Br1 R
  let c5 : ℝ := Real.sqrt 5
  let B0 : ℝ → ℝ := fun R ↦ c5 * S0 R
  let B1 : ℝ → ℝ := fun R ↦ c5 * S1 R
  have hc5 : 0 ≤ c5 := Real.sqrt_nonneg _
  have hS0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S0 R := by
    intro R hR
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (hBd0 R hR) (hBi R hR)) (hBv0 R hR)) (hBa0 R hR)) (hBr0 R hR)
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := by
    intro R hR
    exact add_nonneg (add_nonneg (add_nonneg
      (hBd1 R hR) (hBv1 R hR)) (hBa1 R hR)) (hBr1 R hR)
  refine ⟨B0, B1, fun R hR ↦ mul_nonneg hc5 (hS0 R hR),
    fun R hR ↦ mul_nonneg hc5 (hS1 R hR), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 htop
  let D : ℝ := Bd0 R + Bd1 R * A
  let Ins : ℝ := Bi R
  let V : ℝ := Bv0 R + Bv1 R * A
  let Am : ℝ := Ba0 R + Ba1 R * A
  let Rm : ℝ := Br0 R + Br1 R * A
  let S : ℝ := D + Ins + V + Am + Rm
  have hD : 0 ≤ D := add_nonneg (hBd0 R hR) (mul_nonneg (hBd1 R hR) hA)
  have hIns : 0 ≤ Ins := hBi R hR
  have hV : 0 ≤ V := add_nonneg (hBv0 R hR) (mul_nonneg (hBv1 R hR) hA)
  have hAm : 0 ≤ Am := add_nonneg (hBa0 R hR) (mul_nonneg (hBa1 R hR) hA)
  have hRm : 0 ≤ Rm := add_nonneg (hBr0 R hR) (mul_nonneg (hBr1 R hR) hA)
  have hDjet := hdlb g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hIjet := hins g₁ P htie hδ_le hδ_nonneg hbound R hR hP2
  have hVjet := hvb g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hAjet := ham g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hRjet := hriem g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 htop
  have hraw := tail_h1_parts (I := I) (M := M) g₀ g₁ g_bg
    D Ins V Am Rm (by simpa only [D] using hDjet)
    (by simpa only [Ins] using hIjet) (by simpa only [V] using hVjet)
    (by simpa only [Am] using hAjet) (by simpa only [Rm] using hRjet)
  have hsq : D ^ 2 + Ins ^ 2 + V ^ 2 + Am ^ 2 + Rm ^ 2 ≤ S ^ 2 := by
    dsimp only [S]
    nlinarith [mul_nonneg hD hIns, mul_nonneg hD hV, mul_nonneg hD hAm,
      mul_nonneg hD hRm, mul_nonneg hIns hV, mul_nonneg hIns hAm,
      mul_nonneg hIns hRm, mul_nonneg hV hAm, mul_nonneg hV hRm,
      mul_nonneg hAm hRm]
  have hinside : 0 ≤ 5 * (D ^ 2 + Ins ^ 2 + V ^ 2 + Am ^ 2 + Rm ^ 2) := by
    positivity
  rw [Real.sq_sqrt hinside] at hraw
  have hfactor : c5 * S = B0 R + B1 R * A := by
    dsimp only [c5, S, D, Ins, V, Am, Rm, B0, B1, S0, S1]
    ring
  calc
    _ ≤ 5 * (D ^ 2 + Ins ^ 2 + V ^ 2 + Am ^ 2 + Rm ^ 2) := hraw
    _ ≤ 5 * S ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (c5 * S) ^ 2 := by
      dsimp only [c5]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    _ = (B0 R + B1 R * A) ^ 2 := by rw [hfactor]

-- The affine assembly combines several rank-changing coefficient estimates.
/-- A lower endpoint `H2` radius and an independent endpoint `H3` radius give
the complete affine `H1` bound for `rhsLow0Coeff` along the same convex path. -/
theorem rhs0_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (rhsLow0Coeff (I := I) (M := M) g₀ g_bg
                T T' hδ hδ' s)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C2, hC2, hpath2⟩ := convex_h2_jet (I := I) (M := M) g₀
  obtain ⟨C3, hC3, hpath3⟩ := convex_h3_jet (I := I) (M := M) g₀
  obtain ⟨Br0, Br1, hBr0, hBr1, hric⟩ :=
    ricci0_h1_tame (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨Bd0, Bd1, hBd0, hBd1, hdla⟩ :=
    dla_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  obtain ⟨Bt0, Bt1, hBt0, hBt1, htail⟩ :=
    tail_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  let R0 : ℝ → ℝ := fun R ↦ Br0 (C2 * R)
  let R1 : ℝ → ℝ := fun R ↦ Br1 (C2 * R) * C3
  let D0 : ℝ → ℝ := fun R ↦ Bd0 (C2 * R)
  let D1 : ℝ → ℝ := fun R ↦ Bd1 (C2 * R) * C3
  let T0 : ℝ → ℝ := fun R ↦ Bt0 (C2 * R)
  let T1 : ℝ → ℝ := fun R ↦ Bt1 (C2 * R) * C3
  let B0 : ℝ → ℝ := fun R ↦ 4 * (R0 R + D0 R + T0 R)
  let B1 : ℝ → ℝ := fun R ↦ 4 * (R1 R + D1 R + T1 R)
  have hCR : ∀ R : ℝ, 0 ≤ R → 0 ≤ C2 * R := fun R hR ↦
    mul_nonneg hC2 hR
  have hR0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R0 R := fun R hR ↦
    hBr0 (C2 * R) (hCR R hR)
  have hR1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ R1 R := fun R hR ↦
    mul_nonneg (hBr1 (C2 * R) (hCR R hR)) hC3
  have hD0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D0 R := fun R hR ↦
    hBd0 (C2 * R) (hCR R hR)
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR ↦
    mul_nonneg (hBd1 (C2 * R) (hCR R hR)) hC3
  have hT0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ T0 R := fun R hR ↦
    hBt0 (C2 * R) (hCR R hR)
  have hT1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ T1 R := fun R hR ↦
    mul_nonneg (hBt1 (C2 * R) (hCR R hR)) hC3
  refine ⟨B0, B1, fun R hR ↦ mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hR0 R hR) (hD0 R hR)) (hT0 R hR)),
    fun R hR ↦ mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hR1 R hR) (hD1 R hR)) (hT1 R hR)), ?_⟩
  intro T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3' s hs
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s
  have hlow : 0 ≤ C2 * R := mul_nonneg hC2 hR
  have hhigh : 0 ≤ C3 * A := mul_nonneg hC3 hA
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C2 * R) ^ 2 := by
    simpa only [P] using hpath2 T T' R hR hT2 hT2' s hs
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C3 * A) ^ 2 := by
    simpa only [P] using hpath3 T T' A hA hT3 hT3' s hs
  have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, Finset.sum_range_succ]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
  have htopSq : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤
      (C3 * A) ^ 2 := hsingle.trans hP3
  have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ C3 * A := by
    nlinarith [htopSq, hhigh,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 3 P)]
  have hPbound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using realizedFam_inner_of_mem
      (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ₀_lt hδ₀_lt hs) y v w
  let Ric : SmoothCcTensor g₀ 2 2 :=
    linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
  let DLa : SmoothCcTensor g₀ 2 2 :=
    deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg
  let Tail : SmoothCcTensor g₀ 2 2 :=
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
      lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg
  let RB : ℝ := R0 R + R1 R * A
  let DB : ℝ := D0 R + D1 R * A
  let TB : ℝ := T0 R + T1 R * A
  have hRB : 0 ≤ RB := add_nonneg (hR0 R hR) (mul_nonneg (hR1 R hR) hA)
  have hDB : 0 ≤ DB := add_nonneg (hD0 R hR) (mul_nonneg (hD1 R hR) hA)
  have hTB : 0 ≤ TB := add_nonneg (hT0 R hR) (mul_nonneg (hT1 R hR) hA)
  have hRicRaw := hric g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 htop
  have hRic : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Ric‖ ^ 2) ≤ RB ^ 2 := by
    simpa only [Ric, RB, R0, R1, mul_assoc] using hRicRaw
  have hDlaRaw := hdla g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 htop
  have hDla : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i DLa‖ ^ 2) ≤ DB ^ 2 := by
    simpa only [DLa, DB, D0, D1, mul_assoc] using hDlaRaw
  have hTailRaw := htail g₁ P htie (_hδ_le := le_rfl) hδ₀_nonneg hPbound
    (C2 * R) (C3 * A) hlow hhigh hP2 htop
  have hTail : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Tail‖ ^ 2) ≤ TB ^ 2 := by
    simpa only [Tail, TB, T0, T1, mul_assoc] using hTailRaw
  have hMidRaw := jet_add (I := I) (M := M) g₀ 2 2 2 DLa Tail
    DB TB hDla hTail
  have hMid : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (DLa + Tail)‖ ^ 2) ≤
      (2 * (DB + TB)) ^ 2 := by
    refine hMidRaw.trans ?_
    nlinarith [sq_nonneg DB, sq_nonneg TB, mul_nonneg hDB hTB]
  have hRic2 : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i ((-2 : ℝ) • Ric)‖ ^ 2) ≤
      (2 * RB) ^ 2 := by
    rw [jet_neg_two (I := I) (M := M) g₀ 2 2 2 Ric]
    calc
      4 * (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Ric‖ ^ 2)
          ≤ 4 * RB ^ 2 := mul_le_mul_of_nonneg_left hRic (by norm_num)
      _ = (2 * RB) ^ 2 := by ring
  have hout := jet_add (I := I) (M := M) g₀ 2 2 2
    ((-2 : ℝ) • Ric) (DLa + Tail) (2 * RB) (2 * (DB + TB)) hRic2 hMid
  have hbound : 2 * ((2 * RB) ^ 2 + (2 * (DB + TB)) ^ 2) ≤
      (4 * (RB + DB + TB)) ^ 2 := by
    nlinarith [sq_nonneg RB, sq_nonneg (DB + TB),
      mul_nonneg hRB (add_nonneg hDB hTB)]
  have hfactor : 4 * (RB + DB + TB) = B0 R + B1 R * A := by
    dsimp only [RB, DB, TB, B0, B1]
    ring
  have hrhs : rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s =
      (-2 : ℝ) • Ric + (DLa + Tail) := by
    simp only [rhsLow0Coeff, linearizedRicciConnDiffOrder0Coeff,
      Ric, DLa, Tail, g₁]
    rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField]
    abel
  rw [hrhs]
  exact hout.trans (hbound.trans_eq (by rw [hfactor]))

end DifferentialGeometry.PDE.RicciFlow
