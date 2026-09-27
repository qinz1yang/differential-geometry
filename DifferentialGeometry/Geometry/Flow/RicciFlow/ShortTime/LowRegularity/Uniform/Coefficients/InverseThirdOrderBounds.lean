import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.InverseSecondOrderBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private def invJetGrid3
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (x : M) : ℝ :=
  ∑ n ∈ Finset.range 4,
    ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
      ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)

theorem inv_coeff_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2) (g₁ : SmoothRiemannianMetric I M),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 2 2 x
                ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x) ≤
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2) ∧
            (∑ j ∈ Finset.range 4,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hinv₂⟩ :=
    exists_inverseMetricDifferenceSlotCoefficient_secondOrder_bound_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  have hdim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hmorrey⟩ :=
    morreyTwoC_spec (I := I) (M := M) gBase
      (le_trans zero_le_one hΛ) hdim
  obtain ⟨Cinv, hCinv, hinv⟩ :=
    invDiff_grid_uniform (I := I) (M := M)
      (show (1 / 2 : ℝ) < 1 by norm_num)
  let Cpt : ℝ := morreyTwoC (I := I) (M := M) gBase Λ
  let Cop : ℝ := hs2OpActionC Cpt Kcurv.rankTwo
  let Ch₂ : ℝ := h2CovsumC Kcurv.rankTwo
  let Ch₃ : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let ρop : ℝ := min 1 (4 * Cop)⁻¹
  let ρ : ℝ := min ρ₂ ρop
  let K₃ : ℝ := Cinv 3 *
    rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 3 Ch₂ * Ch₃ ^ 2
  let K : ℝ := C₂ ^ 2 + K₃
  have hCpt' : 0 ≤ Cpt := by simpa only [Cpt] using hCpt
  have hCop : 0 < Cop := by
    dsimp only [Cop]
    exact hs2OpActionC_pos hCpt' Kcurv.rankTwo
  have hCh₂ : 0 ≤ Ch₂ := by
    dsimp only [Ch₂]
    exact h2CovsumC_nonneg Kcurv.rankTwo
  have hCh₃ : 0 ≤ Ch₃ := by
    dsimp only [Ch₃]
    exact h3CovsumC_nonneg Kcurv.rankTwo Kcurv.rankThree
  have hρop : 0 < ρop := by
    dsimp only [ρop]
    exact lt_min (by norm_num) (inv_pos.mpr (mul_pos (by norm_num) hCop))
  have hρ : 0 < ρ := lt_min hρ₂ hρop
  have hK₃ : 0 ≤ K₃ := by
    dsimp only [K₃]
    exact mul_nonneg
      (mul_nonneg (hCinv 3)
        (rank_two_grid_nonneg (E := E) (I := I) (M := M)
          gBase Λ 3 Ch₂))
      (sq_nonneg Ch₃)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨ρ, Real.sqrt K, hρ, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T g₁ hT₂ htie
  have hT₂base :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₂ :=
    hT₂.trans (by dsimp only [ρ]; exact min_le_left _ _)
  obtain ⟨hpt₂, hjets₂⟩ := hinv₂ g hEq hjet T g₁ hT₂base htie
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  obtain ⟨hact₂, hact₃⟩ := hKcurv.bounds g hEq hjet
  have hmor : ∀ (S : SmoothCcTensor g 0 2) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) ≤
        Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2 := by
    simpa only [Cpt] using hmorrey g hEq hjet1 hjet2
  let N₂ : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let N₃ : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let δ : ℝ := Cop * N₂
  have hN₂ : 0 ≤ N₂ := norm_nonneg _
  have hN₃ : 0 ≤ N₃ := norm_nonneg _
  have hN₂N₃ : N₂ ≤ N₃ := by
    dsimp only [N₂, N₃]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hN₂ρop : N₂ ≤ ρop := by
    simpa only [N₂] using
      hT₂.trans (by dsimp only [ρ]; exact min_le_right _ _)
  have hN₂one : N₂ ≤ 1 :=
    hN₂ρop.trans (by dsimp only [ρop]; exact min_le_left _ _)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδfour : δ ≤ 1 / 4 := by
    calc
      δ = Cop * N₂ := rfl
      _ ≤ Cop * ρop := mul_le_mul_of_nonneg_left hN₂ρop hCop.le
      _ ≤ Cop * (4 * Cop)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (by dsimp only [ρop]; exact min_le_right _ _) hCop.le
      _ = 1 / 4 := by field_simp [ne_of_gt hCop]
  have hδhalf : δ < 1 / 2 := by linarith
  have hδone : δ < 1 := by linarith
  have hbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ := by
    simpa only [δ, Cop, N₂] using
      (hs2_op_bound_action (I := I) (M := M) hDim g hact₂ hCpt' hmor T)
  have hjetSum₂ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ Ch₂ * N₂ := by
    simpa only [Ch₂, N₂] using
      (covsum_hs_two (I := I) (M := M) g 2 hact₂ T)
  have hjetSq₂ :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Ch₂ ^ 2 := by
    have hsumSq :
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
    have hChN : Ch₂ * N₂ ≤ Ch₂ := by
      calc
        Ch₂ * N₂ ≤ Ch₂ * 1 := mul_le_mul_of_nonneg_left hN₂one hCh₂
        _ = Ch₂ := by ring
    exact hsumSq.trans ((pow_le_pow_left₀
      (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hjetSum₂ 2).trans
        (pow_le_pow_left₀ (mul_nonneg hCh₂ hN₂) hChN 2))
  have hjetSum₃ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ Ch₃ * N₃ := by
    simpa only [Ch₃, N₃] using
      (covsum_hs_three (I := I) (M := M) g 2 hact₂ hact₃ T)
  have htop :
      ‖iteratedCovGrad (I := I) g 0 2 3 T‖ ≤ Ch₃ * N₃ :=
    (Finset.single_le_sum
      (s := Finset.range 4)
      (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
      (fun j _ => norm_nonneg _)
      (show 3 ∈ Finset.range 4 by norm_num)).trans hjetSum₃
  have hgrid := rank_two_grid_uniform (E := E) (I := I) (M := M)
    hDim gBase (le_trans zero_le_one hΛ) 3 (by norm_num) g hEq hjet1 hjet2
      T Ch₂ (Ch₃ * N₃) hCh₂ (mul_nonneg hCh₃ hN₃) hjetSq₂ htop
  have hgrid_int : Integrable (invJetGrid3 (I := I) (M := M) g T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    with_unfolding_all
      exact hgrid.1
  have hinv_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 5 x
          ((iteratedCovGrad (I := I) g 2 2 3
            (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)).toSection x) ≤
        Cinv 3 * invJetGrid3 (I := I) (M := M) g T x := by
    intro x
    simpa only [invJetGrid3] using
      (hinv g g₁ T htie (show δ ≤ (1 / 2 : ℝ) by linarith)
        hδ hbound 3 x)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 2 5
    (iteratedCovGrad (I := I) g 2 2 3
      (inverseMetricDifferenceSlotCoefficient (I := I) g g₁))
    (fun x => Cinv 3 * invJetGrid3 (I := I) (M := M) g T x)
    (hgrid_int.const_mul (Cinv 3)) hinv_pt
  have hinv₃ :
      ‖iteratedCovGrad (I := I) g 2 2 3
          (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 ≤ K₃ * N₃ ^ 2 := by
    refine hsq.trans ?_
    rw [MeasureTheory.integral_const_mul]
    calc
      Cinv 3 * (∫ x, invJetGrid3 (I := I) (M := M) g T x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          Cinv 3 *
            (rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 3 Ch₂ *
              (Ch₃ * N₃) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [invJetGrid3] using hgrid.2) (hCinv 3)
      _ = K₃ * N₃ ^ 2 := by dsimp only [K₃]; ring
  have hC₂N : C₂ * N₂ ≤ C₂ * N₃ :=
    mul_le_mul_of_nonneg_left hN₂N₃ hC₂
  have hpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x) ≤
        (Real.sqrt K * N₃) ^ 2 := by
    intro x
    calc
      _ ≤ (C₂ * N₂) ^ 2 := by simpa only [N₂] using hpt₂ x
      _ ≤ (C₂ * N₃) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hC₂ hN₂) hC₂N 2
      _ = C₂ ^ 2 * N₃ ^ 2 := by ring
      _ ≤ K * N₃ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg N₃)
        dsimp only [K]
        linarith
      _ = (Real.sqrt K * N₃) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK]
  have hlow :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
        C₂ ^ 2 * N₃ ^ 2 := by
    calc
      _ ≤ (C₂ * N₂) ^ 2 := by simpa only [N₂] using hjets₂
      _ ≤ (C₂ * N₃) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hC₂ hN₂) hC₂N 2
      _ = C₂ ^ 2 * N₃ ^ 2 := by ring
  refine ⟨by simpa only [N₃] using hpoint, ?_⟩
  have hsum :
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤ K * N₃ ^ 2 := by
    calc
      _ = (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) +
          ‖iteratedCovGrad (I := I) g 2 2 3
            (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 := by
        rw [Finset.sum_range_succ]
      _ ≤ C₂ ^ 2 * N₃ ^ 2 + K₃ * N₃ ^ 2 := add_le_add hlow hinv₃
      _ = K * N₃ ^ 2 := by dsimp only [K]; ring
  calc
    _ ≤ K * N₃ ^ 2 := hsum
    _ = (Real.sqrt K * N₃) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK]
    _ = (Real.sqrt K *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
