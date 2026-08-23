import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricComparisonEndomorphismJetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.GagliardoNirenberg
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
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

private def invJetGrid
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (i : ℕ) (x : M) : ℝ :=
  ∑ n ∈ Finset.range (i + 1),
    ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
      ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g 0 2 (e m) T).toSection x)


theorem exists_inverseMetricDifferenceSlotCoefficient_secondOrder_bound_uniform
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
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2) ∧
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
              (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  have hdim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hmorrey⟩ :=
    morreyTwoC_spec (I := I) (M := M) gBase
      (le_trans zero_le_one hΛ) hdim
  obtain ⟨Cinv, hCinv, hinv⟩ :=
    invDiff_grid_unif (I := I) (M := M)
      (show (1 / 2 : ℝ) < 1 by norm_num)
  let Cpt : ℝ := morreyTwoC (I := I) (M := M) gBase Λ
  let Cop : ℝ := hs2OpActionC Cpt Kcurv.rankTwo
  let Ch : ℝ := h2CovsumC Kcurv.rankTwo
  let ρ : ℝ := min 1 (4 * Cop)⁻¹
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let n : ℝ := Module.finrank ℝ E
  let Kpt : ℝ := (2 * n * Cop) ^ 2
  let K₀ : ℝ := Kpt * vol
  let K₁ : ℝ := Cinv 1 *
    rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 1 Ch * Ch ^ 2
  let K₂ : ℝ := Cinv 2 *
    rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 2 Ch * Ch ^ 2
  let K : ℝ := Kpt + K₀ + K₁ + K₂
  have hCpt' : 0 ≤ Cpt := by simpa only [Cpt] using hCpt
  have hCop : 0 < Cop := by
    dsimp only [Cop]
    exact hs2OpActionC_pos hCpt' Kcurv.rankTwo
  have hCh : 0 ≤ Ch := by
    dsimp only [Ch]
    exact h2CovsumC_nonneg Kcurv.rankTwo
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min (by norm_num) (inv_pos.mpr (mul_pos (by norm_num) hCop))
  have hvol : 0 ≤ vol := by
    dsimp only [vol]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hn : 0 ≤ n := by
    dsimp only [n]
    exact Nat.cast_nonneg _
  have hKpt : 0 ≤ Kpt := by dsimp only [Kpt]; positivity
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by
    dsimp only [K₁]
    exact mul_nonneg
      (mul_nonneg (hCinv 1)
        (rank_two_grid_nonneg (E := E) (I := I) (M := M)
          gBase Λ 1 Ch))
      (sq_nonneg Ch)
  have hK₂ : 0 ≤ K₂ := by
    dsimp only [K₂]
    exact mul_nonneg
      (mul_nonneg (hCinv 2)
        (rank_two_grid_nonneg (E := E) (I := I) (M := M)
          gBase Λ 2 Ch))
      (sq_nonneg Ch)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨ρ, Real.sqrt K, hρ, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T g₁ hT htie
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hact : IsCurvAction0 (I := I) (M := M) g 2 Kcurv.rankTwo :=
    (hKcurv.bounds g hEq hjet).1
  have hmor : ∀ (S : SmoothCcTensor g 0 2) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) ≤
        Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2 := by
    simpa only [Cpt] using hmorrey g hEq hjet1 hjet2
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let δ : ℝ := Cop * N
  have hN : 0 ≤ N := norm_nonneg _
  have hNρ : N ≤ ρ := by simpa only [N] using hT
  have hN1 : N ≤ 1 := hNρ.trans (by dsimp only [ρ]; exact min_le_left _ _)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδfour : δ ≤ 1 / 4 := by
    calc
      δ = Cop * N := rfl
      _ ≤ Cop * ρ := mul_le_mul_of_nonneg_left hNρ hCop.le
      _ ≤ Cop * (4 * Cop)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (by dsimp only [ρ]; exact min_le_right _ _) hCop.le
      _ = 1 / 4 := by field_simp [ne_of_gt hCop]
  have hδhalf : δ < 1 / 2 := by linarith
  have hδone : δ < 1 := by linarith
  have hbound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ := by
    simpa only [δ, Cop, N] using
      (hs2_op_bound_action (I := I) (M := M) hDim g hact hCpt' hmor T)
  have hratio : δ / (1 - δ) ≤ 2 * δ := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).2
    nlinarith [mul_nonneg hδ (show 0 ≤ 1 - 2 * δ by linarith)]
  have hratio_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ (by linarith)
  have hjetSum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ Ch * N := by
    simpa only [Ch, N] using
      (covsum_hs_two (I := I) (M := M) g 2 hact T)
  have hjetSq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ (Ch * N) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg _)).trans
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hjetSum 2)
  have hCN : Ch * N ≤ Ch := by
    calc
      Ch * N ≤ Ch * 1 := mul_le_mul_of_nonneg_left hN1 hCh
      _ = Ch := by ring
  have hjetBall :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ Ch ^ 2 :=
    hjetSq.trans (pow_le_pow_left₀ (mul_nonneg hCh hN) hCN 2)
  have hinv₀_pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x) ≤
        Kpt * N ^ 2 := by
    intro x
    have hb := riemannianFiberNormSq_gInvDiffSlotEndo_le
      (I := I) (M := M) g g₁
      (ccTensorBilinSymm (I := I) g T) htie hδone hδ hbound x
    have hmul : n * (δ / (1 - δ)) ≤ 2 * n * Cop * N := by
      calc
        n * (δ / (1 - δ)) ≤ n * (2 * δ) :=
          mul_le_mul_of_nonneg_left hratio hn
        _ = 2 * n * Cop * N := by dsimp only [δ]; ring
    calc
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x) ≤
          (n * (δ / (1 - δ))) ^ 2 := by simpa only [n] using hb
      _ ≤ (2 * n * Cop * N) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hn hratio_nn) hmul 2
      _ = Kpt * N ^ 2 := by dsimp only [Kpt]; ring
  have hinv₀ : ‖iteratedCovGrad (I := I) g 2 2 0
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 ≤ K₀ * N ^ 2 := by
    rw [iteratedCovGrad_zero]
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g 2 2
      (inverseMetricDifferenceSlotCoefficient (I := I) g g₁) (Kpt * N ^ 2) hinv₀_pt).trans ?_
    have hvolg := (volumeReal_cross (I := I) (M := M) gBase g hEq).1
    have hvolg' :
        ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤ vol := by
      simpa only [vol] using hvolg
    calc
      Kpt * N ^ 2 *
          ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
          Kpt * N ^ 2 * vol :=
        mul_le_mul_of_nonneg_left hvolg' (mul_nonneg hKpt (sq_nonneg N))
      _ = K₀ * N ^ 2 := by dsimp only [K₀]; ring
  have hinv_pos : ∀ i : ℕ, 1 ≤ i → i ≤ 2 →
      ‖iteratedCovGrad (I := I) g 2 2 i
          (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 ≤
        (Cinv i *
          rankTwoGridC (E := E) (I := I) (M := M) gBase Λ i Ch * Ch ^ 2) *
          N ^ 2 := by
    intro i hi1 hi2
    have hi3 : i < 3 := by omega
    have htop : ‖iteratedCovGrad (I := I) g 0 2 i T‖ ≤ Ch * N :=
      (Finset.single_le_sum
        (s := Finset.range 3)
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
        (fun j _ => norm_nonneg _)
        (Finset.mem_range.mpr hi3)).trans hjetSum
    have hgrid := rank_two_grid_uniform (E := E) (I := I) (M := M)
      hDim gBase (le_trans zero_le_one hΛ) i hi1 g hEq hjet1 hjet2 T Ch (Ch * N)
      hCh (mul_nonneg hCh hN) hjetBall htop
    have hgrid_int : Integrable (invJetGrid (I := I) (M := M) g T i)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [invJetGrid] using hgrid.1
    have hinv_pt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
            ((iteratedCovGrad (I := I) g 2 2 i
              (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)).toSection x) ≤
          Cinv i * invJetGrid (I := I) (M := M) g T i x := by
      intro x
      simpa only [invJetGrid] using
        (hinv g g₁ T htie (show δ ≤ (1 / 2 : ℝ) by linarith)
          hδ hbound i x)
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 2 (2 + i)
      (iteratedCovGrad (I := I) g 2 2 i
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁))
      (fun x => Cinv i * invJetGrid (I := I) (M := M) g T i x)
      (hgrid_int.const_mul (Cinv i)) hinv_pt
    refine hsq.trans ?_
    rw [MeasureTheory.integral_const_mul]
    calc
      Cinv i * (∫ x, invJetGrid (I := I) (M := M) g T i x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          Cinv i *
            (rankTwoGridC (E := E) (I := I) (M := M) gBase Λ i Ch *
              (Ch * N) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [invJetGrid] using hgrid.2) (hCinv i)
      _ = (Cinv i *
          rankTwoGridC (E := E) (I := I) (M := M) gBase Λ i Ch * Ch ^ 2) *
            N ^ 2 := by ring
  have hinv₁ : ‖iteratedCovGrad (I := I) g 2 2 1
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 ≤ K₁ * N ^ 2 := by
    simpa only [K₁] using hinv_pos 1 (by norm_num) (by norm_num)
  have hinv₂ : ‖iteratedCovGrad (I := I) g 2 2 2
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2 ≤ K₂ * N ^ 2 := by
    simpa only [K₂] using hinv_pos 2 (by norm_num) (by norm_num)
  have hsum : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2) ≤
        (K₀ + K₁ + K₂) * N ^ 2 := by
    let f : ℕ → ℝ := fun j => ‖iteratedCovGrad (I := I) g 2 2 j
      (inverseMetricDifferenceSlotCoefficient (I := I) g g₁)‖ ^ 2
    change (∑ j ∈ Finset.range 3, f j) ≤ (K₀ + K₁ + K₂) * N ^ 2
    have hf₀ : f 0 ≤ K₀ * N ^ 2 := by simpa only [f] using hinv₀
    have hf₁ : f 1 ≤ K₁ * N ^ 2 := by simpa only [f] using hinv₁
    have hf₂ : f 2 ≤ K₂ * N ^ 2 := by simpa only [f] using hinv₂
    calc
      ∑ j ∈ Finset.range 3, f j = f 0 + f 1 + f 2 := by
        norm_num [Finset.sum_range_succ]
      _ ≤ K₀ * N ^ 2 + K₁ * N ^ 2 + K₂ * N ^ 2 :=
        add_le_add (add_le_add hf₀ hf₁) hf₂
      _ = (K₀ + K₁ + K₂) * N ^ 2 := by ring
  have hpt_final : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          ((inverseMetricDifferenceSlotCoefficient (I := I) g g₁).toSection x) ≤
        (Real.sqrt K * N) ^ 2 := by
    intro x
    refine (hinv₀_pt x).trans ?_
    rw [mul_pow, Real.sq_sqrt hK]
    dsimp only [K]
    nlinarith [mul_nonneg hKpt (sq_nonneg N),
      mul_nonneg hK₀ (sq_nonneg N), mul_nonneg hK₁ (sq_nonneg N),
      mul_nonneg hK₂ (sq_nonneg N)]
  refine ⟨by simpa only [N] using hpt_final, ?_⟩
  refine hsum.trans ?_
  rw [mul_pow, Real.sq_sqrt hK]
  dsimp only [K]
  nlinarith [mul_nonneg hKpt (sq_nonneg N),
    mul_nonneg hK₀ (sq_nonneg N), mul_nonneg hK₁ (sq_nonneg N),
    mul_nonneg hK₂ (sq_nonneg N)]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
