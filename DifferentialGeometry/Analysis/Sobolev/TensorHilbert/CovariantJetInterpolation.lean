import DifferentialGeometry.Analysis.Estimates.ProductBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

noncomputable section

open Bundle Manifold
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2

private theorem le_mul_of_le_weighted_sq_average {X a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * a ^ 2 + b ^ 2 / t) / 2) :
    X ≤ a * b := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (a + b + 1) with hδdef
  have hden : 0 < a + b + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hbδ : 0 < b + δ := by linarith
  have haδ : 0 < a + δ := by linarith
  have ht : 0 < (b + δ) / (a + δ) := div_pos hbδ haδ
  have hX := h _ ht
  have h1 : (b + δ) / (a + δ) * a ^ 2 ≤ a * b + δ * a := by
    have hkey : a ^ 2 ≤ a * (a + δ) := by nlinarith
    have hstep : (b + δ) / (a + δ) * a ^ 2 ≤
        (b + δ) / (a + δ) * (a * (a + δ)) :=
      mul_le_mul_of_nonneg_left hkey (le_of_lt ht)
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have h2 : b ^ 2 / ((b + δ) / (a + δ)) ≤ a * b + δ * b := by
    rw [div_div_eq_mul_div]
    rw [div_le_iff₀ hbδ]
    nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le,
      mul_nonneg (mul_nonneg hb hδ.le) hδ.le, sq_nonneg b]
  have hsum : (((b + δ) / (a + δ)) * a ^ 2 +
      b ^ 2 / ((b + δ) / (a + δ))) / 2 ≤ a * b + δ * (a + b) / 2 := by
    have := add_le_add h1 h2
    linarith
  have hfin : δ * (a + b) / 2 ≤ ε := by
    rw [hδdef]
    rw [div_mul_eq_mul_div, div_div]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (a + b + 1) * 2)]
    nlinarith [hε.le, ha, hb]
  linarith [hX, hsum, hfin]

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
private theorem tensorSobolevWeight_three_le_weighted_average_two_four
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g 0 s) {t : ℝ} (ht : 0 < t) :
    tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) ≤
      (t * tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) / t) / 2 := by
  have e2 : tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 2 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 2
  have e3 : tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 3 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 3
  have e4 : tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ 4 := by
    simp only [tensorSobolevWeight]
    exact Real.rpow_natCast _ 4
  rw [e2, e3, e4]
  set w : ℝ := 1 + TensorEigenIdx.lambda (I := I) (M := M) i
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hcancel : t * (w ^ 4 / t) = w ^ 4 := by
    field_simp
  have hprod : t * (w ^ 3 * 2) ≤ t * (t * w ^ 2 + w ^ 4 / t) := by
    have hq : t * (t * w ^ 2 + w ^ 4 / t) = t ^ 2 * w ^ 2 + w ^ 4 := by
      rw [mul_add, hcancel]
      ring
    rw [hq]
    nlinarith [sq_nonneg (t * w - w ^ 2)]
  exact le_of_mul_le_mul_left hprod ht

private theorem ccTensorToHs_norm_three_sq_le_weighted_average_two_four
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {t : ℝ} (ht : 0 < t) :
    ‖ccTensorToHs (I := I) (M := M) g s ((3 : ℕ) : ℝ) S‖ ^ 2 ≤
      (t * ‖ccTensorToHs (I := I) (M := M) g s ((2 : ℕ) : ℝ) S‖ ^ 2 +
        ‖ccTensorToHs (I := I) (M := M) g s ((4 : ℕ) : ℝ) S‖ ^ 2 / t) / 2 := by
  classical
  let c : TensorEigenIdx (I := I) (M := M) g 0 s → ℝ := fun i =>
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
      (SmoothCcTensor.toL2 S) i
  have hn : ∀ σ : ℝ, ‖ccTensorToHs (I := I) (M := M) g s σ S‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2 := by
    intro σ
    rw [TensorHs.norm_sq_eq_tsum]
    rfl
  have hsm : ∀ σ : ℝ, Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (c i) ^ 2) := by
    intro σ
    exact (ccTensorToHs (I := I) (M := M) g s σ S).weighted_summable
  have hkey : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 s,
      tensorSobolevWeight (I := I) (M := M) i ((3 : ℕ) : ℝ) * (c i) ^ 2 ≤
        (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
            (c i) ^ 2) +
          tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
            (c i) ^ 2 / t) / 2 := by
    intro i
    have hweight := tensorSobolevWeight_three_le_weighted_average_two_four
      (I := I) (M := M) g i ht
    have hstep := mul_le_mul_of_nonneg_right hweight (sq_nonneg (c i))
    refine hstep.trans (le_of_eq ?_)
    field_simp
  have hsumR : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 s =>
      (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2 / t) / 2) :=
    (((hsm _).mul_left t).add ((hsm _).div_const t)).div_const 2
  have hle := Summable.tsum_le_tsum hkey (hsm _) hsumR
  have htsum : (∑' i : TensorEigenIdx (I := I) (M := M) g 0 s,
      (t * (tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2 / t) / 2) =
      (t * (∑' i, tensorSobolevWeight (I := I) (M := M) i ((2 : ℕ) : ℝ) *
          (c i) ^ 2) +
        (∑' i, tensorSobolevWeight (I := I) (M := M) i ((4 : ℕ) : ℝ) *
          (c i) ^ 2) / t) / 2 := by
    rw [tsum_div_const,
      Summable.tsum_add ((hsm _).mul_left t) ((hsm _).div_const t),
      tsum_mul_left, tsum_div_const]
  rw [hn ((3 : ℕ) : ℝ), hn ((2 : ℕ) : ℝ), hn ((4 : ℕ) : ℝ)]
  rw [← htsum]
  exact hle

theorem ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g s ((3 : ℕ) : ℝ) S‖ ^ 2 ≤
      ‖ccTensorToHs (I := I) (M := M) g s ((2 : ℕ) : ℝ) S‖ *
        ‖ccTensorToHs (I := I) (M := M) g s ((4 : ℕ) : ℝ) S‖ := by
  exact le_mul_of_le_weighted_sq_average (norm_nonneg _) (norm_nonneg _)
    (fun _ ht => ccTensorToHs_norm_three_sq_le_weighted_average_two_four
      (I := I) (M := M) g s S ht)

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem covariantJetNormSq_le_sq_sum_norm
    (g : SmoothRiemannianMetric I M) {s : ℕ} (n : ℕ)
    (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g n S ≤
      (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 := by
  unfold covariantJetNormSq
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem sq_sum_norm_le_mul_covariantJetNormSq
    (g : SmoothRiemannianMetric I M) {s : ℕ} (n : ℕ)
    (S : SmoothCcTensor g 0 s) :
    (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
      ((n : ℝ) + 1) * covariantJetNormSq (I := I) (M := M) g n S := by
  unfold covariantJetNormSq
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun _ => (1 : ℝ)) (fun j => ‖iteratedCovGrad (I := I) g 0 s j S‖)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using h

theorem exists_covariantJetNormSq_le_spectralSobolevNorm_sq
    (g : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g 0 s,
        covariantJetNormSq (I := I) (M := M) g n S ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) S‖) ^ 2 := by
  obtain ⟨C, hC, hjet⟩ := hsJet_le (I := I) (M := M) g s n
  refine ⟨C, hC, fun S => ?_⟩
  exact (covariantJetNormSq_le_sq_sum_norm (I := I) (M := M) g n S).trans
    (pow_le_pow_left₀
      (Finset.sum_nonneg fun j _ =>
        norm_nonneg (iteratedCovGrad (I := I) g 0 s j S))
      (hjet S) 2)

theorem exists_spectralSobolevNorm_le_of_covariantJetNormSq_le_sq
    (g : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 s) (Q : ℝ), 0 ≤ Q →
        covariantJetNormSq (I := I) (M := M) g n S ≤ Q ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) S‖ ≤ C * Q := by
  obtain ⟨C₀, hC₀, hs⟩ := hs_le_jet (I := I) (M := M) g s n
  refine ⟨C₀ * (n + 1), mul_nonneg hC₀ (by positivity), ?_⟩
  intro S Q hQ hS
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 s j S‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 s j S‖ ^ 2 ≤
          covariantJetNormSq (I := I) (M := M) g n S :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 s i S‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    exact (sq_le_sq₀ (norm_nonneg _) hQ).mp (hsingle.trans hS)
  have hsum :
      ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖ ≤ (n + 1 : ℝ) * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (n + 1), Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = (n + 1 : ℝ) * Q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_cast
  calc
    ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) S‖ ≤
        C₀ * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖ := hs S
    _ ≤ C₀ * ((n + 1 : ℝ) * Q) :=
      mul_le_mul_of_nonneg_left hsum hC₀
    _ = (C₀ * (n + 1)) * Q := by ring

theorem covariantJetNormSq_three_interpolation
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 s) (R A4 : ℝ), 0 ≤ R → 0 ≤ A4 →
        covariantJetNormSq (I := I) (M := M) g 2 S ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 S ≤ A4 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 3 S ≤ C * (R * A4) := by
  obtain ⟨C3, hC3, hjet3⟩ := hsJet_le (I := I) (M := M) g s 3
  obtain ⟨K2, hK2, hhs2⟩ := hs_le_jet (I := I) (M := M) g s 2
  obtain ⟨K4, hK4, hhs4⟩ := hs_le_jet (I := I) (M := M) g s 4
  refine ⟨C3 ^ 2 * (K2 * Real.sqrt 3) * (K4 * Real.sqrt 5),
    by positivity, ?_⟩
  intro S R A4 hR hA4 h2 h4
  set N2 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((2 : ℕ) : ℝ) S‖
  set N3 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((3 : ℕ) : ℝ) S‖
  set N4 : ℝ := ‖ccTensorToHs (I := I) (M := M) g s ((4 : ℕ) : ℝ) S‖
  have hup : covariantJetNormSq (I := I) (M := M) g 3 S ≤ C3 ^ 2 * N3 ^ 2 := by
    refine (covariantJetNormSq_le_sq_sum_norm (I := I) (M := M) g 3 S).trans ?_
    have h := hjet3 S
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (3 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc
      (∑ j ∈ Finset.range (3 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
        (C3 * N3) ^ 2 := pow_le_pow_left₀ hnn h 2
      _ = C3 ^ 2 * N3 ^ 2 := by ring
  have hN2le : N2 ≤ K2 * Real.sqrt 3 * R := by
    refine (hhs2 S).trans ?_
    have hcs := sq_sum_norm_le_mul_covariantJetNormSq
      (I := I) (M := M) g 2 S
    have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hbd : (∑ j ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤ Real.sqrt 3 * R := by
      have hstep : (∑ j ∈ Finset.range (2 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
          (Real.sqrt 3 * R) ^ 2 := by
        refine hcs.trans ?_
        have hsq : (Real.sqrt 3 * R) ^ 2 = 3 * R ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        rw [hsq]
        norm_num
        exact h2
      have hb : (0 : ℝ) ≤ Real.sqrt 3 * R :=
        mul_nonneg (Real.sqrt_nonneg _) hR
      have hsq := Real.sqrt_le_sqrt hstep
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hb] at hsq
    calc
      K2 * (∑ j ∈ Finset.range (2 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤
        K2 * (Real.sqrt 3 * R) := mul_le_mul_of_nonneg_left hbd hK2
      _ = K2 * Real.sqrt 3 * R := by ring
  have hN4le : N4 ≤ K4 * Real.sqrt 5 * A4 := by
    refine (hhs4 S).trans ?_
    have hcs := sq_sum_norm_le_mul_covariantJetNormSq
      (I := I) (M := M) g 4 S
    have hbd : (∑ j ∈ Finset.range (4 + 1),
        ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤ Real.sqrt 5 * A4 := by
      have hstep : (∑ j ∈ Finset.range (4 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 ≤
          (Real.sqrt 5 * A4) ^ 2 := by
        refine hcs.trans ?_
        have hsq : (Real.sqrt 5 * A4) ^ 2 = 5 * A4 ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
        rw [hsq]
        norm_num
        exact h4
      have hb : (0 : ℝ) ≤ Real.sqrt 5 * A4 :=
        mul_nonneg (Real.sqrt_nonneg _) hA4
      have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (4 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hsq := Real.sqrt_le_sqrt hstep
      rwa [Real.sqrt_sq hnn, Real.sqrt_sq hb] at hsq
    calc
      K4 * (∑ j ∈ Finset.range (4 + 1),
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤
        K4 * (Real.sqrt 5 * A4) := mul_le_mul_of_nonneg_left hbd hK4
      _ = K4 * Real.sqrt 5 * A4 := by ring
  have hprod : N3 ^ 2 ≤ (K2 * Real.sqrt 3 * R) * (K4 * Real.sqrt 5 * A4) :=
    (ccTensorToHs_norm_three_sq_le_norm_two_mul_norm_four
      (I := I) (M := M) g s S).trans
      (mul_le_mul hN2le hN4le (norm_nonneg _) (by positivity))
  calc
    covariantJetNormSq (I := I) (M := M) g 3 S ≤ C3 ^ 2 * N3 ^ 2 := hup
    _ ≤ C3 ^ 2 * ((K2 * Real.sqrt 3 * R) * (K4 * Real.sqrt 5 * A4)) :=
      mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ = C3 ^ 2 * (K2 * Real.sqrt 3) * (K4 * Real.sqrt 5) * (R * A4) := by
      ring

end DifferentialGeometry.Analysis.Sobolev
